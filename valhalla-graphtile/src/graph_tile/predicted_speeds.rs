//! # Predicted (Historical) Traffic
//!
//! Helpers for working with predicted speeds.
//! These speeds can optionally be encoded in the edge info for each graph tile.
//! The average speeds are broken up into equal-sized windows (hardcoded at 5 minutes in Valhalla)
//! That's a lot of data, so it's stored in a compressed form by applying a DCT-II transformation.
//! When routing, it's decompressed using the inverse operation (DTC-III).
//!
//! NOTE: The term "predicted speed" is preserved from Valhalla.
//! However, it's perhaps more accurate to understand it as historical average speeds,
//! which are useful for prediction as long as there isn't a special event,
//! temporary lane closure, etc.
//!
//! This code is ported from [Valhalla](https://github.com/valhalla/valhalla)'s baldr module
//! (predictedspeeds.cc and predictedspeeds.h).
//! The original code is available under the MIT license.
use base64::{Engine as _, engine::general_purpose::STANDARD};
use std::sync::LazyLock;
use thiserror::Error;
use zerocopy::{I16, LE, U32};

/// The size of each interval.
///
/// The week is broken into fixed-size buckets.
/// 5 minutes is hard-coded in Valhalla.
pub const SPEED_BUCKET_SIZE_MINUTES: u32 = 5;
const SPEED_BUCKET_SIZE_SECONDS: u32 = SPEED_BUCKET_SIZE_MINUTES * 60;
pub const BUCKETS_PER_WEEK: usize = (7 * 24 * 60) as usize / SPEED_BUCKET_SIZE_MINUTES as usize;

/// Length of the DCT table for the buckets.
pub const COEFFICIENT_COUNT: usize = 200;

/// Expected size (bytes) of decoded speed coefficients.
/// Each value (`i16`) is encoded as 2 bytes in big-endian order.
const DECODED_SPEED_SIZE: usize = 2 * COEFFICIENT_COUNT;

/// Lazily initialized cosine lookup table.
///
/// We pre-scale the table as an additional optimization from the Valhalla version.
/// This adds negligible additional ops during init,
/// and saves a bunch later during runtime without resorting to a compile-time table or similar
/// (which incurs a RAM penalty for everyone).
///
/// This optimization was born of necessity wanting to run tests under Miri.
/// While Miri is not an indicator of performance on bare metal,
/// the floating point and trig op reduction when pre-scaling the table
/// results in approximately 100x faster tests under Miri,
/// and a surprisingly measurable (~5 sec -> ~3.5 sec) test execution time on bare metal
/// (Apple Silicon M1 Max).
static COS_TABLE: LazyLock<Box<[[f32; COEFFICIENT_COUNT]]>> = LazyLock::new(|| {
    // DCT-III constants for speed decoding and normalization
    #[expect(
        clippy::cast_precision_loss,
        reason = "BUCKETS_PER_WEEK is always <= 23 bits"
    )]
    const PI_BUCKET_CONST: f32 = std::f32::consts::PI / BUCKETS_PER_WEEK as f32;

    // Uses the trig_const crate to precompute this at compile time within an acceptable range of error.
    // If sqrt is ever made stable in const contexts, we can drop this dependency.
    #[expect(
        clippy::cast_possible_truncation,
        clippy::cast_precision_loss,
        reason = "This value is guaranteed to be small, since BUCKETS_PER_WEEK is small."
    )]
    const SPEED_NORM: f32 = const { trig_const::sqrt(2.0 / BUCKETS_PER_WEEK as f64) as f32 };

    const {
        assert!(BUCKETS_PER_WEEK < 2usize.pow(24));
    }

    let mut rows: Vec<[f32; COEFFICIENT_COUNT]> = vec![[0.0; COEFFICIENT_COUNT]; BUCKETS_PER_WEEK];

    for bucket in 0..BUCKETS_PER_WEEK {
        #[expect(
            clippy::cast_precision_loss,
            reason = "BUCKETS_PER_WEEK is always <= 23 bits"
        )]
        let bucket_center = (bucket as f32) + 0.5;

        let row = &mut rows[bucket];

        // c == 0 column (DC) with extra 1/sqrt(2)
        row[0] = (PI_BUCKET_CONST * bucket_center * 0.0f32).cos()
            * SPEED_NORM
            * std::f32::consts::FRAC_1_SQRT_2;

        // c >= 1 columns
        for c in 1..COEFFICIENT_COUNT {
            #[expect(
                clippy::cast_precision_loss,
                reason = "COEFFICIENT_COUNT is always <= 23 bits"
            )]
            let v = (PI_BUCKET_CONST * bucket_center * c as f32).cos() * SPEED_NORM;
            row[c] = v;
        }
    }
    rows.into_boxed_slice()
});

/// Get the (pre-scaled) cosine row for a specific bucket (zero-indexed by week).
fn cos_row(bucket: usize) -> &'static [f32; COEFFICIENT_COUNT] {
    &COS_TABLE[bucket]
}

#[derive(Debug, Error)]
pub enum PredictedSpeedCodecError {
    #[error("Base64 decoding error: {0:?}")]
    Base64DecodeError(#[from] base64::DecodeError),
    #[error("Incorrect number of bytes decoded: found {count}; expected {DECODED_SPEED_SIZE}")]
    IncorrectByteCount { count: usize },
}

/// Compress a full week of speed buckets by truncating its DCT-II.
///
/// Speeds are expected to be specified in kilometers per hour.
#[inline]
pub fn compress_speed_buckets(speeds: &[f32; BUCKETS_PER_WEEK]) -> [i16; COEFFICIENT_COUNT] {
    let mut acc = [0f32; COEFFICIENT_COUNT];

    // DCT-II accumulation (bucket-major) using the precomputed, scaled cosines.
    for (bucket, &speed) in speeds.iter().enumerate() {
        let row = cos_row(bucket);
        for (a, &basis) in acc.iter_mut().zip(row.iter()) {
            *a += speed * basis;
        }
    }

    // Quantize (round) directly to i16
    let mut result = [0i16; COEFFICIENT_COUNT];
    #[expect(
        clippy::cast_possible_truncation,
        reason = "We already round the value, so truncation is not possible."
    )]
    for (i, coeff) in acc.iter().enumerate() {
        result[i] = coeff.round() as i16;
    }
    result
}

/// Recover a single bucket’s speed from the compressed coefficients.
///
/// `bucket_idx` must be in [0, [`BUCKETS_PER_WEEK`]).
/// Returns a speed in kilometers per hour.
#[inline]
pub fn decompress_speed_bucket(coefficients: &[i16; COEFFICIENT_COUNT], bucket_idx: usize) -> f32 {
    let row = cos_row(bucket_idx);

    // DCT-III reconstruction using the normalized cosine rows.
    // Regrettably, the manual messy indexed loop is the only way to get this code to auto-vectorize
    // at the time of this writing.
    let mut s = 0.0f32;
    for i in 0..COEFFICIENT_COUNT {
        s = row[i].mul_add(f32::from(coefficients[i]), s);
    }
    s
}

/// Pack transformed speed values into a base64 string.
/// Each i16 is serialized big-endian to match the C++.
#[inline]
pub fn encode_compressed_speeds(coefficients: &[i16; COEFFICIENT_COUNT]) -> String {
    // Exact-sized stack buffer; unfortunately also needs to be written out explicitly for now
    // to avoid a bunch of tiny extends on a vector
    let mut raw = [0u8; DECODED_SPEED_SIZE];
    for (i, &c) in coefficients.iter().enumerate() {
        raw[2 * i..2 * i + 2].copy_from_slice(&c.to_be_bytes());
    }
    STANDARD.encode(raw)
}

/// Decode a base64 string into the 200 i16 coefficients.
///
/// # Errors
///
/// Fails if the decoded byte length != 400.
pub fn decode_base64_speed_coefficients(
    encoded: &str,
) -> Result<[i16; COEFFICIENT_COUNT], PredictedSpeedCodecError> {
    let raw = STANDARD.decode(encoded.as_bytes())?;
    if raw.len() != DECODED_SPEED_SIZE {
        return Err(PredictedSpeedCodecError::IncorrectByteCount { count: raw.len() });
    }
    let mut out = [0i16; COEFFICIENT_COUNT];
    for (i, chunk) in raw.chunks_exact(2).enumerate() {
        out[i] = i16::from_be_bytes([chunk[0], chunk[1]]);
    }
    Ok(out)
}

/// Computes an average speed profile from a set of compressed coefficients.
///
/// # Performance
///
/// This function should be reasonably fast, as there is no intermediate decode step.
/// The averaging is applied directly in the DCT compressed domain.
/// The generated code is vectorized on modern CPUs (verified using Compiler Explorer).
///
/// # Accuracy
///
/// The dominant source of error in Valhalla predicted traffic is the DCT-II compression itself,
/// which lossily compresses 2016 speed buckets into 200 low-frequency coefficients and therefore
/// smooths sharp or sudden changes.
///
/// This function does not introduce any additional structural loss beyond that compression.
/// It computes the coefficient-space mean of the already-quantized profiles and performs a
/// single final quantization step.
///
/// Compared to averaging fully decoded profiles and then recompressing them, this approach
/// is at least as accurate and typically more accurate, since it avoids an extra
/// compress–decompress cycle.
///
/// The only additional error introduced here is due to integer division when computing the
/// mean coefficient values; this is bounded to less than 1 least-significant unit per coefficient.
/// In practice, this translates to sub-kph differences in reconstructed speeds.
pub fn average_compressed_speeds(speeds: &[[i16; COEFFICIENT_COUNT]]) -> [i16; COEFFICIENT_COUNT] {
    debug_assert!(
        speeds.len() < usize::from(u16::MAX),
        "Are you SURE you want to average more than 65,535 profiles? This method doesn't currently support that."
    );
    let mut result = [0i32; COEFFICIENT_COUNT];

    // Sum all speed arrays elementwise
    for speed_array in speeds {
        for i in 0..COEFFICIENT_COUNT {
            result[i] += i32::from(speed_array[i]);
        }
    }

    // Divide by count and convert back to i16
    let count = speeds.len() as i32;
    let mut output = [0i16; COEFFICIENT_COUNT];

    for i in 0..COEFFICIENT_COUNT {
        output[i] = (result[i] / count) as i16;
    }

    output
}

/// Safe accessor for predicted speed profiles stored in a tile-like blob.
///
/// * `offsets` is an array where each directed-edge index maps to an offset
///   (in *coefficients*, not bytes) into `profiles`.
/// * `profiles` is a flat array of i16 coefficients; each profile occupies
///   `COEFFICIENT_COUNT` consecutive entries.
#[derive(Debug, Clone)]
pub(crate) struct PredictedSpeeds<'a> {
    /// An array of offsets mapping every directed edge in the tile
    /// to a _starting offset_ in the `profiles` array.
    ///
    /// This array must have one entry for each directed edge in the graph tile,
    /// regardless of whether that edge has predicted traffic or not.
    /// Directed edges have a single bit indicating whether they have predicted speeds,
    /// accessible via [`super::DirectedEdge::has_predicted_speed`].
    /// Attempting to access speeds for an edge which does not have this bit set
    /// results in undefined behavior (in the sense that we make no guarantees about what happens).
    offsets: &'a [U32<LE>],
    /// The weekly speed profile data, stored as a flat blob.
    ///
    /// This must be some multiple of [`COEFFICIENT_COUNT`].
    /// In debug builds, we check this with a runtime assertion.
    /// For release builds, we assume the size is correct,
    /// and may panic if a tile is invalid.
    profiles: &'a [I16<LE>],
}

impl<'a> PredictedSpeeds<'a> {
    pub fn new(offsets: &'a [U32<LE>], profiles: &'a [I16<LE>]) -> Self {
        debug_assert!(
            profiles.len().is_multiple_of(COEFFICIENT_COUNT),
            "Unexpected profiles length: {}. Expected a multiple of {COEFFICIENT_COUNT}",
            profiles.len()
        );
        Self { offsets, profiles }
    }

    /// Get the predicted speed (kph) for a given directed-edge index at a specific time.
    ///
    /// The time `seconds_from_start_of_week` is measured from midnight Sunday local time.
    /// Returns `None` if the offset is invalid.
    ///
    /// NB: It is the caller's responsibility to ensure that the provided directed edge index
    /// actually has traffic data!
    /// The Valhalla tile format does not have any sort of sentinel value,
    /// so the resulting value will appear valid but will not be accurate for the edge!
    pub fn speed(
        &self,
        directed_edge_index: usize,
        seconds_from_start_of_week: u32,
    ) -> Option<f32> {
        let bucket = (seconds_from_start_of_week / SPEED_BUCKET_SIZE_SECONDS) as usize;
        if bucket >= BUCKETS_PER_WEEK {
            return None;
        }
        let start = self.offsets.get(directed_edge_index)?.get() as usize;

        // View the profiles as fixed-size chunks
        let (chunks, rem) = self.profiles.as_chunks::<COEFFICIENT_COUNT>();
        debug_assert!(
            rem.is_empty(),
            "profiles length must be a multiple of COEFFICIENT_COUNT. The graph tile is invalid."
        );
        debug_assert!(
            start.is_multiple_of(COEFFICIENT_COUNT),
            "Offset {start} must be a multiple of {COEFFICIENT_COUNT}. The graph tile is invalid."
        );

        let chunk_idx = start / COEFFICIENT_COUNT;
        let coeffs = chunks.get(chunk_idx)?.map(I16::get);

        Some(decompress_speed_bucket(&coeffs, bucket))
    }

    /// Returns the raw borrowed slices for the offsets and profiles (in order).
    ///
    /// This is for internal use by the builder, which provides a sane interface
    /// for creating / manipulating predicted speed data at the edge level.
    pub(crate) fn as_offsets_and_profiles(&self) -> (&'a [U32<LE>], &'a [I16<LE>]) {
        (self.offsets, self.profiles)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[cfg(not(miri))]
    use proptest::prop_assert;

    // Temporarily not run under miri, since the trig ops are REALLY slow
    #[cfg(not(miri))]
    proptest::proptest! {
        /// For arbitrary non-negative weekly speeds, the decoded speeds should not go negative,
        /// allowing a tiny epsilon for floating point jitter.
        #[test]
        fn prop_non_negative_after_decode(
            // Generate 2016 bucket values in a reasonable kph range.
            speeds in proptest::collection::vec(0.0f32..250.0f32, BUCKETS_PER_WEEK)
        ) {
            // Convert Vec -> array
            let speeds: [f32; BUCKETS_PER_WEEK] = speeds.try_into().expect("exact length");

            // Compress then decode all buckets
            let coeffs = compress_speed_buckets(&speeds);
            let mut recon = [0f32; BUCKETS_PER_WEEK];
            for i in 0..BUCKETS_PER_WEEK {
                recon[i] = decompress_speed_bucket(&coeffs, i);
            }

            for (i, &s) in recon.iter().enumerate() {
                // These can be preeeety negative...
                prop_assert!(s >= -5.0, "negative speed at bucket {i}: {s}");
            }
        }

        #[test]
        fn prop_averaging_in_compressed_domain_white_noise(
            speeds1 in proptest::collection::vec(1.0f32..250.0f32, BUCKETS_PER_WEEK),
            speeds2 in proptest::collection::vec(1.0f32..250.0f32, BUCKETS_PER_WEEK),
            speeds3 in proptest::collection::vec(1.0f32..250.0f32, BUCKETS_PER_WEEK)
        ) {
            // Convert Vec -> array
            let speeds1: [f32; BUCKETS_PER_WEEK] = speeds1.try_into().expect("exact length");
            let speeds2: [f32; BUCKETS_PER_WEEK] = speeds2.try_into().expect("exact length");
            let speeds3: [f32; BUCKETS_PER_WEEK] = speeds3.try_into().expect("exact length");

            // Compress all three profiles
            let coeffs1 = compress_speed_buckets(&speeds1);
            let coeffs2 = compress_speed_buckets(&speeds2);
            let coeffs3 = compress_speed_buckets(&speeds3);

            // Method 1: Decompress first; then average the decompressed speeds
            // NB: Since our test contains essentially random speeds, we can't accurately compare
            // with the true average, since the compresion is so lossy.
            // This approach tests the actual property which is "if we decompressed the speeds
            // and then averaged those values, is that the same as averaging the coefficients directly."
            let mut b1 = [0.0f32; BUCKETS_PER_WEEK];
            let mut b2 = [0.0f32; BUCKETS_PER_WEEK];
            let mut b3 = [0.0f32; BUCKETS_PER_WEEK];
            for i in 0..BUCKETS_PER_WEEK {
                b1[i] = decompress_speed_bucket(&coeffs1, i);
                b2[i] = decompress_speed_bucket(&coeffs2, i);
                b3[i] = decompress_speed_bucket(&coeffs3, i);
            }

            let mut avg_buckets_direct = [0.0f32; BUCKETS_PER_WEEK];
            for i in 0..BUCKETS_PER_WEEK {
                avg_buckets_direct[i] = (b1[i] + b2[i] + b3[i]) / 3.0;
            }

            // Method 2: Average directly in the compressed domain using the average_compressed_speeds function
            let avg_coeffs = average_compressed_speeds(&[coeffs1, coeffs2, coeffs3]);

            // Decompress the averaged coefficients
            let mut avg_buckets_compressed = [0f32; BUCKETS_PER_WEEK];
            for i in 0..BUCKETS_PER_WEEK {
                avg_buckets_compressed[i] = decompress_speed_bucket(&avg_coeffs, i);
            }

            for i in 0..BUCKETS_PER_WEEK {
                let diff = (avg_buckets_direct[i] - avg_buckets_compressed[i]).abs();
                prop_assert!(
                    diff <= 1.0,
                    "Bucket {i}: direct average = {}, compressed average = {}, diff = {}",
                    avg_buckets_direct[i],
                    avg_buckets_compressed[i],
                    diff
                );
            }
        }

        /// For a single speed profile, averaging should be a no-op (round-trip unchanged).
        #[test]
        fn prop_average_single_profile_unchanged(
            speeds in proptest::collection::vec(0.0f32..250.0f32, BUCKETS_PER_WEEK)
        ) {
            // Convert Vec -> array
            let speeds: [f32; BUCKETS_PER_WEEK] = speeds.try_into().expect("exact length");

            // Compress the profile
            let coeffs = compress_speed_buckets(&speeds);

            // Average a single profile
            let avg_coeffs = average_compressed_speeds(&[coeffs]);

            // The averaged coefficients should be identical to the original
            prop_assert!(
                coeffs == avg_coeffs,
                "Averaging a single speed profile should return the same coefficients"
            );
        }

        /// For smooth, low-frequency weekly profiles, the round-trip error should be small.
        /// This mirrors the C++ deterministic test thresholds.
        #[test]
        fn prop_smooth_roundtrip_accuracy(
            base in 20.0f32..80.0f32,      // baseline kph
            amp1 in  0.0f32..25.0f32,      // daily-ish variation
            amp2 in  0.0f32..10.0f32,      // smaller component
            phase1 in 0.0f32..(std::f32::consts::TAU),
            phase2 in 0.0f32..(std::f32::consts::TAU),
            noise_scale in 0.0f32..1.0f32  // tiny jitter
        ) {
            /// Helper: mean absolute error and max absolute error.
            fn mae_and_max(a: &[f32], b: &[f32]) -> (f32, f32) {
                assert_eq!(a.len(), b.len());
                let mut sum = 0.0f32;
                let mut maxd = 0.0f32;
                for (x, y) in a.iter().zip(b.iter()) {
                    let d = (x - y).abs();
                    sum += d;
                    if d > maxd { maxd = d; }
                }
                (sum / (a.len() as f32), maxd)
            }

            // Build a smooth signal: combination of two low-frequency sinusoids + tiny noise,
            // clamped to non-negative speeds.
            let mut speeds = [0f32; BUCKETS_PER_WEEK];
            for i in 0..BUCKETS_PER_WEEK {
                // "Time" in arbitrary units; 2016 buckets per week, keep frequencies low.
                let t = i as f32;

                // Periods chosen to be long relative to the week to bias toward low-frequency content.
                let s1 = (t * (2.0*std::f32::consts::PI / 288.0) + phase1).sin(); // ~1 day (288 * 5min)
                let s2 = (t * (2.0*std::f32::consts::PI / 672.0) + phase2).sin(); // ~2.33 days

                // Deterministic tiny "noise": bounded in [-1,1] then scaled
                let n = ((t * 0.12345).sin() * (t * 0.54321).cos()) * noise_scale;

                let v = base + amp1 * s1 + amp2 * s2 + n;
                speeds[i] = v.max(0.0);
            }

            // Compress and reconstruct
            let coeffs = compress_speed_buckets(&speeds);
            let mut recon = [0f32; BUCKETS_PER_WEEK];
            for i in 0..BUCKETS_PER_WEEK {
                recon[i] = decompress_speed_bucket(&coeffs, i);
            }

            let (mae, maxe) = mae_and_max(&speeds, &recon);

            // Match the C++ expectations: <= 1.0 average, <= 2.0 max.
            // (If you want to tighten globally, start here.)
            prop_assert!(mae <= 1.0, "MAE too large: {mae}");
            prop_assert!(maxe <= 2.0, "Max error too large: {maxe}");
        }
    }

    const SPEEDS: [u16; BUCKETS_PER_WEEK] = [
        36, 36, 36, 36, 36, 36, 36, 36, 36, 37, 37, 37, 38, 38, 39, 40, 40, 41, 41, 42, 42, 42, 42,
        42, 42, 42, 42, 41, 41, 41, 41, 41, 41, 41, 41, 42, 42, 43, 43, 44, 44, 45, 45, 45, 46, 46,
        45, 45, 45, 44, 43, 43, 42, 41, 40, 40, 39, 39, 38, 38, 37, 37, 37, 36, 36, 35, 34, 34, 33,
        32, 30, 29, 27, 26, 24, 23, 21, 20, 19, 18, 17, 17, 16, 16, 16, 16, 16, 16, 17, 17, 16, 16,
        16, 15, 15, 14, 13, 12, 12, 11, 11, 10, 10, 11, 12, 13, 14, 16, 17, 19, 21, 24, 25, 27, 29,
        30, 31, 32, 33, 33, 33, 33, 33, 32, 32, 32, 33, 33, 34, 35, 36, 38, 39, 41, 42, 44, 45, 46,
        47, 47, 48, 48, 47, 47, 46, 45, 45, 44, 43, 43, 43, 43, 43, 44, 44, 45, 46, 46, 47, 48, 48,
        49, 49, 48, 48, 48, 47, 46, 46, 45, 44, 44, 43, 43, 43, 43, 43, 43, 43, 42, 42, 42, 41, 41,
        40, 39, 38, 37, 35, 34, 33, 31, 30, 29, 28, 27, 26, 26, 25, 25, 25, 25, 25, 25, 25, 25, 25,
        25, 25, 25, 25, 25, 24, 24, 24, 23, 23, 22, 22, 21, 20, 19, 18, 18, 17, 17, 16, 16, 16, 16,
        17, 17, 18, 19, 20, 22, 23, 24, 25, 27, 27, 28, 29, 29, 29, 29, 29, 29, 29, 30, 30, 30, 31,
        32, 33, 34, 36, 37, 39, 41, 42, 43, 45, 45, 46, 47, 47, 47, 47, 47, 47, 47, 47, 47, 47, 47,
        48, 49, 49, 50, 51, 52, 52, 53, 53, 53, 53, 52, 52, 51, 50, 49, 48, 46, 45, 44, 44, 43, 42,
        41, 41, 40, 40, 39, 38, 38, 37, 36, 35, 34, 34, 33, 33, 32, 32, 32, 32, 33, 33, 34, 34, 35,
        35, 35, 35, 35, 34, 33, 32, 31, 29, 27, 26, 24, 23, 21, 20, 19, 19, 18, 18, 18, 19, 19, 20,
        20, 20, 21, 21, 21, 21, 21, 21, 21, 20, 20, 21, 21, 21, 22, 22, 23, 24, 25, 26, 27, 28, 29,
        29, 29, 30, 30, 29, 29, 29, 29, 29, 30, 30, 31, 32, 33, 35, 37, 39, 41, 43, 44, 46, 47, 48,
        49, 50, 50, 50, 49, 49, 48, 48, 47, 46, 46, 46, 46, 46, 46, 46, 47, 48, 48, 49, 49, 49, 49,
        49, 49, 49, 48, 47, 46, 45, 44, 43, 42, 42, 41, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40,
        39, 39, 38, 37, 36, 35, 34, 32, 31, 29, 27, 26, 24, 23, 21, 20, 19, 19, 18, 18, 18, 18, 18,
        19, 19, 20, 20, 21, 22, 22, 23, 23, 24, 24, 24, 23, 23, 23, 22, 22, 21, 20, 20, 19, 19, 18,
        18, 18, 18, 18, 18, 18, 18, 18, 18, 19, 19, 20, 21, 22, 23, 24, 25, 27, 28, 30, 32, 33, 35,
        37, 39, 40, 41, 42, 43, 44, 44, 44, 44, 43, 42, 42, 41, 40, 39, 39, 38, 38, 38, 38, 39, 40,
        41, 42, 43, 44, 45, 47, 48, 49, 50, 50, 51, 51, 51, 51, 50, 50, 49, 48, 47, 46, 45, 44, 44,
        43, 42, 41, 41, 40, 40, 39, 38, 38, 37, 36, 35, 34, 33, 32, 31, 30, 29, 28, 27, 27, 26, 26,
        26, 26, 26, 27, 27, 27, 28, 28, 28, 28, 28, 28, 27, 26, 24, 22, 20, 18, 16, 14, 12, 10, 8,
        7, 6, 5, 5, 5, 5, 6, 7, 8, 9, 10, 12, 13, 13, 14, 15, 15, 15, 15, 15, 15, 15, 16, 16, 17,
        18, 19, 21, 23, 25, 27, 29, 32, 34, 36, 38, 40, 41, 42, 43, 44, 44, 45, 45, 44, 44, 44, 43,
        43, 43, 42, 42, 41, 41, 41, 40, 40, 39, 38, 38, 37, 37, 36, 36, 36, 36, 36, 37, 38, 38, 39,
        41, 42, 43, 44, 44, 45, 45, 45, 44, 44, 42, 41, 39, 38, 36, 34, 32, 31, 29, 28, 28, 27, 27,
        27, 27, 28, 28, 29, 29, 29, 30, 29, 29, 29, 28, 27, 26, 25, 23, 22, 21, 20, 20, 19, 19, 18,
        18, 19, 19, 19, 20, 20, 20, 21, 21, 21, 22, 22, 22, 22, 22, 22, 23, 23, 23, 24, 24, 24, 25,
        25, 25, 25, 25, 25, 25, 25, 25, 25, 24, 24, 24, 25, 25, 26, 27, 28, 29, 30, 32, 33, 35, 36,
        38, 39, 41, 42, 43, 44, 45, 46, 46, 47, 48, 49, 49, 50, 51, 52, 53, 53, 54, 54, 54, 54, 54,
        54, 53, 52, 50, 49, 47, 46, 44, 43, 42, 40, 40, 39, 39, 39, 39, 40, 40, 41, 42, 43, 43, 44,
        44, 44, 44, 44, 43, 42, 41, 40, 39, 38, 36, 35, 34, 33, 32, 32, 31, 30, 29, 29, 28, 28, 27,
        26, 25, 25, 24, 23, 22, 21, 21, 20, 19, 19, 19, 18, 18, 18, 18, 18, 17, 17, 17, 16, 16, 15,
        15, 14, 14, 14, 13, 13, 13, 13, 14, 14, 15, 16, 17, 18, 19, 21, 22, 23, 24, 26, 27, 27, 28,
        29, 30, 30, 31, 32, 32, 33, 34, 35, 35, 36, 38, 39, 40, 41, 42, 43, 44, 45, 45, 46, 46, 46,
        46, 46, 46, 46, 45, 45, 44, 44, 43, 43, 43, 43, 43, 43, 43, 43, 44, 44, 44, 45, 45, 45, 46,
        46, 46, 45, 45, 45, 44, 44, 43, 42, 41, 41, 40, 39, 37, 36, 35, 34, 32, 31, 30, 28, 27, 25,
        24, 23, 21, 20, 19, 19, 18, 18, 18, 18, 18, 19, 19, 20, 21, 21, 22, 22, 23, 23, 23, 22, 22,
        21, 20, 19, 18, 18, 17, 16, 16, 16, 16, 17, 17, 18, 19, 20, 22, 23, 24, 25, 26, 26, 27, 27,
        27, 27, 27, 27, 27, 27, 27, 28, 28, 29, 30, 31, 33, 34, 36, 37, 39, 40, 41, 41, 42, 42, 42,
        42, 41, 40, 40, 39, 38, 38, 37, 37, 37, 38, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 48,
        49, 49, 49, 49, 49, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 49, 49, 48, 47, 46, 45, 44, 42,
        41, 40, 38, 37, 36, 35, 34, 33, 33, 33, 32, 32, 32, 32, 32, 31, 31, 30, 30, 29, 28, 27, 26,
        25, 23, 22, 21, 20, 18, 18, 17, 16, 16, 16, 16, 17, 17, 18, 19, 19, 20, 21, 22, 23, 24, 24,
        25, 25, 25, 26, 26, 26, 26, 26, 27, 27, 27, 28, 28, 29, 30, 30, 31, 32, 32, 33, 33, 34, 34,
        34, 34, 34, 34, 34, 34, 33, 34, 34, 34, 35, 36, 37, 38, 39, 41, 42, 43, 45, 46, 47, 48, 49,
        50, 50, 51, 51, 51, 51, 51, 51, 51, 51, 51, 51, 51, 52, 52, 51, 51, 51, 50, 50, 49, 47, 46,
        45, 43, 42, 40, 39, 38, 37, 36, 36, 36, 36, 36, 36, 36, 37, 37, 37, 37, 37, 36, 35, 34, 33,
        32, 31, 29, 28, 27, 27, 26, 26, 26, 26, 26, 27, 27, 27, 28, 28, 28, 27, 27, 26, 25, 24, 23,
        22, 22, 21, 20, 20, 20, 21, 21, 22, 23, 24, 25, 26, 26, 27, 28, 28, 28, 28, 28, 28, 27, 27,
        26, 26, 26, 26, 26, 27, 27, 28, 29, 30, 30, 31, 32, 33, 34, 35, 36, 37, 37, 38, 39, 40, 41,
        42, 43, 44, 45, 46, 46, 47, 47, 47, 46, 46, 45, 44, 43, 42, 40, 39, 39, 38, 38, 38, 38, 39,
        41, 42, 44, 45, 47, 49, 50, 51, 52, 52, 52, 52, 51, 50, 48, 46, 45, 43, 42, 40, 39, 38, 38,
        37, 37, 37, 37, 38, 38, 38, 38, 38, 38, 37, 37, 36, 36, 35, 34, 34, 33, 32, 32, 31, 31, 30,
        30, 29, 28, 27, 26, 24, 22, 20, 18, 16, 14, 12, 10, 9, 8, 7, 7, 7, 7, 8, 9, 10, 12, 13, 15,
        16, 17, 18, 19, 20, 20, 21, 21, 21, 21, 21, 21, 21, 22, 23, 24, 25, 26, 27, 29, 30, 32, 33,
        35, 36, 38, 39, 40, 42, 43, 44, 45, 46, 46, 47, 48, 49, 49, 49, 49, 49, 49, 48, 48, 47, 45,
        44, 42, 41, 40, 38, 37, 36, 36, 36, 36, 36, 37, 39, 40, 42, 43, 45, 47, 48, 49, 50, 50, 50,
        50, 49, 47, 46, 43, 41, 39, 36, 34, 32, 29, 28, 26, 25, 24, 24, 23, 23, 24, 24, 25, 25, 26,
        26, 26, 26, 26, 26, 25, 24, 23, 22, 21, 19, 18, 17, 16, 15, 14, 13, 13, 13, 13, 14, 14, 15,
        16, 17, 17, 18, 19, 19, 20, 20, 20, 20, 20, 20, 20, 20, 20, 21, 21, 21, 22, 23, 24, 25, 26,
        27, 28, 29, 30, 31, 31, 32, 32, 32, 33, 33, 33, 33, 33, 33, 34, 34, 35, 36, 38, 39, 40, 42,
        43, 45, 46, 47, 48, 48, 48, 48, 48, 47, 47, 46, 45, 44, 43, 42, 42, 41, 41, 41, 41, 42, 42,
        42, 43, 43, 44, 44, 44, 43, 43, 43, 42, 41, 40, 40, 39, 38, 38, 38, 38, 38, 38, 38, 39, 39,
        39, 39, 39, 39, 38, 37, 35, 33, 31, 29, 27, 25, 23, 21, 19, 18, 18, 17, 17, 18, 19, 20, 21,
        22, 23, 23, 24, 24, 24, 23, 22, 21, 19, 17, 16, 14, 13, 12, 11, 11, 11, 11, 12, 14, 15, 17,
        19, 21, 23, 24, 25, 26, 27, 28, 28, 28, 28, 28, 28, 29, 29, 30, 31, 33, 35, 36, 38, 40, 42,
        43, 44, 45, 46, 46, 45, 45, 44, 42, 41, 40, 39, 39, 38, 39, 39, 40, 42, 44, 46, 48, 50, 52,
        53, 55, 56, 56, 56, 56, 55, 54, 52, 51, 49, 47, 46, 45, 44, 44, 44, 44, 44, 45, 45, 46, 47,
        47, 47, 47, 47, 46, 46, 45, 43, 42, 41, 40, 39, 37, 37, 36, 35, 34, 34, 33, 33, 32, 31, 30,
        29, 27, 26, 25, 23, 22, 20, 19, 19, 18, 18, 18, 18, 19, 19, 20, 21, 22, 22, 23, 23, 23, 22,
        21, 21, 20, 19, 18, 17, 16, 16, 16, 17, 18, 19, 21, 23, 26, 28, 30, 33, 35, 37, 38, 39, 40,
        40, 40, 40, 39, 39, 38, 37, 37, 36, 36, 36, 36, 37, 37, 38, 39, 40, 41, 42, 43, 44, 44, 45,
        45, 45, 45, 45, 45, 44, 44, 44, 43, 43, 43, 42, 42, 42, 42, 43, 43, 43, 44, 44, 45, 46, 47,
        48, 49, 50, 51, 52, 53, 53, 53, 53, 53, 52, 51, 50, 48, 46, 43, 40, 37, 34, 32, 29, 26, 24,
        22, 20, 19, 19, 19, 19, 19, 20, 21, 22, 24, 25, 26, 27, 28, 29, 29, 29, 29, 28, 28, 27, 26,
        25, 24, 22, 21, 20, 18, 17, 16, 14, 13, 12, 11, 10, 10, 9, 9, 9, 10, 10, 11, 13, 14, 16,
        17, 19, 21, 23, 24, 26, 27, 28, 29, 29, 30, 30, 30, 30, 31, 31, 31, 32, 32, 33, 34, 35, 36,
        37, 39, 40, 41, 41, 42, 42, 43, 43, 43, 43, 42, 42, 42, 42, 42, 42, 43, 43, 44, 45, 46, 47,
        47, 48, 49, 49, 49, 49, 49, 49, 48, 47, 47, 46, 45, 44, 44, 44, 43, 43, 43, 43, 43, 43, 43,
        43, 43, 42, 41, 40, 39, 37, 36, 34, 33, 31, 30, 29, 28, 27, 27, 27, 27, 27, 27, 27, 27, 26,
        26, 25, 24, 23, 21, 20, 18, 17, 15, 14, 14, 13, 13, 14, 15, 16, 18, 20, 21, 23, 25, 27, 28,
        29, 30, 30, 29, 29, 28, 27, 25, 24, 23, 22, 22, 21, 21, 22, 23, 24, 25, 26, 27, 29, 30, 31,
        31, 32, 32, 32, 32, 31, 31, 30, 30, 30, 29,
    ];

    #[test]
    fn averaging_realistic_speed_profiles() {
        // Use the existing realistic speed profile as a base
        let base_speeds: [f32; BUCKETS_PER_WEEK] = SPEEDS.map(|s| s as f32);

        // Create two additional profiles with small realistic variations
        // Profile 1: slightly faster (5% increase)
        let speeds1: [f32; BUCKETS_PER_WEEK] = base_speeds.map(|s| s * 1.05);

        // Profile 2: slightly slower (5% decrease)
        let speeds2: [f32; BUCKETS_PER_WEEK] = base_speeds.map(|s| s * 0.95);

        // The true average should be the base profile
        let true_average = base_speeds;

        // Compress all three profiles
        let coeffs_base = compress_speed_buckets(&base_speeds);
        let coeffs1 = compress_speed_buckets(&speeds1);
        let coeffs2 = compress_speed_buckets(&speeds2);

        // Average in the compressed domain
        let avg_coeffs = average_compressed_speeds(&[coeffs_base, coeffs1, coeffs2]);

        // Decompress the averaged coefficients
        let mut avg_speeds = [0f32; BUCKETS_PER_WEEK];
        for i in 0..BUCKETS_PER_WEEK {
            avg_speeds[i] = decompress_speed_bucket(&avg_coeffs, i);
        }

        // Compare with true average
        let mut max_error = 0.0f32;

        for i in 0..BUCKETS_PER_WEEK {
            let error = (avg_speeds[i] - true_average[i]).abs();
            max_error = max_error.max(error);
        }

        // The error should be quite small for realistic profiles
        // Even though we're averaging in the compressed domain, the smooth nature
        // of the profiles means the DCT compression doesn't introduce much error
        assert!(
            max_error <= 1.0,
            "Max error is larger than expected: {max_error} kph"
        );
    }

    // TODO: Make these two prop tests

    #[test]
    fn round_trip_constant_speed() {
        // 50 kph across the week
        let speeds = [50.0f32; BUCKETS_PER_WEEK];
        let coeffs = compress_speed_buckets(&speeds);
        // DC should dominate; reconstruction should be ~50 everywhere.
        for b in 0..BUCKETS_PER_WEEK {
            let s = decompress_speed_bucket(&coeffs, b);
            assert!((s - 50.0).abs() < 0.05);
        }
    }

    #[test]
    fn base64_round_trip() {
        // simple pattern
        let mut coeffs = [0i16; COEFFICIENT_COUNT];
        for i in 0..COEFFICIENT_COUNT {
            coeffs[i] = (i as i16) + 1000;
        }
        let enc = encode_compressed_speeds(&coeffs);
        let dec = decode_base64_speed_coefficients(&enc).unwrap();
        assert_eq!(coeffs, dec);
    }

    #[test]
    fn test_base64_encode_fixture() {
        // A random fixture of a looping series.
        // This has been verified against the original C++ implementation as well
        // as another random check.
        let mut speeds = [0f32; BUCKETS_PER_WEEK];
        for i in 0..BUCKETS_PER_WEEK {
            speeds[i] = (i as f32) % 100.0;
        }
        let coeffs = compress_speed_buckets(&speeds);
        let enc = encode_compressed_speeds(&coeffs);
        assert_eq!(
            enc,
            "CKD/4f/r/+H/6//g/+v/4P/q/9//6v/f/+r/3v/q/93/6f/b/+n/2v/o/9f/5//V/+b/0f/l/8z/4//G/+D/vf/d/67/1/+V/8z/Xf+u/nz+GwLJAEcAqwAWAFwABwA8AAAAK//8ACD/+AAZ//YAE//0AA//8gAM//AACf/uAAb/7AAE/+kAAv/m////4v/9/93/+f/U//T/xf/q/5//y/6PAQMAngApADkAFwAfABAAEwAMAAwACQAHAAcAAwAGAAAABf/9AAT/+wAD//kAA//2AAL/9AAC//EAAf/tAAH/6AAA/+EAAP/U////tv///x8AFADL//8AQ///ACf//gAa//4AE//+AA7//QAL//0ACP/9AAb//AAE//wAAv/8AAD/+//+//v//P/6//r/+v/2//n/8v/4/+v/9f/b/+//nP+TALoADAAyAAMAHgAAABX//gAQ//0ADf/9AAv//AAJ//sAB//7AAb/+gAF//kABP/4AAP/9wAC//YAAf/1AAD/8//+//D//P/q//f/2w=="
        );
    }

    /// End-to-end test decoding speeds from a base64 string.
    #[test]
    fn test_decoding() {
        let encoded_speed = "BcUACQAEACEADP/7/9sAGf/fAAwAGwARAAX/+AAAAB0AFAAS//AAF//+ACwACQAqAAAAKP/6AEMABABsAAsBBAAq/rcAAP+bAAz/zv/s/9MABf/Y//X/8//9/+wACf/P//EADv/8//L//P/y//H////7AAwAFf/5//oADgAZAAQAFf/3/+8AB//yAB8ABv/0AAUAEf/8//QAFAAG//b////j//v//QAT//7/+f/kABMABwABAAv/6//8//cAEwAAABT/8v/6//wAAAAQ//cACwAFAAT/1//sAAEADAABAAYAE//9AAn/7gAH/+AAFQAB//4AC//o/+gAE//+AAAAFf/l//kABP/+//kACAAG//cAHv/qAB0AAv/4/+v/+wALAAMABP/3AAT/8wAIAAr/9wAK//j/+wAEAAD/+P/8//v/8f/2//L//AALAAcABgAG//gAAv/5AAoAHv//AAcAFf/zABD/7AAUAAv/7v/8AAgACAAN//0ADP/iABD/9f/3//7/+P/3AAQADP//AAMABw==";

        let coeffs = decode_base64_speed_coefficients(encoded_speed)
            .expect("Failed to decode coefficients")
            .map(|c| c.into());

        // Build a single-edge profile view
        let offsets: [U32<LE>; 1] = [0.into()];
        let profiles: Vec<I16<LE>> = coeffs.into();

        let ps = PredictedSpeeds::new(&offsets, &profiles);

        for (i, &exp) in SPEEDS.iter().enumerate() {
            let secs = (i as u32) * SPEED_BUCKET_SIZE_SECONDS;
            let s = ps.speed(0, secs).expect("speed");
            // The C++ codebase had a rather strange way of comparing these.
            // Presumably it was to account for theoretical differences that could arise
            // due to floating point imprecision?
            assert!(
                (s - exp as f32).abs() < 1.0,
                "Speed at bucket {i} ({s}) doesn't match expectation ({exp})"
            );
        }
    }

    fn normalized_l1_norm(vec: &[f32]) -> f32 {
        assert!(!vec.is_empty());
        let sum: f32 = vec.iter().map(|v| v.abs()).sum();
        sum / (vec.len() as f32)
    }

    /// Tests from the C++ library.
    mod cpp_tests {
        use super::*;

        /// Limited base64 decoding tests.
        ///
        /// Ported as-is from the C++ reference implementation.
        #[test]
        fn test_free_flow_speed() {
            // Mirrors the C++ helper that inspects a tiny base64 header containing
            // t (5 bits), free_flow_speed, constrained_flow_speed.
            // If the values don't match the expected fixtures, panics with an assertion error.
            fn try_free_flow_speed(
                encoded: &str,
                expected_free_flow: u32,
                expected_constrained_flow: u32,
            ) {
                let decoded = STANDARD.decode(encoded.as_bytes()).expect("base64 decode");
                let raw = &decoded[..];
                let mut index = 0usize;

                let t = (raw[index] as u32) & 0x1f;
                index += 1;
                assert_eq!(t, 0);

                let free_flow_speed = (raw[index] as u32) & 0xff;
                index += 1;
                assert_eq!(free_flow_speed, expected_free_flow);

                let constrained_flow_speed = (raw[index] as u32) & 0xff;
                assert_eq!(constrained_flow_speed, expected_constrained_flow);
            }

            try_free_flow_speed("AAie", 8, 158);
            try_free_flow_speed("AACe", 0, 158);
        }

        /// Tests decoding of a base64 string to bucketized speeds.
        ///
        /// This is preserved as-is from the C++ test code for completeness.
        /// However, the C++ code noted that the test fixture was broken,
        /// and so the test case essentially copies a bunch of the existing decoding code
        /// instead of exercising the existing helpers.
        ///
        /// An improved version outside the legacy module addresses these issues.
        #[test]
        fn test_decoding() {
            // Bit of a hacky, and rather lossy comparison function.
            // Preserved as-is.
            fn within_threshold(v1: u32, v2: u32) -> bool {
                const SPEED_ERROR_THRESHOLD: u32 = 1;
                let abs_delta = if v2 > v1 { v2 - v1 } else { v1 - v2 };
                abs_delta < SPEED_ERROR_THRESHOLD
            }

            // The fixture from the C++ tests, which is one byte too long.
            // It has an extra byte at the beginning for some reason.
            let encoded_speed_string = "AQXFAAkABAAhAAz/+//bABn/3wAMABsAEQAF//gAAAAdABQAEv/wABf//gAsAAkAKgAAACj/+gBDAAQAbAALAQQAKv63AAD/mwAM/87/7P/TAAX/2P/1//P//f/sAAn/z//xAA7//P/y//z/8v/x////+wAMABX/+f/6AA4AGQAEABX/9//vAAf/8gAfAAb/9AAFABH//P/0ABQABv/2////4//7//0AE//+//n/5AATAAcAAQAL/+v//P/3ABMAAAAU//L/+v/8AAAAEP/3AAsABQAE/9f/7AABAAwAAQAGABP//QAJ/+4AB//gABUAAf/+AAv/6P/oABP//gAAABX/5f/5AAT//v/5AAgABv/3AB7/6gAdAAL/+P/r//sACwADAAT/9wAE//MACAAK//cACv/4//sABAAA//j//P/7//H/9v/y//wACwAHAAYABv/4AAL/+QAKAB7//wAHABX/8wAQ/+wAFAAL/+7//AAIAAgADf/9AAz/4gAQ//X/9//+//j/9wAEAAz//wADAAc=";

            let decoded = STANDARD
                .decode(encoded_speed_string.as_bytes())
                .expect("base64 decode");
            // Broken fixture expectation (+1)
            assert_eq!(decoded.len(), DECODED_SPEED_SIZE + 1);

            // raw signed bytes
            let raw = &decoded[..];

            // first value (at index 0) is 1 in the broken fixture
            assert_eq!(raw[0] as i8, 1, "First value should be 1");

            // Create coefficients by reading big-endian i16 *starting at offset 1*
            let mut coeffs = [0.into(); COEFFICIENT_COUNT];
            let mut idx = 1usize;
            for i in 0..COEFFICIENT_COUNT {
                let be = i16::from_be_bytes([raw[idx], raw[idx + 1]]);
                coeffs[i] = be.into();
                idx += 2;
            }

            // Build a single-edge profile view
            let offsets: [U32<LE>; 1] = [0.into()];
            let profiles: Vec<I16<LE>> = coeffs.into();

            let ps = PredictedSpeeds::new(&offsets, &profiles);

            for (i, &exp) in SPEEDS.iter().enumerate() {
                let secs = (i as u32) * SPEED_BUCKET_SIZE_SECONDS;
                let s = ps.speed(0, secs).expect("speed");
                let s_rounded = (s + 0.5).floor() as u32;
                assert!(
                    within_threshold(s_rounded, exp as u32),
                    "Speed outside of range at bucket {i}. Expected {exp}; found {s_rounded}"
                );
            }
        }

        /// Asserts that no negative speeds are deserialized.
        ///
        /// The original code did not state whether this was a regression test
        /// against some known input or if it was just a simple sanity check,
        /// so it is included as-is.
        /// However, the spirit of this test is better represented by the property test
        /// in the enclosing module.
        #[test]
        fn test_negative_speeds_original() {
            // Same “broken fixture” pattern (decoded size == DECODED_SPEED_SIZE + 1).
            let encoded_speed_string = "AQRu//UAEAAC/+4AA//6//gAAwAFAA//9wAHAAH/4AAd/+wACwAH//0AGQAYAA7//wANAAL/9//mAAUACgATAAb/8v/2//8AC//1ABMAAAAGABX/9//0//0AAAAQAAIAAv/6////9gAJAAcACf/zAAQAAwAC//oACf/2//sADQAVABD/+QADAAcACf/2//gABwAHAAAABv/9AAf/+QAM//kAEAAE//r//wAMAAD/9AAN//D/7QAK//EAE//7AAkAAQAF//f/+AAB//z/6f/y//MAAP/6ABL//AATABX//wAFAAMAGv/2AAf//wAI//sACv/5AAb/8gAOAAYADv/5AAMACP////T/7gAH//P/+f/9//n/9f/0//0AAwAP//3/8gAA//8ACv////gAAgAHAAP//QALAAcAFAAA//8ABP/vAAIAEAAM/+3/9QAC//j//v/tABj/+wAA//sAC//6//0ABwAAAAoABgAMAAb/+P/3AAX/9//7//0ADP/sAAwAB//v/+3//wAMABAACgAF//o=";

            let decoded = STANDARD
                .decode(encoded_speed_string.as_bytes())
                .expect("base64 decode");
            assert_eq!(decoded.len(), DECODED_SPEED_SIZE + 1);

            let raw = &decoded[..];
            assert_eq!(raw[0] as i8, 1, "First value should be 1");

            // Build coefficients from offset 1 (big-endian)
            let mut coeffs = [0.into(); COEFFICIENT_COUNT];
            let mut idx = 1usize;
            for i in 0..COEFFICIENT_COUNT {
                let be = i16::from_be_bytes([raw[idx], raw[idx + 1]]);
                coeffs[i] = be.into();
                idx += 2;
            }

            let offsets: [U32<LE>; 1] = [0.into()];
            let profiles: Vec<I16<LE>> = coeffs.into();
            let ps = PredictedSpeeds::new(&offsets, &profiles);

            for i in 0..BUCKETS_PER_WEEK {
                let secs = (i as u32) * SPEED_BUCKET_SIZE_SECONDS;
                let s = ps.speed(0, secs).expect("speed");
                assert!(s >= 0.0, "Negative speed at bucket {i}");
            }
        }

        /// Same as the above test, but uses a fixture of the correct length.
        ///
        /// Provided for completeness.
        #[test]
        fn negative_speeds_correct_fixture() {
            let encoded_speed = "BG7/9QAQAAL/7gAD//r/+AADAAUAD//3AAcAAf/gAB3/7AALAAf//QAZABgADv//AA0AAv/3/+YABQAKABMABv/y//b//wAL//UAEwAAAAYAFf/3//T//QAAABAAAgAC//r////2AAkABwAJ//MABAADAAL/+gAJ//b/+wANABUAEP/5AAMABwAJ//b/+AAHAAcAAAAG//0AB//5AAz/+QAQAAT/+v//AAwAAP/0AA3/8P/tAAr/8QAT//sACQABAAX/9//4AAH//P/p//L/8wAA//oAEv/8ABMAFf//AAUAAwAa//YAB///AAj/+wAK//kABv/yAA4ABgAO//kAAwAI////9P/uAAf/8//5//3/+f/1//T//QADAA///f/yAAD//wAK////+AACAAcAA//9AAsABwAUAAD//wAE/+8AAgAQAAz/7f/1AAL/+P/+/+0AGP/7AAD/+wAL//r//QAHAAAACgAGAAwABv/4//cABf/3//v//QAM/+wADAAH/+//7f//AAwAEAAKAAX/+g==";

            let coeffs = decode_base64_speed_coefficients(encoded_speed)
                .expect("Failed to decode coefficients")
                .map(|c| c.into());

            let offsets: [U32<LE>; 1] = [0.into()];
            let profiles: Vec<I16<LE>> = coeffs.into();
            let ps = PredictedSpeeds::new(&offsets, &profiles);

            for i in 0..BUCKETS_PER_WEEK {
                let secs = (i as u32) * SPEED_BUCKET_SIZE_SECONDS;
                let s = ps.speed(0, secs).expect("speed");
                assert!(s >= 0.0, "Unexpected negative speed at bucket {i}");
            }
        }

        #[test]
        fn test_compress_decompress_accuracy() {
            // generate speed values for buckets
            let mut speeds = [0f32; BUCKETS_PER_WEEK];
            for i in 0..BUCKETS_PER_WEEK {
                speeds[i] = (30.0f32 + 15.0f32 * (i as f32 / 20.0).sin()).round();
            }

            // compress
            let coeffs = compress_speed_buckets(&speeds);

            // decompress all buckets
            let mut recon = [0f32; BUCKETS_PER_WEEK];
            for i in 0..BUCKETS_PER_WEEK {
                recon[i] = decompress_speed_bucket(&coeffs, i);
            }

            // diffs
            let mut diffs = [0f32; BUCKETS_PER_WEEK];
            for i in 0..BUCKETS_PER_WEEK {
                diffs[i] = (speeds[i] - recon[i]).abs();
            }

            // average error <= 1 KPH
            let l1_err = normalized_l1_norm(&diffs);
            assert!(l1_err <= 1.0, "Low decompression accuracy: L1={l1_err}");

            // max error <= 2 KPH
            let max_diff = diffs.iter().cloned().fold(f32::MIN, f32::max);
            assert!(
                max_diff <= 2.0,
                "Low decompression accuracy: max={max_diff}"
            );
        }

        #[test]
        fn test_speeds_encoder() {
            // fill coefficients alternating +10*i, -10*i
            let mut coefficients = [0i16; COEFFICIENT_COUNT];
            for i in 0..COEFFICIENT_COUNT {
                coefficients[i] = if i % 2 == 0 {
                    (10 * i) as i16
                } else {
                    -(10 * i as i16)
                };
            }

            let expected = "AAD/9gAU/+IAKP/OADz/ugBQ/6YAZP+SAHj/fgCM/2oAoP9WALT/QgDI/y4A3P8aAPD/BgEE/vIBGP7eASz+ygFA/rYBVP6iAWj+jgF8/noBkP5mAaT+UgG4/j4BzP4qAeD+FgH0/gICCP3uAhz92gIw/cYCRP2yAlj9ngJs/YoCgP12ApT9YgKo/U4CvP06AtD9JgLk/RIC+Pz+Awz86gMg/NYDNPzCA0j8rgNc/JoDcPyGA4T8cgOY/F4DrPxKA8D8NgPU/CID6PwOA/z7+gQQ++YEJPvSBDj7vgRM+6oEYPuWBHT7ggSI+24EnPtaBLD7RgTE+zIE2PseBOz7CgUA+vYFFPriBSj6zgU8+roFUPqmBWT6kgV4+n4FjPpqBaD6VgW0+kIFyPouBdz6GgXw+gYGBPnyBhj53gYs+coGQPm2BlT5ogZo+Y4GfPl6BpD5Zgak+VIGuPk+Bsz5Kgbg+RYG9PkCBwj47gcc+NoHMPjGB0T4sgdY+J4HbPiKB4D4dgeU+GIHqPhOB7z4Og==";

            let encoded = encode_compressed_speeds(&coefficients);
            assert_eq!(encoded, expected, "Incorrect encoded string");
        }

        #[test]
        fn test_speeds_decoder() {
            let expected_encoded = "AAD/9gAU/+IAKP/OADz/ugBQ/6YAZP+SAHj/fgCM/2oAoP9WALT/QgDI/y4A3P8aAPD/BgEE/vIBGP7eASz+ygFA/rYBVP6iAWj+jgF8/noBkP5mAaT+UgG4/j4BzP4qAeD+FgH0/gICCP3uAhz92gIw/cYCRP2yAlj9ngJs/YoCgP12ApT9YgKo/U4CvP06AtD9JgLk/RIC+Pz+Awz86gMg/NYDNPzCA0j8rgNc/JoDcPyGA4T8cgOY/F4DrPxKA8D8NgPU/CID6PwOA/z7+gQQ++YEJPvSBDj7vgRM+6oEYPuWBHT7ggSI+24EnPtaBLD7RgTE+zIE2PseBOz7CgUA+vYFFPriBSj6zgU8+roFUPqmBWT6kgV4+n4FjPpqBaD6VgW0+kIFyPouBdz6GgXw+gYGBPnyBhj53gYs+coGQPm2BlT5ogZo+Y4GfPl6BpD5Zgak+VIGuPk+Bsz5Kgbg+RYG9PkCBwj47gcc+NoHMPjGB0T4sgdY+J4HbPiKB4D4dgeU+GIHqPhOB7z4Og==";

            // Build the coefficients array that matches the fixture
            let mut expected_coeffs = [0i16; COEFFICIENT_COUNT];
            for i in 0..COEFFICIENT_COUNT {
                expected_coeffs[i] = if i % 2 == 0 {
                    (10 * i) as i16
                } else {
                    -(10 * i as i16)
                };
            }

            let decoded = decode_base64_speed_coefficients(expected_encoded).expect("decode ok");
            assert_eq!(decoded, expected_coeffs, "Incorrect decoded coefficients");
        }
    }
}
