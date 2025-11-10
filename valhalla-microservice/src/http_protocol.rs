//! HTTP-specific data structures.
//!
//! These mirror equivalent concepts from `prime_server`'s `http_protocol.hpp`.

use bitfield_struct::bitfield;
use tracing::warn;
use zerocopy::{LE, U16, U32};
use zerocopy_derive::{FromBytes, Immutable, IntoBytes, Unaligned};

/// HTTP request info.
///
/// In Valhalla service workers,
/// this is passed as the first message in any exchange sequence.
#[derive(FromBytes, IntoBytes, Immutable, Unaligned, Debug, Copy, Clone)]
#[repr(C)]
pub struct HttpRequestInfo {
    /// The request ID
    id: U32<LE>,
    /// The request timestamp.
    ///
    /// This SHOULD be an integer seconds UNIX timestamp
    /// (though it technically isn't specified very well).
    /// This is eventually going to run out of space (year-based bugs)
    /// or hit some bad behavior!
    timestamp: U32<LE>,
    inner_bitfield: HttpRequestInfoInnerBitfield,
    /// Required padding to make the struct 16-byte aligned.
    ///
    /// NB: This is implicit in the C++ struct definition.
    _spare: U16<LE>,
}

#[bitfield(u16,
    repr = U16<LE>,
    from = bit_twiddling_helpers::conv_u16le::from_inner,
    into = bit_twiddling_helpers::conv_u16le::into_inner
)]
#[derive(FromBytes, IntoBytes, Immutable, Unaligned)]
struct HttpRequestInfoInnerBitfield {
    /// Protocol-specific space for versioning info.
    ///
    /// Valhalla seems to use the following values:
    /// * 0 - HTTP/1.0
    /// * 1 - Technically anything else
    #[bits(3)]
    version: u8,
    /// Indicates whether the header is present or not
    #[bits(1)]
    connection_keep_alive: bool,
    /// Indicates whether the header is present or not
    #[bits(1)]
    connection_close: bool,
    /// What response code was set to when sent back to the client
    #[bits(10, from = bit_twiddling_helpers::conv_u16le::from_inner, into = bit_twiddling_helpers::conv_u16le::into_inner)]
    response_code: U16<LE>,
    /// Spare padding bits to be explicit about alignment
    #[bits(1)]
    _spare: u8,
}

impl HttpRequestInfo {
    /// The request ID (generated serially by Valhalla).
    pub fn id(&self) -> u32 {
        self.id.into()
    }

    /// The HTTP version string for this request (e.g. "HTTP/1.1").
    pub fn http_version_string(&self) -> &'static str {
        let version = self.inner_bitfield.version();
        match version {
            0 => "HTTP/1.0",
            1 => "HTTP/1.1",
            _ => {
                warn!(
                    "Unknown HTTP version from Valhalla service: {}; treating it as HTTP/1.1",
                    version
                );

                "HTTP/1.1"
            }
        }
    }

    pub fn connection_keep_alive(&self) -> bool {
        self.inner_bitfield.connection_keep_alive()
    }

    pub fn connection_close(&self) -> bool {
        self.inner_bitfield.connection_close()
    }

    pub fn set_response_code(&mut self, code: u16) {
        self.inner_bitfield.set_response_code(code.into());
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use zerocopy::transmute;

    #[test]
    fn decode_http_info_message() {
        const MESSAGE: [u8; 12] = [
            0x00, 0x00, 0x00, 0x00, 0xf5, 0x76, 0xb1, 0x68, 0x01, 0x00, 0x00, 0x00,
        ];
        let parsed: HttpRequestInfo = transmute!(MESSAGE);

        if !cfg!(miri) {
            insta::assert_debug_snapshot!(parsed);
        }
    }
}
