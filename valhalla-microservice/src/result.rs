use crate::http_protocol::HttpRequestInfo;
use http::header::{ACCESS_CONTROL_ALLOW_ORIGIN, CONNECTION, CONTENT_LENGTH, CONTENT_TYPE};
use http::{HeaderMap, StatusCode};
use itertools::intersperse;
use serde::Serialize;

/// The result of a worker computation.
pub enum WorkerResult {
    /// An HTTP response to be delivered to the user.
    ///
    /// No further processing will be done downstream.
    /// Use helper methods like [`WorkerResult::json`] wherever possible to avoid footguns,
    /// like forgetting to set headers.
    HttpResponse {
        status_code: StatusCode,
        /// A map of HTTP headers.
        ///
        /// If you are constructing this enum variant on your own (or implementing a new helper),
        /// be careful to set `Content-Type`, and any other headers specific to this type of response.
        ///
        /// `Content-Length`, `Access-Control-Allow-Origin`, and `Connection`
        /// may be set automatically during serialization; any values you set here will be clobbered.
        headers: HeaderMap,
        body: Vec<u8>,
    },
    // TODO: Figure out the other variants here...
    PlaceholderDownstreamTBD,
}

impl WorkerResult {
    /// Helper for constructing a JSON HTTP response.
    pub fn json<T: Serialize>(status_code: StatusCode, value: T) -> WorkerResult {
        #[expect(clippy::missing_panics_doc)]
        let body = serde_json::to_vec(&value).expect("Programming error: either Serialize is incorrectly implemented, or the structure contains a map with non-string keys.");
        let mut headers = HeaderMap::new();
        headers.insert(
            CONTENT_TYPE,
            #[expect(clippy::missing_panics_doc)]
            "application/json;charset=utf-8".parse().unwrap(),
        );

        WorkerResult::HttpResponse {
            status_code,
            headers,
            body,
        }
    }
}

pub(crate) fn serialize_http(
    request_info: HttpRequestInfo,
    status_code: StatusCode,
    headers: HeaderMap,
    body: Vec<u8>,
) -> Vec<u8> {
    let prelude: Vec<u8> =
        format!("{} {}\r\n", request_info.http_version_string(), status_code).into_bytes();
    let mut headers = headers;
    headers.insert(CONTENT_LENGTH, body.len().to_string().parse().unwrap());
    headers.insert(ACCESS_CONTROL_ALLOW_ORIGIN, "*".parse().unwrap());

    if request_info.connection_keep_alive() {
        headers.insert(CONNECTION, "Keep-Alive".parse().unwrap());
    } else if request_info.connection_close() {
        headers.insert(CONNECTION, "Close".parse().unwrap());
    }

    let headers: Vec<u8> = intersperse(
        headers
            .iter()
            .map(|(name, value)| [name.as_str().as_bytes(), b": ", value.as_bytes()].concat()),
        "\r\n".to_string().into_bytes(),
    )
    .flatten()
    .collect();

    [prelude, headers, "\r\n\r\n".to_string().into_bytes(), body].concat()
}

#[cfg(test)]
mod tests {
    use super::*;
    use zerocopy::transmute;

    #[test]
    fn test_serialize_http() {
        const BODY: &[u8] = br#"{"version":"3.5.1","tileset_last_modified":1756439278,"available_actions":["status","centroid","expansion","transit_available","trace_attributes","trace_route","isochrone","optimized_route","sources_to_targets","height","route","locate"]}"#;
        const REQ_INFO_BYTES: [u8; 12] = [
            0x00, 0x00, 0x00, 0x00, 0xf5, 0x76, 0xb1, 0x68, 0x01, 0x00, 0x00, 0x00,
        ];
        let req_info: HttpRequestInfo = transmute!(REQ_INFO_BYTES);

        let mut headers = HeaderMap::new();
        headers.insert(
            CONTENT_TYPE,
            "application/json;charset=utf-8".parse().unwrap(),
        );
        headers.insert(CONTENT_LENGTH, BODY.len().to_string().parse().unwrap());

        let result = serialize_http(req_info, StatusCode::OK, headers, BODY.to_vec());

        let reesult_utf8 = String::from_utf8(result).expect("Expected a UTF-8 result.");

        if !cfg!(miri) {
            insta::assert_snapshot!(reesult_utf8);
        }
    }
}
