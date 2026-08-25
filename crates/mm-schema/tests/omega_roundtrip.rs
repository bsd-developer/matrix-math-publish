//! Canonical encoding of omega certificates (§3.5, §6.3, §6.5).
#![allow(
    clippy::expect_used,
    clippy::panic,
    clippy::unwrap_used,
    reason = "test assertions must fail loudly; §17.1 governs library code"
)]

use mm_schema::{CanonicalReader, CanonicalWriter, Limits, decode_omega, encode_omega};

fn fixture(name: &str) -> Vec<u8> {
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../tests/vectors")
        .join(name);
    std::fs::read(&path).unwrap_or_else(|error| panic!("read {path:?}: {error}"))
}

/// §3.5: the decoded typed values must re-encode to the published bytes exactly.
/// Without this a generated Lean module could prove a theorem about data other
/// than what was published.
#[test]
fn the_hand_fixture_round_trips_byte_for_byte() {
    let bytes = fixture("omega-l2-hand.json");
    let mut reader =
        CanonicalReader::new(std::io::BufReader::new(bytes.as_slice()), Limits::default());
    let certificate = decode_omega(&mut reader).expect("decode");
    let published_digest = reader.finish().expect("digest");

    let mut out: Vec<u8> = Vec::new();
    let (digest, byte_count) = encode_omega(&mut out, &certificate).expect("encode");

    assert_eq!(
        out, bytes,
        "re-encoded bytes differ from the published bytes"
    );
    assert_eq!(digest, published_digest);
    assert_eq!(byte_count as usize, bytes.len());
}

/// An object nested directly inside an array is the shape omega certificates
/// use for every block and node. Emitting it through `begin_object` must not
/// take the array's element separator for the object's own members.
#[test]
fn objects_nested_in_arrays_do_not_borrow_the_array_separator() {
    let mut out: Vec<u8> = Vec::new();
    {
        let mut writer = CanonicalWriter::new(&mut out);
        writer.begin_array().expect("array");
        for value in ["1", "2"] {
            writer.begin_object().expect("object");
            writer.key("d").expect("key");
            writer.string("10").expect("string");
            writer.key("n").expect("key");
            writer.string(value).expect("string");
            writer.end_object().expect("end object");
        }
        writer.end_array().expect("end array");
        writer.finish().expect("finish");
    }
    assert_eq!(
        String::from_utf8(out).expect("utf8"),
        r#"[{"d":"10","n":"1"},{"d":"10","n":"2"}]"#
    );
}
