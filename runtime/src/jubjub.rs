use anyhow::{Result, anyhow, ensure};
use serialize::Deserializable;
use std::io::Cursor;
use transient_crypto::curve::{EmbeddedFr, EmbeddedGroupAffine, Fr};

pub(crate) fn scalar(text: &str) -> Result<EmbeddedFr> {
    EmbeddedFr::try_from(crate::canonical_field(text)?)
        .map_err(|_| anyhow!("Jubjub scalar out of range"))
}

pub(crate) fn reduce_scalar(value: Fr) -> Result<EmbeddedFr> {
    EmbeddedFr::from_le_bytes_wide(&value.as_le_bytes())
        .ok_or_else(|| anyhow!("invalid Jubjub scalar encoding"))
}

pub(crate) fn scalar_native(value: EmbeddedFr) -> Result<Fr> {
    Fr::try_from(value).map_err(|_| anyhow!("Jubjub scalar does not fit Native"))
}

pub(crate) fn point(x: Fr, y: Fr) -> Result<EmbeddedGroupAffine> {
    let expected = [x, y];
    let x_bytes: [u8; 32] = x
        .as_le_bytes()
        .try_into()
        .map_err(|_| anyhow!("invalid Jubjub coordinate encoding"))?;
    let mut encoded: [u8; 32] = y
        .as_le_bytes()
        .try_into()
        .map_err(|_| anyhow!("invalid Jubjub coordinate encoding"))?;
    encoded[31] = (encoded[31] & 0x7f) | ((x_bytes[0] & 1) << 7);

    // Decode through the subgroup-checked encoding boundary.
    let point = from_bytes(&encoded)?;
    ensure!(
        coordinates(point)? == expected,
        "Jubjub coordinates do not round trip"
    );
    Ok(point)
}

pub(crate) fn to_bytes(point: EmbeddedGroupAffine) -> Result<[u8; 32]> {
    let [x, y] = coordinates(point)?;
    let mut encoded: [u8; 32] = y
        .as_le_bytes()
        .try_into()
        .map_err(|_| anyhow!("invalid Jubjub coordinate encoding"))?;
    encoded[31] = (encoded[31] & 0x7f) | ((x.as_le_bytes()[0] & 1) << 7);
    Ok(encoded)
}

pub(crate) fn from_bytes(encoded: &[u8]) -> Result<EmbeddedGroupAffine> {
    ensure!(
        encoded.len() == 32,
        "Jubjub point encoding requires 32 bytes"
    );
    let mut reader = Cursor::new(encoded);
    let point = EmbeddedGroupAffine::deserialize(&mut reader, 0)
        .map_err(|_| anyhow!("invalid Jubjub point"))?;
    ensure!(
        reader.position() == 32 && to_bytes(point)?.as_slice() == encoded,
        "noncanonical Jubjub point encoding"
    );
    Ok(point)
}

pub(crate) fn coordinates(point: EmbeddedGroupAffine) -> Result<[Fr; 2]> {
    Ok([
        point
            .x()
            .ok_or_else(|| anyhow!("missing Jubjub x coordinate"))?,
        point
            .y()
            .ok_or_else(|| anyhow!("missing Jubjub y coordinate"))?,
    ])
}
