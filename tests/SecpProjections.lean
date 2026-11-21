import Noctium.Frontend

open scoped Noctium

noctium_circuit secpProjectionInputs where
  private kPoint : Secp256k1Point
  private kScalar : Secp256k1Scalar
  private rPoint : Secp256r1Point
  private rScalar : Secp256r1Scalar
end

noctium_contract SecpProjections where
  entry inspect uses secpProjectionInputs where
    return kPointResult : Secp256k1Point := disclose(kPoint)
    return kScalarResult : Secp256k1Scalar := disclose(kScalar)
    return kX : Secp256k1Base := disclose(curveX(kPoint))
    return kY : Secp256k1Base := disclose(curveY(kPoint))
    return rPointResult : Secp256r1Point := disclose(rPoint)
    return rScalarResult : Secp256r1Scalar := disclose(rScalar)
    return rX : Secp256r1Base := disclose(curveX(rPoint))
    return rY : Secp256r1Base := disclose(curveY(rPoint))
  end
end
