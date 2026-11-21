import Noctium.Frontend

open scoped Noctium

noctium_witness_circuit secp256k1PointLiteral where
  output valuePoint : Secp256k1Point :=
    secp256k1Point(55066263022277343669578718895168534326250603453777594175500187360389116729240,
      32670510020758816978083085130507043184471273380659243275938904335757337482424)
end

noctium_circuit secp256r1PointLiteral where
  output valuePoint : Secp256r1Point :=
    secp256r1Point(48439561293906451759052585252797914202762949526041747995844080717082404635286,
      36134250956749795798585127919587881956611106672985015071877198253568414405109)
end

noctium_circuit curve25519PointLiteral where
  output valuePoint : Curve25519Point :=
    curve25519Point(15112221349535400772501151409588531511454012693041857206046113283949847762202,
      46316835694926478169428394003475163141307993866256225615783033603165251855960)
end

noctium_contract ForeignPointLiterals where
  constructor() where
  end
  entry secp256k1 uses secp256k1PointLiteral where
    return point : Secp256k1Point := valuePoint
  end
  entry secp256r1 uses secp256r1PointLiteral where
    return point : Secp256r1Point := valuePoint
  end
  entry curve25519 uses curve25519PointLiteral where
    return point : Curve25519Point := valuePoint
  end
end

/-- error: foreign point is not canonical or on curve -/
#guard_msgs in
noctium_circuit rejectsOffCurvePoint where
  output point : Secp256k1Point := secp256k1Point(0, 1)
end

/-- error: Noctium expression type mismatch -/
#guard_msgs in
noctium_circuit rejectsMismatchedPointFamily where
  output point : Secp256r1Point := secp256k1Point(55066263022277343669578718895168534326250603453777594175500187360389116729240,
    32670510020758816978083085130507043184471273380659243275938904335757337482424)
end

/-- error: foreign point is not canonical or on curve -/
#guard_msgs in
noctium_circuit rejectsCurve25519SmallSubgroupPoint where
  output point : Curve25519Point :=
    curve25519Point(0, 57896044618658097711785492504343953926634992332820282019728792003956564819948)
end
