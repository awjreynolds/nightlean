import Noctium.Frontend

open scoped Noctium

namespace ScalarSerialization

noctium_circuit transcode where
  private flagFrame : Bytes 3
  private countFrame : Bytes 3
  private fieldFrame : Bytes 34
  private scalarFrame : Bytes 32
  private byteFrame : Bytes 3
  let flag : Bool := deserialize(Bool, flagFrame)
  let count : UIntRange 301 := deserialize(UIntRange 301, countFrame)
  let field : Native := deserialize(Native, fieldFrame)
  let scalar : Secp256k1Scalar := deserialize(Secp256k1Scalar, scalarFrame)
  output flagWire : Bytes 3 := disclose(serialize(flag, 3))
  output countWire : Bytes 4 := disclose(serialize(count, 4))
  output fieldWire : Bytes 34 := disclose(serialize(field, 34))
  output scalarWire : Bytes 32 := disclose(serialize(scalar, 32))
  output bytesWire : Bytes 5 := disclose(serialize(deserialize(Bytes 2, byteFrame), 5))
end

noctium_contract Codec where
  entry transcode uses transcode where
    return flagEncoding : Bytes 3 := flagWire
    return countEncoding : Bytes 4 := countWire
    return fieldEncoding : Bytes 34 := fieldWire
    return scalarEncoding : Bytes 32 := scalarWire
    return bytesEncoding : Bytes 5 := bytesWire
  end
end

end ScalarSerialization
