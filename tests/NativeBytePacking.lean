import Noctium.Frontend

open scoped Noctium

noctium_circuit packingInputs where
  private b1 : Bytes 1
  private b31 : Bytes 31
  private b32 : Bytes 32
  private b62 : Bytes 62
  private b63 : Bytes 63
  private empty0 : Bytes 0
end

noctium_contract NativeBytePacking where
  entry pack uses packingInputs where
    return r1 : Bytes 1 := disclose(reverseBytes(b1))
    return r31 : Bytes 31 := disclose(reverseBytes(b31))
    return r32 : Bytes 32 := disclose(reverseBytes(b32))
    return r62 : Bytes 62 := disclose(reverseBytes(b62))
    return r63 : Bytes 63 := disclose(reverseBytes(b63))
    return emptyResult : Bytes 0 := disclose(reverseBytes(empty0))
  end
end
