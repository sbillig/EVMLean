import Ethereum.PrecompileOutput

namespace ffi

@[extern "blake2compressb64"]
opaque BLAKE2Compress (input : @& ByteArray) : ByteArray

def BLAKE2 (d : ByteArray) : Except String ByteArray := do
  if d.size != 213                    then throw "error"
  if d[212]! ∉ [0, 1].map Nat.toUInt8 then throw "error"
  Ethereum.checkedPrecompileOutput "BLAKE2" 64 <|
    .ok (BLAKE2Compress d)

end ffi
