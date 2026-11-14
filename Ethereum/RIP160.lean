import Ethereum.Wheels
import Ethereum.RIPEMD160

/-- The output of the RIPEMD-160 precompile: the 20-byte digest of `d`, left-padded
with zeros to 32 bytes. -/
def RIP160 (d : ByteArray) : Except String ByteArray :=
  .ok (ByteArray.zeroes 12 ++ Ethereum.RIPEMD160.hash d)
