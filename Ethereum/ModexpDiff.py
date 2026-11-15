"""Compare the MODEXP precompile `Ξ_EXPMOD` with Python's `pow(b, e, m)` on generated inputs.

Run from the repository root: `python3 Ethereum/ModexpDiff.py [count] [seed]`. It writes a Lean
file of `#guard` checks to a temporary directory, runs `lake env lean` on it, and reports the
cases that disagree. The inputs cover zero lengths, a zero modulus, lengths that are not
multiples of 8 or 32, exponents with leading zero bytes, call data shorter and longer than the
declared lengths, and bases and moduli up to a few hundred bytes.
"""

import os
import random
import subprocess
import sys
import tempfile


def field(d, off, w):
    seg = d[off:off + w]
    return int.from_bytes(seg + bytes(w - len(seg)), "big")


def expected(d):
    bl, el, ml = field(d, 0, 32), field(d, 32, 32), field(d, 64, 32)
    b, e = field(d, 96, bl), field(d, 96 + bl, el)
    m = field(d, 96 + bl + el, ml)
    r = 0 if m == 0 else pow(b, e, m)
    return r.to_bytes(ml, "big")


def number(rng, n, lead_zeros=0):
    if n == 0:
        return b""
    z = min(lead_zeros, n)
    return bytes(z) + bytes(rng.randrange(256) for _ in range(n - z))


def case(rng):
    lengths = [0, 1, 2, 3, 5, 7, 8, 9, 15, 16, 17, 31, 32, 33, 40, 63, 64, 65, 100, 127, 128,
               129, 200, 255, 256, 257, 300]
    bl = rng.choice(lengths)
    el = rng.choice([0, 1, 2, 3, 7, 8, 9, 31, 32, 33, 40, 64])
    ml = rng.choice(lengths)
    base = number(rng, bl, rng.choice([0, 0, 1, 5]))
    exp = number(rng, el, rng.choice([0, 0, 1, 3, 31]))
    mod = number(rng, ml, rng.choice([0, 0, 0, 1]))
    if ml and rng.random() < 0.1:
        mod = bytes(ml)  # a zero modulus
    data = (bl.to_bytes(32, "big") + el.to_bytes(32, "big") + ml.to_bytes(32, "big")
            + base + exp + mod)
    shape = rng.random()
    if shape < 0.15:
        data = data[:rng.randrange(len(data) + 1)]  # shorter than declared
    elif shape < 0.3:
        data = data + number(rng, rng.randrange(1, 40))  # longer than declared
    return data


HEADER = """import Ethereum.PrecompiledContracts

open Ethereum

private def bytes (s : String) : ByteArray :=
  match ByteArray.ofBlob s with
  | .ok b => b
  | .error _ => .empty

private def hex (b : ByteArray) : String :=
  let d := "0123456789abcdef".toList.toArray
  String.ofList <| b.data.toList.flatMap fun x => [d[x.toNat / 16]!, d[x.toNat % 16]!]

private def run (s : String) : String :=
  let I : ExecutionEnv := { (default : ExecutionEnv) with calldata := bytes s }
  hex (Ξ_EXPMOD ∅ (UInt256.ofNat (2 ^ 255)) default I).2.2.2

"""


def main():
    count = int(sys.argv[1]) if len(sys.argv) > 1 else 500
    seed = int(sys.argv[2]) if len(sys.argv) > 2 else 2565
    rng = random.Random(seed)
    cases = [case(rng) for _ in range(count)]
    with tempfile.TemporaryDirectory() as tmp:
        path = os.path.join(tmp, "ModexpDiff.lean")
        with open(path, "w") as f:
            f.write(HEADER)
            for d in cases:
                f.write(f'#guard run "{d.hex()}" == "{expected(d).hex()}"\n')
        result = subprocess.run(["lake", "env", "lean", path], capture_output=True, text=True)
    failures = result.stdout.count("error:") + result.stderr.count("error:")
    print(f"{count} cases, {failures} disagreements")
    if failures:
        print(result.stdout[:4000], result.stderr[:4000])
    return 1 if failures else 0


if __name__ == "__main__":
    sys.exit(main())
