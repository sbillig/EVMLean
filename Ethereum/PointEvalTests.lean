import Ethereum.Theory.PointEval

/-!
Test vectors for the point evaluation precompile (`0x0a`), run through `Ξ_PointEval`.
The checks run when this module is built (`lake build Ethereum.PointEvalTests`); the library does not
import it.
-/

namespace Ethereum.PointEvalTests

private def bytes (s : String) : ByteArray :=
  match ByteArray.ofBlob s with
  | .ok b => b
  | .error _ => .empty

/-- A nonempty account map, so that failure (an empty map) can be told apart. -/
private def σ₀ : AccountMap := (∅ : AccountMap).insert 0 default

private def env (d : ByteArray) : ExecutionEnv := { (default : ExecutionEnv) with calldata := d }

/-- The gas used and the output of point evaluation on the call data `s` (hex), with 10,000,000 gas, or
`none` if the call fails. -/
private def run (s : String) : Option (ℕ × String) :=
  let (σ, g, _, o) := Ξ_PointEval σ₀ ⟨10000000⟩ default (env (bytes s))
  if σ == ∅ then none else some (10000000 - g.toNat, toHex o)

-- go-ethereum `core/vm/testdata/precompiles/pointEvaluation.json`: gas used and output.
-- pointEvaluation1
#guard run ("01e798154708fe7789429634053cbf9f99b619f9f084048927333fce637f549b564c0a11a0f704f4" ++
    "fc3e8acfe0f8245f0ad1347b378fbf96e206da11a5d3630624d25032e67a7e6a4910df5834b8fe70" ++
    "e6bcfeeac0352434196bdf4b2485d5a18f59a8d2a1a625a17f3fea0fe5eb8c896db3764f3185481b" ++
    "c22f91b4aaffcca25f26936857bc3a7c2539ea8ec3a952b7873033e038326e87ed3e1276fd140253" ++
    "fa08e9fc25fb2d9a98527fc22a2c9612fbeafdad446cbc7bcdbdcd780af2c16a") ==
  some (50000, ("000000000000000000000000000000000000000000000000000000000000100073eda753299d7d48" ++
    "3339d80809a1d80553bda402fffe5bfeffffffff00000001"))

-- The same input with byte 5 of the versioned hash changed.
#guard run ("01e798154718fe7789429634053cbf9f99b619f9f084048927333fce637f549b564c0a11a0f704f4" ++
    "fc3e8acfe0f8245f0ad1347b378fbf96e206da11a5d3630624d25032e67a7e6a4910df5834b8fe70" ++
    "e6bcfeeac0352434196bdf4b2485d5a18f59a8d2a1a625a17f3fea0fe5eb8c896db3764f3185481b" ++
    "c22f91b4aaffcca25f26936857bc3a7c2539ea8ec3a952b7873033e038326e87ed3e1276fd140253" ++
    "fa08e9fc25fb2d9a98527fc22a2c9612fbeafdad446cbc7bcdbdcd780af2c16a") == none
-- The same input without its last byte.
#guard run ("01e798154708fe7789429634053cbf9f99b619f9f084048927333fce637f549b564c0a11a0f704f4" ++
    "fc3e8acfe0f8245f0ad1347b378fbf96e206da11a5d3630624d25032e67a7e6a4910df5834b8fe70" ++
    "e6bcfeeac0352434196bdf4b2485d5a18f59a8d2a1a625a17f3fea0fe5eb8c896db3764f3185481b" ++
    "c22f91b4aaffcca25f26936857bc3a7c2539ea8ec3a952b7873033e038326e87ed3e1276fd140253" ++
    "fa08e9fc25fb2d9a98527fc22a2c9612fbeafdad446cbc7bcdbdcd780af2c1") == none
-- Out of gas.
#guard (Ξ_PointEval σ₀ ⟨49999⟩ default (env (bytes ("01e798154708fe7789429634053cbf9f99b619f9f084048927333fce637f549b564c0a11a0f704f4" ++
      "fc3e8acfe0f8245f0ad1347b378fbf96e206da11a5d3630624d25032e67a7e6a4910df5834b8fe70" ++
      "e6bcfeeac0352434196bdf4b2485d5a18f59a8d2a1a625a17f3fea0fe5eb8c896db3764f3185481b" ++
      "c22f91b4aaffcca25f26936857bc3a7c2539ea8ec3a952b7873033e038326e87ed3e1276fd140253" ++
      "fa08e9fc25fb2d9a98527fc22a2c9612fbeafdad446cbc7bcdbdcd780af2c16a")))).1 == ∅

end Ethereum.PointEvalTests
