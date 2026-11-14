import Ethereum.Weierstrass.Lucas
import Ethereum.BN254.Impl

/-!
The order `r` of the group of points of alt_bn128 (BN254), the modulus of its scalar field
(EIP-196), and its primality.

The certificate is `prime_of_lucas` applied to a witness and the prime factors of `r - 1`,
nested for the large factors (a Pratt certificate), as for `p` in `Prime.lean`.
-/

namespace Ethereum.BN254

open Weierstrass

/-- The order of the group of points of alt_bn128, the modulus of its scalar field. -/
def r : Nat := 21888242871839275222246405745257275088548364400416034343698204186575808495617

private theorem r_prime_237073 : Nat.Prime 237073 :=
  prime_of_lucas 237073 15 [2, 2, 2, 2, 3, 11, 449]
    (by decide) (by decide) (by prime_factors [])
    (by decide +kernel) (by decide +kernel)

private theorem r_prime_1593227 : Nat.Prime 1593227 :=
  prime_of_lucas 1593227 2 [2, 19, 41927]
    (by decide) (by decide) (by prime_factors [])
    (by decide +kernel) (by decide +kernel)

private theorem r_prime_405928799 : Nat.Prime 405928799 :=
  prime_of_lucas 405928799 22 [2, 11, 3691, 4999]
    (by decide) (by decide) (by prime_factors [])
    (by decide +kernel) (by decide +kernel)

private theorem r_prime_639533339 : Nat.Prime 639533339 :=
  prime_of_lucas 639533339 2 [2, 229, 853, 1637]
    (by decide) (by decide) (by prime_factors [])
    (by decide +kernel) (by decide +kernel)

private theorem r_prime_12048837557 : Nat.Prime 12048837557 :=
  prime_of_lucas 12048837557 2 [2, 2, 7, 7, 661, 93001]
    (by decide) (by decide) (by prime_factors [])
    (by decide +kernel) (by decide +kernel)

private theorem r_prime_5156902474397 : Nat.Prime 5156902474397 :=
  prime_of_lucas 5156902474397 2 [2, 2, 107, 12048837557]
    (by decide) (by decide) (by prime_factors [r_prime_12048837557])
    (by decide +kernel) (by decide +kernel)

private theorem r_prime_1670836401704629 : Nat.Prime 1670836401704629 :=
  prime_of_lucas 1670836401704629 2 [2, 2, 3, 3, 3, 3, 5156902474397]
    (by decide) (by decide) (by prime_factors [r_prime_5156902474397])
    (by decide +kernel) (by decide +kernel)

private theorem r_prime_65865678001877903 : Nat.Prime 65865678001877903 :=
  prime_of_lucas 65865678001877903 5 [2, 83, 379, 1637, 639533339]
    (by decide) (by decide) (by prime_factors [r_prime_639533339])
    (by decide +kernel) (by decide +kernel)

private theorem r_prime_13818364434197438864469338081 : Nat.Prime 13818364434197438864469338081 :=
  prime_of_lucas 13818364434197438864469338081 3 [2, 2, 2, 2, 2, 5, 823, 1593227, 65865678001877903]
    (by decide) (by decide) (by prime_factors [r_prime_1593227, r_prime_65865678001877903])
    (by decide +kernel) (by decide +kernel)

/-- The group order `r` is prime. -/
theorem r_prime : Nat.Prime r :=
  prime_of_lucas r 5
    [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3,
     13, 29, 983, 11003, 237073, 405928799, 1670836401704629, 13818364434197438864469338081]
    (by decide) (by decide)
    (by prime_factors [r_prime_237073, r_prime_405928799, r_prime_1670836401704629,
      r_prime_13818364434197438864469338081])
    (by decide +kernel) (by decide +kernel)

end Ethereum.BN254
