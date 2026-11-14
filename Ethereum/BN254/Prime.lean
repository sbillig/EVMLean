import Ethereum.Weierstrass.Lucas
import Ethereum.BN254.Impl

/-!
The primality of the alt_bn128 (BN254) field prime `p`.

The certificate is `prime_of_lucas` applied to a witness and the prime factors of
`p - 1`, nested for the large factors (a Pratt certificate). Factors below `10⁵`
are proved prime by `norm_num`; the factorizations were computed with GNU
`factor`, and the kernel checks every product and power (`decide +kernel`).
-/

namespace Ethereum.BN254

open Weierstrass

private theorem prime_327599 : Nat.Prime 327599 :=
  prime_of_lucas 327599 19 [2, 19, 37, 233]
    (by decide) (by decide) (by prime_factors [])
    (by decide +kernel) (by decide +kernel)

private theorem prime_1853641 : Nat.Prime 1853641 :=
  prime_of_lucas 1853641 17 [2, 2, 2, 3, 3, 5, 19, 271]
    (by decide) (by decide) (by prime_factors [])
    (by decide +kernel) (by decide +kernel)

private theorem prime_4562087 : Nat.Prime 4562087 :=
  prime_of_lucas 4562087 5 [2, 17, 109, 1231]
    (by decide) (by decide) (by prime_factors [])
    (by decide +kernel) (by decide +kernel)

private theorem prime_173171039 : Nat.Prime 173171039 :=
  prime_of_lucas 173171039 13 [2, 73, 89, 13327]
    (by decide) (by decide) (by prime_factors [])
    (by decide +kernel) (by decide +kernel)

private theorem prime_405928799 : Nat.Prime 405928799 :=
  prime_of_lucas 405928799 22 [2, 11, 3691, 4999]
    (by decide) (by decide) (by prime_factors [])
    (by decide +kernel) (by decide +kernel)

private theorem prime_1263766531 : Nat.Prime 1263766531 :=
  prime_of_lucas 1263766531 10 [2, 3, 5, 13, 911, 3557]
    (by decide) (by decide) (by prime_factors [])
    (by decide +kernel) (by decide +kernel)

private theorem prime_11465965001 : Nat.Prime 11465965001 :=
  prime_of_lucas 11465965001 3 [2, 2, 2, 5, 5, 5, 5, 7, 327599]
    (by decide) (by decide) (by prime_factors [prime_327599])
    (by decide +kernel) (by decide +kernel)

private theorem prime_35385462869 : Nat.Prime 35385462869 :=
  prime_of_lucas 35385462869 2 [2, 2, 7, 1263766531]
    (by decide) (by decide) (by prime_factors [prime_1263766531])
    (by decide +kernel) (by decide +kernel)

private theorem prime_248087480174 : Nat.Prime 2480874801745591 :=
  prime_of_lucas 2480874801745591 6 [2, 3, 3, 5, 19, 41, 35385462869]
    (by decide) (by decide) (by prime_factors [prime_35385462869])
    (by decide +kernel) (by decide +kernel)

private theorem prime_134276886673 : Nat.Prime 13427688667394608761327070753331941386769 :=
  prime_of_lucas 13427688667394608761327070753331941386769 17
    [2, 2, 2, 2, 3, 7, 11, 1853641, 4562087, 173171039, 2480874801745591]
    (by decide) (by decide)
    (by prime_factors [prime_1853641, prime_4562087, prime_173171039, prime_248087480174])
    (by decide +kernel) (by decide +kernel)

/-- The field prime `p` is prime. -/
theorem p_prime : Nat.Prime p :=
  prime_of_lucas p 3
    [2, 3, 3, 13, 29, 67, 229, 311, 983, 11003, 405928799, 11465965001,
     13427688667394608761327070753331941386769]
    (by decide) (by decide)
    (by prime_factors [prime_405928799, prime_11465965001, prime_134276886673])
    (by decide +kernel) (by decide +kernel)

end Ethereum.BN254
