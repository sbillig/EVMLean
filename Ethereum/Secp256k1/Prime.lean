import Ethereum.Weierstrass.Lucas
import Ethereum.Secp256k1.Impl

/-!
The primality of secp256k1's field prime `p` and group order `n`.

Each certificate below is `prime_of_lucas` applied to a witness and the prime
factors of `m - 1`. Factors below `10⁵` are proved prime by `norm_num`, larger
ones by their own certificate, and the modular powers are evaluated by the
kernel (`decide +kernel`). The factorizations were computed with GNU `factor`
or taken from the certificates of ethereum/EthLib
(`EthLib/Cryptography/Proofs/Secp256k1/Field.lean`, CC0-1.0); the kernel checks
every product and power.
-/

namespace Ethereum.Secp256k1

open Weierstrass

private theorem prime_120233 : Nat.Prime 120233 :=
  prime_of_lucas 120233 3 [2, 2, 2, 7, 19, 113]
    (by decide) (by decide) (by prime_factors [])
    (by decide +kernel) (by decide +kernel)

private theorem prime_305873 : Nat.Prime 305873 :=
  prime_of_lucas 305873 3 [2, 2, 2, 2, 7, 2731]
    (by decide) (by decide) (by prime_factors [])
    (by decide +kernel) (by decide +kernel)

private theorem prime_1206781 : Nat.Prime 1206781 :=
  prime_of_lucas 1206781 10 [2, 2, 3, 5, 20113]
    (by decide) (by decide) (by prime_factors [])
    (by decide +kernel) (by decide +kernel)

private theorem prime_1627771 : Nat.Prime 1627771 :=
  prime_of_lucas 1627771 3 [2, 3, 5, 29, 1871]
    (by decide) (by decide) (by prime_factors [])
    (by decide +kernel) (by decide +kernel)

private theorem prime_4681609 : Nat.Prime 4681609 :=
  prime_of_lucas 4681609 23 [2, 2, 2, 3, 97, 2011]
    (by decide) (by decide) (by prime_factors [])
    (by decide +kernel) (by decide +kernel)

private theorem prime_7240687 : Nat.Prime 7240687 :=
  prime_of_lucas 7240687 3 [2, 3, 1206781]
    (by decide) (by decide) (by prime_factors [prime_1206781])
    (by decide +kernel) (by decide +kernel)

private theorem prime_13331831 : Nat.Prime 13331831 :=
  prime_of_lucas 13331831 13 [2, 5, 971, 1373]
    (by decide) (by decide) (by prime_factors [])
    (by decide +kernel) (by decide +kernel)

private theorem prime_44706919 : Nat.Prime 44706919 :=
  prime_of_lucas 44706919 6 [2, 3, 797, 9349]
    (by decide) (by decide) (by prime_factors [])
    (by decide +kernel) (by decide +kernel)

private theorem prime_107590001 : Nat.Prime 107590001 :=
  prime_of_lucas 107590001 3 [2, 2, 2, 2, 5, 5, 5, 5, 7, 29, 53]
    (by decide) (by decide) (by prime_factors [])
    (by decide +kernel) (by decide +kernel)

private theorem prime_545358713 : Nat.Prime 545358713 :=
  prime_of_lucas 545358713 5 [2, 2, 2, 41, 59, 28181]
    (by decide) (by decide) (by prime_factors [])
    (by decide +kernel) (by decide +kernel)

private theorem prime_297159362677 : Nat.Prime 297159362677 :=
  prime_of_lucas 297159362677 2 [2, 2, 3, 3, 11, 461, 1627771]
    (by decide) (by decide) (by prime_factors [prime_1627771])
    (by decide +kernel) (by decide +kernel)

private theorem prime_107361793816 : Nat.Prime 107361793816595537 :=
  prime_of_lucas 107361793816595537 3 [2, 2, 2, 2, 16699, 85831, 4681609]
    (by decide) (by decide) (by prime_factors [prime_4681609])
    (by decide +kernel) (by decide +kernel)

private theorem prime_173378833005 : Nat.Prime 173378833005251801 :=
  prime_of_lucas 173378833005251801 6 [2, 2, 2, 5, 5, 2621, 24809, 13331831]
    (by decide) (by decide) (by prime_factors [prime_13331831])
    (by decide +kernel) (by decide +kernel)

private theorem prime_174723607534 : Nat.Prime 174723607534414371449 :=
  prime_of_lucas 174723607534414371449 3 [2, 2, 2, 17, 59, 4051, 120233, 44706919]
    (by decide) (by decide) (by prime_factors [prime_120233, prime_44706919])
    (by decide +kernel) (by decide +kernel)

private theorem prime_221494926740 : Nat.Prime 22149492674086928081353 :=
  prime_of_lucas 22149492674086928081353 5 [2, 2, 2, 3, 5323, 173378833005251801]
    (by decide) (by decide) (by prime_factors [prime_173378833005])
    (by decide +kernel) (by decide +kernel)

private theorem prime_132896956044 : Nat.Prime 132896956044521568488119 :=
  prime_of_lucas 132896956044521568488119 6 [2, 3, 22149492674086928081353]
    (by decide) (by decide) (by prime_factors [prime_221494926740])
    (by decide +kernel) (by decide +kernel)

private theorem prime_290476118734 : Nat.Prime 29047611873442575647497758179 :=
  prime_of_lucas 29047611873442575647497758179 2 [2, 293, 305873, 545358713, 297159362677]
    (by decide) (by decide) (by prime_factors [prime_305873, prime_545358713, prime_297159362677])
    (by decide +kernel) (by decide +kernel)

private theorem prime_341948486974 : Nat.Prime 341948486974166000522343609283189 :=
  prime_of_lucas 341948486974166000522343609283189 2
    [2, 2, 3, 3, 3, 109, 29047611873442575647497758179]
    (by decide) (by decide) (by prime_factors [prime_290476118734])
    (by decide +kernel) (by decide +kernel)

private theorem prime_255515944373 : Nat.Prime 255515944373312847190720520512484175977 :=
  prime_of_lucas 255515944373312847190720520512484175977 3
    [2, 2, 2, 7, 7, 11, 1627, 2657, 4423, 41201, 96557, 7240687, 107590001]
    (by decide) (by decide) (by prime_factors [prime_7240687, prime_107590001])
    (by decide +kernel) (by decide +kernel)

private theorem prime_205115282021 :
    Nat.Prime 205115282021455665897114700593932402728804164701536103180137503955397371 :=
  prime_of_lucas 205115282021455665897114700593932402728804164701536103180137503955397371 10
    [2, 3, 5, 29, 29, 31, 7723, 132896956044521568488119, 255515944373312847190720520512484175977]
    (by decide) (by decide) (by prime_factors [prime_132896956044, prime_255515944373])
    (by decide +kernel) (by decide +kernel)

/-- The group order `n` is prime. -/
theorem n_prime : Nat.Prime n :=
  prime_of_lucas n 7
    [2, 2, 2, 2, 2, 2, 3, 149, 631, 107361793816595537, 174723607534414371449,
     341948486974166000522343609283189]
    (by decide) (by decide)
    (by prime_factors [prime_107361793816, prime_174723607534, prime_341948486974])
    (by decide +kernel) (by decide +kernel)

/-- The field prime `p` is prime. -/
theorem p_prime : Nat.Prime p :=
  prime_of_lucas p 3
    [2, 3, 7, 13441, 205115282021455665897114700593932402728804164701536103180137503955397371]
    (by decide) (by decide) (by prime_factors [prime_205115282021])
    (by decide +kernel) (by decide +kernel)

end Ethereum.Secp256k1
