/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Least Authority
-/

import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Data.Fintype.Units
import Mathlib.Data.Fintype.Card

namespace SmoothIndex

variable {F: Type*} [Semiring F]
         (ι : Finset F)
         (k : ℕ )


/-- A set ι ⊆ R is `smooth` if `|ι| = 2^k` for some `k` and there exists a subgroup `H`
    in the group of units `Rˣ` and an invertible element `a ∈ R` such that `L = a • H` -/
class Smooth where
  H         : Subgroup (Units F)
  a         : Units F
  coset     : (ι : Set F)
              -- f : α → β, S : Set α  then  f '' S means {y : β ∣ ∃x∈S,y=f(x) }
              = (fun h : Units F => (a : F) * (h : F)) '' (H : Set (Units F)) -- L = a • H
  card_pow2 : ι.card = 2 ^ k

/-- The `k`-th power of `L`,  `L^k := { x^k | x ∈ L }` -/
def powIndex [DecidableEq F] : Finset F :=
  ι.image fun x : F => x ^ k

/-- The fiber `f⁻¹(y)` for the surjection `f : L → L^k, x → x^k` and `y ∈ L^k` -/
def powFiber
  [DecidableEq F] (y : powIndex ι k) : Finset F :=
  ι.filter (fun x => x^ k = y)

end SmoothIndex
