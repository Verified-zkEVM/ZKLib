/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Least Authority
-/

import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Data.Fintype.Units
import Mathlib.Data.Fintype.Card

/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Least Authority
-/

import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Data.Fintype.Units
import Mathlib.Data.Fintype.Card

namespace SmoothDomain

variable {F: Type*} [Semiring F] [DecidableEq F]
         {ι : Type*} [Fintype ι]

/-- A domain `ι ↪ F` is `smooth`, if `ι ⊆ F`, `|ι| = 2^k` for some `k` and
    there exists a subgroup `H` in the group of units `Rˣ`
    and an invertible element `a ∈ R` such that `ι = a • H` -/
class Smooth
  [DecidableEq ι]
  (domain : ι ↪ F) where
    H           : Subgroup (Units F)
    a           : Units F
    h_coset     : Finset.image domain Finset.univ
                  = (fun h : Units F => (a : F) * (h : F)) '' (H : Set (Units F))
    h_card_pow2 : ∃ k : ℕ, Fintype.card ι = 2 ^ k

/-- The `k`-th power of a domain `ι`, i.e the set `ιᵏ := {xᵏ | x ∈ ι }. -/
def indexPow (domain : ι ↪ F) (k : ℕ) : Finset F :=
  Finset.image (fun x => (domain x) ^ k) Finset.univ

/-- The k-th power domain `ιᵏ ↪ F` for a given domain `ι ↪ F`. -/
def pow (domain : ι ↪ F) (k : ℕ) : indexPow domain k ↪ F :=
    Function.Embedding.subtype fun y => y ∈ indexPow domain k

/-- The fiber `f⁻¹(y)` for the surjection `f : ι → ιᵏ, x ↦ xᵏ` and `y ∈ ιᵏ` -/
def powFiber (domain : ι ↪ F) (k : ℕ) (y : F) : Finset ι :=
  Finset.univ.filter (fun x => (domain x)^k = y)

/-- The fiber domain `f⁻¹(y) ↪ F` for the surjection `f : ι → ιᵏ, x ↦ xᵏ` and `y ∈ ιᵏ`. -/
def fiber (domain : ι ↪ F) (k : ℕ) (y : F) : {z : ι // z ∈ powFiber domain k y} ↪ F :=
  ⟨domain ∘ Subtype.val, sorry⟩


section
-- Test

variable  {F : Type*} [Semiring F] [DecidableEq F]
          {ι₁ : Type*} [Fintype ι₁] [DecidableEq ι₁]
          (dom : ι₁ ↪ F)
          (k : ℕ)
          (y : F)

#check dom
#check pow dom k
#check fiber dom k y

end

end SmoothDomain
