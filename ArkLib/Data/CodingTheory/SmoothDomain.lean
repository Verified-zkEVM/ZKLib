/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Least Authority
-/

import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Data.Fintype.Units
import Mathlib.Data.Fintype.Card

namespace SmoothDomain

variable {F: Type*} [Semiring F] {ι : Finset F}

/-- A domain `ι ↪ F` is `smooth`, if `ι ⊆ F`, `|ι| = 2^k` for some `k` and
    there exists a subgroup `H` in the group of units `Rˣ`
    and an invertible element `a ∈ R` such that `ι = a • H` -/
class Smooth
  (domain : ι ↪ F) -- For ι : Finset F, this is the identity embedding
  (k : ℕ ) where
    H           : Subgroup (Units F)
    a           : Units F
    h_coset     : (ι : Set F)
                  -- f : α → β, S : Set α  then  f '' S means {y : β ∣ ∃x∈S,y=f(x) }
                  = (fun h : Units F => (a : F) * (h : F)) '' (H : Set (Units F)) -- L = a • H
    h_card_pow2 : ι.card = 2 ^ k

/-- The `k`-th power of `ι ⊆ F`, i.e the set `ιᵏ := {xᵏ | x ∈ ι }. -/
abbrev indexPow [DecidableEq F] (ι : Finset F) (k : ℕ) : Finset F :=
  ι.image (fun x => x ^ k)

/-- The k-th power domain `ιᵏ ↪ F` for a given domain `ι ↪ F`. -/
def pow [DecidableEq F]
  (_domain : ι ↪ F)
  (k : ℕ) : indexPow ι k ↪ F :=
    Function.Embedding.subtype fun y => y ∈ indexPow ι k

/-- The fiber `f⁻¹(y)` for the surjection `f : ι → ιᵏ, x → xᵏ` and `y ∈ ιᵏ` -/
abbrev powFiber
  [DecidableEq F] (ι : Finset F) (k : ℕ) (y : indexPow ι k) : Finset F :=
  ι.filter (fun x => x^ k = y)

/-- The fiber domain `f⁻¹(y) ↪ F` for the surjection `f : ι → ιᵏ, x → xᵏ` and `y ∈ ιᵏ`. -/
def fiber [DecidableEq F]
  {k : ℕ}
  (_domainPow : indexPow ι k ↪ F )
  (y : indexPow ι k): powFiber ι k y ↪ F :=
    Function.Embedding.subtype fun z => z ∈ powFiber ι k y

section
--Test

variable {F : Type*} [Semiring F] [DecidableEq F] (ι₁ : Finset F) (dom : ι₁ ↪ F) (k : ℕ)
(y : indexPow ι₁ k)
#check dom
#check pow dom k
#check fiber (pow dom k) y

end

end SmoothDomain
