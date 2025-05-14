/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Least Authority
-/

import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Data.Fintype.Units
import Mathlib.Data.Fintype.Card

namespace SmoothDomain

variable {F: Type*} [Semiring F]
         (L : Finset F)

/-- A set L ⊆ R is `smooth` if `|L| = 2^k` for some `k` and there exists a subgroup `H`
    in the group of units `Rˣ` and an invertible field element `a` such that `L = a • H` -/
def smoothDom: Prop :=
  ∃ H : Subgroup (Units F), ∃ a : Units F, ∃ k : ℕ,
    -- f : α → β, S : Set α  then  f '' S means {y : β ∣ ∃x∈S,y=f(x) }
    (L : Set F) = (fun h : Units F ↦ (a : F) * h) '' (H : Set (Units F))  ∧ -- L = a • H
    L.card = 2 ^ k

/-- The `k`-th power of `L`,  `L^k := { x^k | x ∈ L }` -/
def powDom [DecidableEq F] (k : ℕ) : Finset F :=
  L.image fun x : F => x ^ k

/-- The fiber `f⁻¹(y)` for the surjection `f : L → L^k, x → x^k` and `y ∈ L^k` -/
def powFiber
  [DecidableEq F] (k : ℕ) (y : powDom L k) : Finset F :=
  L.filter (fun x => x^ k = y)

end SmoothDomain
