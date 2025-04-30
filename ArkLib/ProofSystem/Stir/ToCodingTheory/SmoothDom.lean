/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Least Authority
-/

import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Data.Fintype.Units
import Mathlib.Data.Fintype.Card

/-- A set L ⊆ 𝔽 is `smooth` if `|L| = 2^k` for some `k` and there exists a subgroup `H` in `𝔽^⋆` and an invertible field element `a` such that `L = a • H` -/
def smoothDom {F : Type*} [Field F] [DecidableEq F] (L : Finset F) : Prop :=
  ∃ H : Subgroup (Units F), ∃ a : Units F, ∃ k : ℕ,
    -- f : α → β, S : Set α  then  f '' S means {y : β ∣ ∃x∈S,y=f(x) }
    (L : Set F) = (fun h : Units F ↦ (a : F) * h) '' (H : Set (Units F))  ∧ -- L = a • H
    L.card = 2 ^ k

/-- The `k`-th power of `L`,  `L^k := { x^k | x ∈ L }` -/
def powDom {F : Type*} [Field F] [DecidableEq F] (L : Finset F) (k : ℕ) : Finset F :=
  L.image fun x : F => x ^ k

/-- The fiber `f⁻¹(y)` for the surjection `f : L → L^k, x → x^k` and `y ∈ L^k` -/
def powFiber {F : Type*} [Field F] [DecidableEq F] (L : Finset F) (k : ℕ) (x : powDom L k) : Finset F :=
  L.filter (fun y => y ^ k = x)

/-- Restrict `f : L → F` to a subset `S ⊆ L`. -/
def restrictTo {F : Type*} [Field F] [DecidableEq F] (L : Finset F) (f : L → F) (S : Finset F) (hS : S ⊆ L) : (↑S → F) :=
  fun x => f ⟨x, hS x.2⟩
