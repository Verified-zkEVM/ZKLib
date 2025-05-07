/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Least Authority
-/

import Mathlib.Data.Real.Basic
import Mathlib.InformationTheory.Hamming

def fractionalHammingDist
  {α β : Type*} [Fintype α] [DecidableEq β]
  (f g : α → β) : ℚ := (hammingDist f g : ℚ) / Fintype.card α

/-- The fractional Hamming distance between a function f : α → β
and a nonempty finite set of functions S ⊆ (α → β) is defined as
∆(f, S) := min_{h ∈ S} ∆(f, h) -/
def fractionalHammingDistSet
  {α β : Type*} [Fintype α] [DecidableEq β]
  (f : α → β) (S : Finset (α → β))
  (h_nonempty : S.Nonempty) : ℚ :=
    (S.inf' h_nonempty (fun g ↦ (hammingDist f g)) : ℚ) / Fintype.card α
