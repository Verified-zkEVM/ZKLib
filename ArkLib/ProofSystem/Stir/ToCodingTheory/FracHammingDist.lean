/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Least Authority
-/

import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Data.Real.Basic
import Mathlib.InformationTheory.Hamming

/-- The fractional Hamming distance between two functions f, g : L → F is defined as ∆(f, g) := (number of positions at which f and g differ) / |L| -/
def fractionalHammingDist {F : Type*} {L : Finset F} [DecidableEq F]
  (f g : ↑L → F) : ℚ := (hammingDist f g : ℚ) / Fintype.card L

/-- The fractional Hamming distance between a function f : L → F and a nonempty finite set of functions S ⊆ (L → F) is defined as ∆(f, S) := min_{h ∈ S} ∆(f, h) -/
def fractionalHammingDistSet {F : Type*} {L : Finset F} [DecidableEq F]
  (f : ↑L → F)
  (S : Finset (↑L → F))
  (h_nonempty : S.Nonempty) : ℚ := (S.inf' h_nonempty (hammingDist f ·) : ℚ) / Fintype.card L
