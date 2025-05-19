/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Least Authority
-/

import ArkLib.Data.CodingTheory.RelativeHammingDistance
import ArkLib.Data.Probability.Notation

import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Probability.Distributions.Uniform

structure Generator
  {F : Type*} [Semiring F]
  {ι : Type*} [Fintype ι]
  (C : LinearCode ι F)
  (l : ℕ) where
    Smpl   : F → (Fin l → F)
    BStar  : ℝ
    err    : {δ : ℝ // 0 < δ ∧ δ < 1 - BStar} → ENNReal


namespace ProximityGenerator

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
         {ι : Type*} [Fintype ι] [DecidableEq ι]


def proximity_property
  [Nonempty ι]
  {l : ℕ}
  {C : LinearCode ι F}
  (G : Generator C l)
  (f : Fin l → ι → F)
  (δ : {δ // 0 < δ ∧ δ < 1 - G.BStar})
  : F → Prop
    | r => δᵣ(fun x => ∑ j : Fin l, (G.Smpl r) j • f j x, C ) ≤ δ.val

/- A generator `G`is a `proximity generator` if for every list of functions
   `f₁,…,fₗ : ι → F` and every admissible radius `δ` the following holds true:

   if a linear combination `\sum rᵢ·fᵢ` with random coefficients `rᵢ` drawn according
   to `G.Smpl` lands within fractional Hamming distance `δ` of the code `C`
   more frequently than the error bound `G.err δ`, then each function `fᵢ` coincides with
   some codeword on at least a `(1 - δ)` fraction of the evaluaton points.-/
def isProximityGenerator
  [Nonempty ι]
  {l : ℕ} {C : LinearCode ι F}
  (G : Generator C l)
  : Prop :=
  ∀ (f : Fin l → ι → F)
    (δ : {δ : ℝ // 0 < δ ∧ δ < 1 - G.BStar}),
    Pr_{r ← F}[ (proximity_property G f δ) r ] > G.err δ →
    ∃ S : Finset ι,
      S.card ≥ (1 - (δ : ℝ)) * (Fintype.card ι) ∧
      ∀ i : Fin l, ∃ u : C, ∀ x ∈ S, f i x = u.val x

end ProximityGenerator
