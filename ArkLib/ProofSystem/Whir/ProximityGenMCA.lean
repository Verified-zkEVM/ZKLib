/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Least Authority
-/

import ArkLib.Data.CodingTheory.RelativeHammingDistance
import ArkLib.Data.Probability.Notation
import ArkLib.ProofSystem.Whir.ProximityGen


namespace CorrelatedAgreement

open NNReal Generator
variable  {F : Type*} [Semiring F] [Fintype F] [DecidableEq F]
          {ι : Type*} [Fintype ι] [Nonempty ι]

/-- For `l` functions `fᵢ : ι → 𝔽`, distance `δ`, generator function `GenFun: 𝔽 → 𝔽ˡ`and linear
    code `C` the predicate `proximityCondition(r)` is true, if ∃ S ⊆ [n], s.t.
    the following three conditions hold
      (i) |S| > (1-δ)•n and
      (ii) ∃ u ∈ C, u(S) = ∑ j>l, rⱼ•fⱼ(S)
      (iii) ∃ i∈[l], ∀ u' ∈ C, u'(S) ≠ fᵢ(S) -/
def proximityCondition {l : ℕ} (f : Fin l → ι → F) (δ : ℝ≥0) (GenFun : F → Fin l → F)
  (C : LinearCode ι F): F → Prop
    | r =>
      ∃ S : Finset ι,
      (S.card : ℝ≥0) > (1-δ) • l ∧
      ∃ u ∈ C, ∀ s ∈ S, u s = ∑ j : Fin l, GenFun r j • f j s ∧
      ∃ i : Fin l, ∀ u' ∈ C, ∀ s ∈ S, u' s ≠ f i s

/-- Let `C` be a linear code, then Gen is a proximity generator with mutual correlated agreement
    if for `l` functions `fᵢ : ι → F` and distance `δ`, `proximityCondition(r)` is true.

    Definition 4.9 -/
noncomputable def proximityGenMCA (Gen : ProximityGenerator ι F)
  (BStar : ℝ≥0) (errStar : ℝ≥0 → ℝ≥0) :=
    ∀ (f : Fin Gen.l → ι → F) (δ : ℝ≥0) (_hδ : δ < 1 - BStar),
    Pr_{r ← F} [ (proximityCondition f δ Gen.GenFun Gen.C) r ] > errStar δ

/--Let `C` be a linear code with minimum distance `δ_C`, `Gen` be a proximity generator for C
   with parameters `B` and `err`, then Gen has mutual correlated agreement with proximity bound with
   `BStar = min {1 - δ_C/2, B}` and `errStar = err`.

   Lemma 4.10-/
lemma mutual_corr_agreement (Gen : ProximityGenerator ι F) (BStar : ℝ≥0) (errStar : ℝ≥0 → ℝ≥0)
  (h: proximityGenMCA Gen BStar errStar) (C : Set (ι → F)) (hC : C = Gen.C) :
  BStar < min (1 - (δᵣ C) / 2 : ℝ) Gen.B
  ∧
  errStar = Gen.err := by sorry
