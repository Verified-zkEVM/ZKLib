/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Least Authority
-/

import ArkLib.Data.CodingTheory.SmoothReedSolomon
import ArkLib.Data.CodingTheory.RelativeHammingDistance
import ArkLib.Data.Probability.Notation
import ArkLib.ProofSystem.Whir.ProximityGen


namespace CorrelatedAgreement

open NNReal Generator ReedSolomon SmoothDomain
variable  {F : Type*} [Field F] [Fintype F] [DecidableEq F]
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

/-- Definition 4.9
  Let `C` be a linear code, then Gen is a proximity generator with mutual correlated agreement
  if for `l` functions `fᵢ : ι → F` and distance `δ`, `proximityCondition(r)` is true. -/
noncomputable def proximityGenMCA (Gen : ProximityGenerator ι F)
  (BStar : ℝ≥0) (errStar : ℝ≥0 → ℝ≥0) :=
    ∀ (f : Fin Gen.l → ι → F) (δ : ℝ≥0) (_hδ : δ < 1 - BStar),
    Pr_{r ← F} [ (proximityCondition f δ Gen.GenFun Gen.C) r ] > errStar δ

/--Lemma 4.10
  Let `C` be a linear code with minimum distance `δ_C`, `Gen` be a proximity generator for C
  with parameters `B` and `err`, then Gen has mutual correlated agreement with proximity bound with
  `BStar = min {1 - δ_C/2, B}` and `errStar = err`. -/
lemma mutual_corr_agreement (Gen : ProximityGenerator ι F) (BStar : ℝ≥0) (errStar : ℝ≥0 → ℝ≥0)
  (h: proximityGenMCA Gen BStar errStar) (C : Set (ι → F)) (hC : C = Gen.C) :
  BStar < min (1 - (δᵣ C) / 2 : ℝ) Gen.B
  ∧
  errStar = Gen.err := by sorry

/--Corollary 4.11
  Let `rsC` be a (smooth) ReedSolomon Code with rate `ρ`, then the function
  `Gen(l,α)={1,α,..,α ^ l-1}` is a proximity generator for Gen with mutual
  correlated agreement with
    BStar = (1+ρ) / 2
    errStar = (l-1)•2^m / ρ•|F|.

  function `Gen(l,α)={1,α,..,α ^ l-1}`-/
noncomputable def genₐ (α : F) (l : ℕ) : F → Fin l → F :=
  fun _ j => α ^ (j : ℕ)

/--the proximity generator `Genₐ` for smooth ReedSolomon codes wrt function
`Gen(l,α)={1,α,..,α ^ l-1}`-/
noncomputable def ProximityGeneratorₐ
  (ι : Finset F) [Nonempty ι] (Gen : ProximityGenerator ι F) (α : F)
  (domain : ι ↪ F) (m : ℕ) (k : ℕ) [Smooth domain k] :
  ProximityGenerator ι F :=
  {
    C := smoothCode F ι domain k m,
    l := Gen.l,
    GenFun := genₐ α Gen.l,
    B := Gen.B,
    err := Gen.err,
    proximity := by
      intro f δ hδ hprob
      sorry
  }
/--Corollary 4.11
  Let `C` be a smooth ReedSolomon code with rate `ρ`, then `Genₐ` is the proximity generator with
  mutual correlated agreement with bounds
    BStar = (1-ρ) / 2
    errStar = (l-1)•2^m / ρ•|F|. -/
lemma mutual_corr_agreement_rsc (ι : Finset F) [Nonempty ι] (Gen Genₐ: ProximityGenerator ι F)
  (α : F) (domain : ι ↪ F) (m k : ℕ) [Smooth domain k] (BStar ρ : ℝ≥0) (errStar : ℝ≥0 → ℝ≥0)
  (hGen : Genₐ = ProximityGeneratorₐ ι Gen α domain m k)
  (h : proximityGenMCA Genₐ BStar errStar)
  (hrate : ρ = (2^m : ℝ≥0) / (Fintype.card ι)) :
  BStar = (1 - ρ) / 2 ∧
  errStar = fun _ => (Genₐ.l - 1) • 2^m / ρ • (Fintype.card F : ℝ≥0)
  := by sorry
