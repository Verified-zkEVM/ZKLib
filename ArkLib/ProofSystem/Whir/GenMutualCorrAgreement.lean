/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Least Authority
-/

import ArkLib.Data.CodingTheory.ListDecodeability
import ArkLib.Data.CodingTheory.InterleavedCodes
import ArkLib.Data.CodingTheory.SmoothReedSolomon
import ArkLib.Data.CodingTheory.RelativeHammingDistance
import ArkLib.Data.Probability.NotationSingleSampl
import ArkLib.ProofSystem.Whir.ProximityGen

namespace CorrelatedAgreement

open NNReal Generator ReedSolomon SmoothDomain InterleavedCodes
variable  {F : Type*} [Field F] [Fintype F] [DecidableEq F]
          {ι : Type*} [Fintype ι] [Nonempty ι]

/-- For `l` functions `fᵢ : ι → 𝔽`, distance `δ`, generator function `GenFun: 𝔽 → 𝔽ˡ`and linear
    code `C` the predicate `proximityCondition(r)` is true, if ∃ S ⊆ [n], s.t.
    the following three conditions hold
      (i) |S| > (1-δ)•|ι| and
      (ii) ∃ u ∈ C, u(S) = ∑ j < l, rⱼ•fⱼ(S)
      (iii) ∃ i < l, ∀ u' ∈ C, u'(S) ≠ fᵢ(S) -/
def proximityCondition {l : ℕ} (f : Fin l → ι → F) (δ : ℝ≥0) (GenFun : F → Fin l → F)
  (C : LinearCode ι F): F → Prop
    | r =>
      ∃ S : Finset ι,
      (S.card : ℝ≥0) > (1-δ) * Fintype.card ι ∧
      ∃ u ∈ C, ∀ s ∈ S, u s = ∑ j : Fin l, GenFun r j • f j s ∧
      ∃ i : Fin l, ∀ u' ∈ C, ∀ s ∈ S, u' s ≠ f i s

/-- Definition 4.9
  Let `C` be a linear code, then Gen is a proximity generator with mutual correlated agreement,
  if for `l` functions `fᵢ : ι → F` and distance `δ < 1 - B(C,l)`,
  `Pr_{ r ← F } [ proximityCondition(r) ] > errStar(δ)`. -/
noncomputable def genMutualCorrAgreement (Gen : ProximityGenerator ι F)
  (BStar : ℝ≥0) (errStar : ℝ≥0 → ℝ≥0) :=
    ∀ (f : Fin Gen.l → ι → F) (δ : ℝ≥0) (_hδ : δ < 1 - (Gen.B Gen.C Gen.l)),
    Pr_{r ← F} [ (proximityCondition f δ Gen.GenFun Gen.C) r ] > errStar δ

/--Lemma 4.10
  Let `C` be a linear code with minimum distance `δ_C`, `Gen` be a proximity generator for C
  with parameters `B` and `err`, then Gen has mutual correlated agreement with proximity bounds
  `BStar = min {1 - δ_C/2, B}` and `errStar = err`. -/
lemma genMutualCorrAgreement_le_bound (Gen : ProximityGenerator ι F)
  (BStar : ℝ≥0) (errStar : ℝ≥0 → ℝ≥0)
  (C : Set (ι → F)) (hC : C = Gen.C)
  (h: genMutualCorrAgreement Gen BStar errStar) :
  BStar < min (1 - (δᵣ C) / 2 : ℝ) (Gen.B Gen.C Gen.l)
  ∧
  errStar = Gen.err Gen.C Gen.l := by sorry

/--Corollary 4.11
  Let `C` be a (smooth) ReedSolomon Code with rate `ρ`, then the function
  `Gen(l,α)={1,α,..,α ^ (l-1)}` is a proximity generator for Gen with mutual
  correlated agreement with proximity bounds
    BStar = (1+ρ) / 2
    errStar = (l-1)•2^m / ρ•|F|.

  function `Gen(l,α)={1,α,..,α ^ l-1}`-/
noncomputable def gen_α (α : F) (l : ℕ) : F → Fin l → F :=
  fun _ j => α ^ (j : ℕ)

/--the proximity generator for smooth ReedSolomon codes wrt function
  `Gen(l,α)={1,α,..,α ^ l-1}`-/
noncomputable def proximityGenerator_α
  [DecidableEq ι] (Gen : ProximityGenerator ι F) (α : F)
  (φ : ι ↪ F) (m : ℕ) [Smooth φ] :
  ProximityGenerator ι F :=
  {
    C := smoothCode F ι φ m,
    l := Gen.l,
    GenFun := gen_α α Gen.l,
    B := Gen.B,
    err := Gen.err,
    proximity := by
      intro f δ hδ hprob
      sorry
  }

/--Corollary 4.11
  Let `C` be a smooth ReedSolomon code with rate `ρ`, then `Gen_α` is the proximity generator with
  mutual correlated agreement with bounds
    BStar = (1-ρ) / 2
    errStar = (l-1)•2^m / ρ•|F|. -/
lemma genMutualCorrAgreement_rsc_le_bound
  [DecidableEq ι] (Gen Gen_α: ProximityGenerator ι F)
  (α : F) (φ : ι ↪ F) (m : ℕ) [Smooth φ]
  (BStar ρ : ℝ≥0) (errStar : ℝ≥0 → ℝ≥0)
  -- `Gen_α` is the proximity generator wrt function `Gen(l, α)`
  (hGen : Gen_α = proximityGenerator_α Gen α φ m)
  -- the proof that `Gen_α` is the proximity generator with mutual correlated agreement
  -- with proximity bound parameters BStar and errStar
  (h : genMutualCorrAgreement Gen_α BStar errStar)
  (hrate : ρ = (2^m : ℝ≥0) / (Fintype.card ι)) :
  BStar = (1 - ρ) / 2 ∧
  errStar = fun _ => (Gen_α.l - 1) • 2^m / ρ • (Fintype.card F : ℝ≥0)
  := by sorry


/--Conjecture 4.12
  The function `Gen(l,α)={1,α,..,α ^ l-1}` is a proximity generator with mutual correlated
  agreement for every (smooth) ReedSolomon code `C` with rate `ρ = 2^m / |ι|`.
  Below we state two conjectures for the parameters of the proximity bound.

  1. Upto Johnson bound: BStar = √ρ and
                         errStar = (l-1) • 2^2m / |F| • (2 • min {1 - √ρ - δ, √ρ/20}) ^ 7.-/
theorem genMutualCorrAgreement_le_johnsonBound
  [DecidableEq ι] (Gen Gen_α: ProximityGenerator ι F)
  (α : F) (φ : ι ↪ F) (m : ℕ) [Smooth φ]
  (BStar ρ δ: ℝ≥0) (errStar : ℝ≥0 → ℝ≥0)
  (hGen : Gen_α = proximityGenerator_α Gen α φ m)
  (h : genMutualCorrAgreement Gen_α BStar errStar)
  (hrate : ρ = (2^m : ℝ≥0) / (Fintype.card ι)) :
  let minval : ℝ≥0 := min (1 - NNReal.sqrt ρ - δ) (NNReal.sqrt ρ / 20)
  BStar = NNReal.sqrt ρ ∧
  ∀ {η : ℝ≥0} (hδPos : δ > 0) (hδLe : δ < 1 - NNReal.sqrt ρ - η),
  errStar = fun δ => (Gen_α.l - 1) • 2 ^ (2 • m) / (Fintype.card ι • (2 • minval)^7)
  := by sorry

/--2. Upto capacity: BStar = ρ and ∃ c₁,c₂,c₃ ∈ ℕ s.t. ∀ η > 0 and 0 < δ < 1 - ρ - η
      errStar = (l-1)^c₂ • d^c₂ / η^c₁ • ρ^(c₁+c₂) • |F|, where d = 2^m is the degree.-/
theorem genMutualCorrAgreement_le_capacity
  [DecidableEq ι] (Gen Genₐ: ProximityGenerator ι F)
  (α : F) (domain : ι ↪ F) (m : ℕ) [Smooth domain]
  (BStar ρ δ: ℝ≥0) (errStar : ℝ≥0 → ℝ≥0)
  (hGen : Genₐ = proximityGenerator_α Gen α domain m)
  (h : genMutualCorrAgreement Genₐ BStar errStar)
  (hrate : ρ = (2^m : ℝ≥0) / (Fintype.card ι)) :
  BStar = ρ ∧
  ∃ (c₁ c₂ c₃ : ℕ), ∀ {η : ℝ≥0} (hδPos : δ > 0) (hδLe : δ < 1 - ρ - η),
  errStar = fun δ => (Genₐ.l - 1)^c₂ • (2^m)^c₂ / (η^c₁ • ρ^(c₁+c₂) • (Fintype.card ι : ℝ≥0))
  := by sorry

/--For `l` functions `{f₁,..,fₗ}`, `IC` be the `l`-interleaved code from a linear code C,
  with `Gen` as a proximity generator with mutual correlated agreement,
  `proximityListDecodingCondition(r)` is true if,
  ∑ⱼ rⱼ•fⱼ = ∑ⱼ rⱼ•uⱼ, where {uᵢ,..uₗ} ∈ Λᵢ({f₁,..,fₗ}, IC, δ)-/
def proximityListDecodingCondition
  {ι : Type*} [Fintype ι] [Nonempty ι]
  (Gen : ProximityGenerator ι F) (δ : ℝ≥0)
  (fs us : Matrix (Fin Gen.l) ι F)
  (IC : InterleavedCode Gen.l ι F)
  (haveIC : IC = codeOfLinearCode Gen.l Gen.C)
  (haveList : us ∈ Λᵢ(fs, IC.MF, δ)) :
  F → Prop :=
  fun r =>
  let f_r := fun x => ∑ j, Gen.GenFun r j • fs j x
  let u_r := fun x => ∑ j, Gen.GenFun r j • us j x
  f_r ≠ u_r


/--lemma 4.13: Mutual correlated agreement preserves list decoding
  Let C be a linear code with minimum distance δ_c and `Gen` be a proximity generator
  with mutual correlated agreement for `C`.
  Then for every `{f₁,..,fₗ}` and `δ ∈ (0, min δ_c (1 - BStar))`,
  `Pr_{ r ← F} [ proximityListDecodingCondition(r) ] > errStar(δ)`. -/
lemma mutualCorrAgreement_list_decoding
  {ι : Type*} [Fintype ι] [Nonempty ι]
  (Gen : ProximityGenerator ι F) (δ BStar : ℝ≥0) (errStar : ℝ≥0 → ℝ≥0)
  (fs us : Matrix (Fin Gen.l) ι F)
  (IC : InterleavedCode Gen.l ι F)
  (haveIC : IC = codeOfLinearCode Gen.l Gen.C)
  (hGen : genMutualCorrAgreement Gen BStar errStar)
  (C : Set (ι → F)) (hC : C = Gen.C) :
  ∀ {fs : Matrix (Fin Gen.l) ι F} (haveList : us ∈ Λᵢ(fs, IC.MF, δ))
  (hδPos : δ > 0) (hδLt : δ < min (δᵣ C : ℝ) (1 - BStar)),
    Pr_{r ← F} [ proximityListDecodingCondition Gen δ fs us IC haveIC haveList r] ≤ errStar δ
    := by sorry

end CorrelatedAgreement
