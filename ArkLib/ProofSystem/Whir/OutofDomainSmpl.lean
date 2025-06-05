/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Least Authority
-/

import ArkLib.Data.MvPolynomial.Multilinear
import ArkLib.Data.CodingTheory.ConstraintReedSolomon
import ArkLib.Data.CodingTheory.ListDecodeability
import ArkLib.Data.Probability.NotationSingleSampl

namespace OutOfDomSmpl

open ListDecodable MvPolynomial NNReal ReedSolomon SmoothDomain
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
         {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma crs_equiv_rs_randpompt_agreement
  {f : ι → F} {m s : ℕ} {φ : ι ↪ F} [Smooth φ] :
  ∀ (r : Fin s → Fin m → F) (δ : ℝ≥0) (hδLe : δ ≤ 1),
    (∃ u u' : smoothCode F ι φ m,
      u.val ≠ u'.val ∧
      u.val ∈ relHammingBall ↑(smoothCode F ι φ m) f δ ∧
      u'.val ∈ relHammingBall ↑(smoothCode F ι φ m) f δ ∧
      ∀ i : Fin s, (mVdecode u).eval (r i) = (mVdecode u').eval (r i))
    ↔
    (∃ σ : Fin s → F,
      let w : Fin s → MvPolynomial (Fin (m + 1)) F :=
        fun i => MvPolynomial.X (Fin.last m) * rename Fin.castSucc (eqPolynomial (r i))
      let multiCRSCode := multiConstraintCode F ι φ m s w σ
      ∃ g : ι → F, g ∈ relHammingBall ↑multiCRSCode f δ)
  := by sorry

lemma out_of_domain_sampling_crs_eq_rs
    {f : ι → F} {m s : ℕ} {φ : ι ↪ F} [Smooth φ]
    {GenFun : F → Fin s → F} (δ : ℝ≥0) (hδLe : δ ≤ 1) :
    Pr_{ r ← F }
      [ (∃ σ : Fin s → F,
        ∀ i : Fin s,
          let ri := GenFun r i
          let rVec := fun j : Fin m => ri ^ (2^(j : ℕ))
        let w : Fin s → MvPolynomial (Fin (m + 1)) F :=
          fun i => MvPolynomial.X (Fin.last m) * rename Fin.castSucc (eqPolynomial (rVec))
        let multiCRSCode := multiConstraintCode F ι φ m s w σ
        ∃ g : ι → F, g ∈ relHammingBall ↑multiCRSCode f δ)]
    =
    Pr_{ r ← F }
      [ (∃ u u' : smoothCode F ι φ m,
        u.val ≠ u'.val ∧
        u.val ∈ relHammingBall ↑(smoothCode F ι φ m) f δ ∧
        u'.val ∈ relHammingBall ↑(smoothCode F ι φ m) f δ ∧
        ∀ i : Fin s,
          let ri := GenFun r i
          let rVec := fun j : Fin m => ri ^ (2^(j : ℕ))
          (mVdecode u).eval (rVec) = (mVdecode u').eval (rVec))] := by sorry

lemma out_of_domain_sampling_rs_le_bound
    {f : ι → F} {k m s : ℕ} {φ : ι ↪ F} [Smooth φ]
    {GenFun : F → Fin s → F} (δ l : ℝ≥0) (hδLe : δ ≤ 1)
    (C : Set (ι → F)) (hcode : C = smoothCode F ι φ m ∧ listDecodable C δ l) :
    Pr_{ r ← F }
      [ ∃ u u' : smoothCode F ι φ m,
        u.val ≠ u'.val ∧
        u.val ∈ relHammingBall ↑C f δ ∧
        u'.val ∈ relHammingBall ↑C f δ ∧
        ∀ i : Fin s,
          let ri := GenFun r i
          let rVec := fun j : Fin m => ri ^ (2^(j : ℕ))
          (mVdecode u).eval (rVec) = (mVdecode u').eval (rVec)
      ] ≤ l^2 / 2 • ((2^m) / Fintype.card F)^s := by sorry







-- lemma agreement_randompoint_crsc

end OutOfDomSmpl
