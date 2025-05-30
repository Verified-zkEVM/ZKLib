/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Least Authority
-/

import ArkLib.Data.MvPolynomial.Multilinear
import ArkLib.Data.CodingTheory.ConstraintReedSolomon
import ArkLib.Data.CodingTheory.ListDecodeability
import ArkLib.Data.CodingTheory.SmoothDomain

namespace OutOfDomSmpl

open ListDecodable MvPolynomial NNReal ReedSolomon SmoothDomain
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
         {ι : Finset F}


lemma agreement_randompoint_rs {f : ι → F} {k m s : ℕ} {domain : ι ↪ F} [Smooth domain k] :
  ∀ {r : Fin s → Fin m → F} (δ : ℝ≥0) (hδLe : δ ≤ 1), ∃ u u' : smoothCode F ι domain k m,
    u.val ≠ u'.val ∧
    u.val ∈ relHammingBall ↑(smoothCode F ι domain k m) f δ ∧
    u'.val ∈ relHammingBall ↑(smoothCode F ι domain k m) f δ ∧
    ∀ i : Fin s, (mVdecode u).eval (r i) = (mVdecode u').eval (r i)
    := by sorry

lemma agreement_randompoint_crs
  {f : ι → F} {k m s : ℕ} {domain : ι ↪ F} [Smooth domain k] :
  ∀ (r : Fin s → Fin m → F) (δ : ℝ≥0) (hδLe : δ ≤ 1),
    ∃ σ : Fin s → F,
      let w : Fin s → MvPolynomial (Fin (m + 1)) F :=
        fun i => MvPolynomial.X (Fin.last (m)) * rename Fin.castSucc (eqPolynomial (r i))
      let multiCRSCode := multiConstraintCode F ι domain k m s w σ
      let listHamming : Set (ι → F) := relHammingBall ↑multiCRSCode f δ
      ∃ g : ι → F, g ∈ listHamming
  := by sorry







-- lemma agreement_randompoint_crsc

end OutOfDomSmpl
