/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Least Authority
-/

import ArkLib.ProofSystem.Stir.ToCodingTheory.ReedSolomonCodes

import Mathlib.Data.Real.Sqrt

lemma johnson_bound
  {F : Type*} [Field F] [Fintype F] [DecidableEq F]
  {L : Finset F}
  {d : ℕ}
  (C : ReedSolomonCode F L d)
  (η : ℝ)
  (hη : 0 < η ∧ η < 1 - Real.sqrt C.rate) :
    C.toLinearCode.toErrCorrCode.listDecodable
    (1 - Real.sqrt C.rate - η) (1 / (2 *  η * Real.sqrt C.rate)) := by sorry
