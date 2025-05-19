/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Least Authority
-/

import ArkLib.ProofSystem.Whir.ProximityGen
import ArkLib.Data.CodingTheory.FieldReedSolomon

namespace RSGenerator

open ReedSolomon ProximityGenerator

/-! Reed Solomon codes (over fields ?) have proximity generators -/

/-- `Fin l → F: α ↦ (1, α, α², … , α^(l-1))` -/
def rSSmpl
  {F : Type*} [Field F]
  (l : ℕ)
  (x : F) : Fin l → F := fun i => x ^ (i : ℕ)

noncomputable def rSGenerator
  {F : Type*} [Field F] [Fintype F] [DecidableEq F]
  {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
  (domain : ι ↪ F)
  (deg l : ℕ)
  : Generator (code F ι domain deg) l where
    Smpl  := rSSmpl l
    BStar := Real.sqrt (mockRate deg ι )
    err   := fun δ => ENNReal.ofReal (
      if δ ≤ (1 - (mockRate deg ι)) / 2 then
        ((deg - 1) * 2^deg) / ((mockRate deg ι) * Fintype.card F )
      else
        let min_val := min (1 - (Real.sqrt (mockRate deg ι)) - δ )
                                           ((Real.sqrt (mockRate deg ι)) / 20)
        ((deg - 1) * (2^deg)^2) / ((Fintype.card F) * (2 * min_val)^7)
      )
lemma proximity_gap
  (F : Type*) [Field F] [Fintype F] [DecidableEq F]
  (ι : Type*) [Fintype ι] [DecidableEq ι] [Nonempty ι]
  (domain : ι ↪ F)
  (deg l : ℕ) : isProximityGenerator (rSGenerator domain deg l) := sorry

end RSGenerator
