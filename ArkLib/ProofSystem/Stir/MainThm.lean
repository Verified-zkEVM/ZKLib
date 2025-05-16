/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Least Authority
-/

import ArkLib.OracleReduction.VectorIOR
import ArkLib.ProofSystem.Stir.ToCodingTheory.ProximityBound
import ArkLib.ProofSystem.Stir.ToCodingTheory.ReedSolomonCodes
import ArkLib.ProofSystem.Stir.ToCodingTheory.SmoothDom

open Finset
open scoped BigOperators NNReal


namespace VectorIOP

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **Per‑round protocol parameters.**
For a fixed depth `M`, the reduction runs `M + 1` rounds.  In round
`i ∈ {0,…,M}` we fold by a factor `kᵢ`, evaluate on the point set
`Lᵢ ⊆ F`, and repeat certain proximity checks `tᵢ` times. -/
structure Params (F : Type*) [Field F] [Fintype F] [DecidableEq F]
    (M : ℕ) where
  k : Fin (M + 1) → ℕ
  L : Fin (M + 1) → Finset F
  t : Fin (M + 1) → ℕ

/-- **Degree after `i` folds.**
The starting degree is `d`; every fold divides it by `kⱼ (j<i)` to obtain `dᵢ`.
We assume divisibility so the integer division is exact. -/
def degreeᵢ {M : ℕ} (d : ℕ) (P : Params F M) (i : Fin (M + 1)) : ℕ :=
  d / ∏ j : Fin i, P.k (Fin.castLT j (Nat.lt_trans j.isLt i.isLt))

/-- **`Rateᵢ= degreeᵢ/|Lᵢ|`** of the Reed–Solomon code used in round `i`.
A real number because most analytic bounds live in `ℝ`. -/
noncomputable def rateᵢ {M : ℕ} (d : ℕ) (P : Params F M)
    (i : Fin (M + 1)) : ℝ :=
  (degreeᵢ d P i : ℝ) / ((P.L i).card : ℝ)

/-- Distance and list‑size targets per round. -/
structure Distances (M : ℕ) where
  δ : Fin (M + 1) → ℝ
  l : Fin (M + 1) → ℕ

/-- **Family of Reed–Solomon codes** actually expected by the verifier.
The index `i` says *which* round we refer to; all codes are computed from
the same source polynomial `f`. -/
structure Code
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    {d : ℕ} {M : ℕ} {P : Params F M} (i : Fin (M + 1)) where
  codeᵢ : (j : Fin (M + 1)) → ReedSolomonCode F (P.L j) (degreeᵢ d P j)

/-- Predecessor inside `Fin (n+1)` (requires `i ≠ 0`). -/
def predFin {n : ℕ} (i : Fin (n + 1)) (h : i.val ≠ 0) : Fin (n + 1) :=
  ⟨Nat.pred i.val, by
    have hpred : Nat.pred i.val < i.val := Nat.pred_lt h
    exact Nat.lt_trans hpred i.isLt⟩

open OracleComp OracleSpec ProtocolSpec

section STIR
variable {n : ℕ} {ι : Type}

structure Statement
  (F : Type)[Field F][Fintype F][DecidableEq F]
  (L : Finset F)(d : ℕ) where
  eval : L -> F


@[reducible]
def OStmtOut (F : Type) (L : Finset F) (ιₛ : Type) : ιₛ → Type :=
  fun _ => L → F

instance instStirOraclePerIndex
  {F : Type} [Field F] [Fintype F] [DecidableEq F]
  {L : Finset F} {ιₛ : Type} :
  ∀ _ : ιₛ, OracleInterface (L → F) :=
  fun _ => {
    Query := {x // x ∈ L}
    Response := F
    oracle := fun f q => f q
  }

def stirRelation
  {F : Type} [Field F] [Fintype F] [DecidableEq F]
  {L : Finset F} {d : ℕ} {ιₛ : Type}
  (C : ReedSolomonCode F L d) (δ : ℝ)
  : (Statement F L d × ∀ _ : ιₛ, L → F) → Unit → Prop :=
  fun ⟨stmt, _oracles⟩ _ =>
    ∀ c ∈ C.code, fractionalHammingDist stmt.eval c ≥ δ



/-- **STIR main theorem** -/
theorem STIR
  {F : Type} [Field F] [Fintype F] [DecidableEq F] [VCVCompatible F]
  {L : Finset F} (hsmooth : smoothDom L)
  {d : ℕ} (hd : ∃ m, d = 2 ^ m)
  (C : ReedSolomonCode F L d) (secpar : ℕ)
  (δ : ℝ) (hδ0 : 0 < δ) (hδub : δ < 1 - 1.05 * Real.sqrt (d / L.card))
  (k : ℕ) (hk : ∃ m, k = 2 ^ m) (hk4 : 4 ≤ k)
  (hF : Fintype.card F ≥
        secpar * 2 ^ secpar * d^2 * L.card^(7/2) /
        Real.log (1 / C.rate))
  (vPSpec : ProtocolSpec.VectorSpec n)
  (oSpec : OracleSpec ι) [oSpec.FiniteRange]
  {ιₛ : Type}
  [OracleInterface (L → F)]
  (ε_rbr : vPSpec.ChallengeIdx → ℝ≥0) :
  ∃ π : VectorIOP vPSpec F oSpec (Statement F L d) Unit (OStmtOut F L ιₛ),
    IsSecureWithGap (stirRelation C 0)
                    (stirRelation C δ)
                    ε_rbr π :=
by
  sorry

end STIR


section RBR
open Finset BigOperators
variable {n : ℕ} {ι : Type}


/-- **Round-by-round soundness of the STIR IOPP**-/
theorem stir_rbr_soundness
    {F : Type} [Field F] [Fintype F] [DecidableEq F] [VCVCompatible F]
    {d : ℕ}{L : Finset F} (hsmooth : smoothDom L)
    {M : ℕ} (P : Params F M) {f : F → F}
    {i : Fin (M + 1)} (C : Code (P := P) (d := d) i) (s : ℕ)
    (dist : Distances M)
    (h_not_code :
      (fun x : ↥(P.L 0) ↦ f x) ∉ (C.codeᵢ 0).code)
    (hδ₀ :
      0 < dist.δ 0 ∧
      dist.δ 0 ≤
        fractionalHammingDistSet (fun x : ↥(P.L i) ↦ f x)
          (C.codeᵢ i).code (C.codeᵢ i).nonempty ∧
      dist.δ 0 < (1 - Bstar (rateᵢ (d := d) (P := P) 0)))
    (hδᵢ :
      ∀ {j : Fin (M + 1)}, j ≠ 0 →
        0 < dist.δ j ∧
        dist.δ j <
          (1 - rateᵢ (d := d) (P := P) j - 1 / (P.L j).card) ∧
        dist.δ j < (1 - Bstar (rateᵢ (d := d) (P := P) j)))
    (h_list :
      ∀ {j : Fin (M + 1)}, j ≠ 0 →
        (C.codeᵢ j).toLinearCode.toErrCorrCode.listDecodable
          (dist.δ j) (dist.l j))
    (vPSpec : ProtocolSpec.VectorSpec n)
    -- [∀ j, VCVCompatible (vPSpec.ChallengeIdx j)][∀ j, OracleInterface (vPSpec.MessageIdx j)]
    (oSpec : OracleSpec ι) [oSpec.FiniteRange]
    {ιₛ : Type} [OracleInterface (L → F)]
    (ε_fold : ℝ≥0) (ε_out : Fin (M + 1) → ℝ≥0)
    (ε_shift : Fin (M + 1) → ℝ≥0) (ε_fin : ℝ≥0)
    (ε_sound : ℝ≥0) (ε_rbr : vPSpec.ChallengeIdx → ℝ≥0) :
    ∃ π : VectorIOP vPSpec F oSpec (Statement F L d) Unit (OStmtOut F L ιₛ),
      ε_fold ≤ (err' F ((degreeᵢ d P 0) / P.k 0) (rateᵢ d P 0)
                 (dist.δ 0) (P.k 0)).toReal ∧
      (∀ {j : Fin (M + 1)} (hⱼ : j.val ≠ 0),
        ε_out j ≤
          ((dist.l j : ℝ) ^ 2 / 2) *
            ((degreeᵢ d P j : ℝ) /
              (Fintype.card F - (P.L j).card)) ^ s ∧
        let jPred := predFin j hⱼ;
        ε_shift j ≤
          (1 - dist.δ jPred) ^ (P.t jPred) +
          (err' F (degreeᵢ d P j) (rateᵢ d P j)
            (dist.δ j) (P.t jPred) + s).toReal +
          (err' F ((degreeᵢ d P j) / P.k j)
            (rateᵢ d P j) (dist.δ j) (P.k j)).toReal) ∧
        ε_fin ≤ (1 - dist.δ M) ^ (P.t M) :=
by
  sorry

end RBR

end VectorIOP
