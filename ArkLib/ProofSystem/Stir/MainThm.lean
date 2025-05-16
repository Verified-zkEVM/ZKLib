/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Least Authority
-/

import ArkLib.ProofSystem.Stir.IOPP
import ArkLib.ProofSystem.Stir.ToCodingTheory.ProximityBound
import ArkLib.ProofSystem.Stir.ToCodingTheory.ReedSolomonCodes
import ArkLib.ProofSystem.Stir.ToCodingTheory.SmoothDom

open Finset
open scoped BigOperators NNReal


namespace Reduction

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

/-- Max of `ε_fold`, `ε_fin`, all `ε_out` and `ε_shift`.  Uses `max'` so
no `OrderBot ℝ≥0` instance is required. -/
noncomputable def maxErrors {M : ℕ}
    (ε_fold ε_fin : ℝ≥0) (ε_out ε_shift : Fin (M + 1) → ℝ≥0) : ℝ≥0 :=
  (insert ε_fold
    (insert ε_fin
      ((univ : Finset (Fin (M + 1))).image ε_out ∪
       (univ : Finset (Fin (M + 1))).image ε_shift))).max' (by simp)


open OracleComp OracleSpec ProtocolSpec

section STIR
variable {n : ℕ} {ι : Type}

/-- **STIR main theorem** -/
theorem STIR
  {F : Type*} [Field F] [Fintype F] [DecidableEq F]
  {L : Finset F} (hsmooth : smoothDom L)
  {d : ℕ} (hd : ∃ m, d = 2 ^ m)
  (C : ReedSolomonCode F L d) (secpar : ℕ)
  (δ : ℝ) (hδ0 : 0 < δ) (hδub : δ < 1 - 1.05 * Real.sqrt (d / L.card))
  (k : ℕ) (hk : ∃ m, k = 2 ^ m) (hk4 : 4 ≤ k)
  (hF : Fintype.card F ≥
        secpar * 2 ^ secpar * d^2 * L.card^(7/2) /
        Real.log (1 / C.rate))
  (pSpec : ProtocolSpec n) (oSpec : OracleSpec ι)
  [∀ i, VCVCompatible (pSpec.Challenge i)] [oSpec.FiniteRange]
  [∀ i, ToOracle (pSpec.Message i)]
  (StmtIn WitIn : Type)
  {ιₛₒ : Type} (OStmtOut : ιₛₒ → Type) [∀ i, ToOracle (OStmtOut i)]
  (ε_sound : ℝ≥0) (ε_rbr : pSpec.ChallengeIndex → ℝ≥0) :
  ∃ π : IOPP pSpec oSpec StmtIn WitIn OStmtOut ε_sound ε_rbr,
    ε_rbr < 1 / 2 ^ secpar :=
by
  sorry
end STIR


section RBR
open Finset BigOperators
variable {n : ℕ} {ι : Type}
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {d : ℕ}

/-- **Round-by-round soundness of the STIR IOPP**-/
theorem stir_rbr_soundness
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
    (pSpec : ProtocolSpec n) (oSpec : OracleSpec ι)
    [∀ j, VCVCompatible (pSpec.Challenge j)] [oSpec.FiniteRange]
    [∀ j, ToOracle (pSpec.Message j)]
    (StmtIn WitIn : Type)
    {ιₛₒ : Type} (OStmtOut : ιₛₒ → Type) [∀ j, ToOracle (OStmtOut j)]
    (ε_fold : ℝ≥0) (ε_out : Fin (M + 1) → ℝ≥0)
    (ε_shift : Fin (M + 1) → ℝ≥0) (ε_fin : ℝ≥0)
    (ε_sound : ℝ≥0) (ε_rbr : pSpec.ChallengeIndex → ℝ≥0) :
    ∃ π : IOPP pSpec oSpec StmtIn WitIn OStmtOut ε_sound ε_rbr,
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
        ε_fin ≤ (1 - dist.δ M) ^ (P.t M) ∧
        ε_rbr = fun _ => maxErrors ε_fold ε_fin ε_out ε_shift :=
by
  sorry

end RBR

end Reduction
