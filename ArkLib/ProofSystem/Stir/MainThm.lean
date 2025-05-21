/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Least Authority
-/


import ArkLib.Data.CodingTheory.FieldReedSolomon
import ArkLib.Data.CodingTheory.ListDecodeability
import ArkLib.Data.CodingTheory.ProximityBound
import ArkLib.Data.CodingTheory.RelativeHammingDistance
import ArkLib.Data.CodingTheory.SmoothDomain
import ArkLib.OracleReduction.VectorIOR

open Finset ReedSolomon VectorIOP ListDecodable SmoothDomain
open scoped BigOperators NNReal


namespace StirIOP

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
         {ι : Finset F} {domain : ι ↪ F} {f : ι → F}

def toCode (LC : LinearCode ι F) : Code ι F := LC
/-- **Per‑round protocol parameters.**
For a fixed depth `M`, the reduction runs `M + 1` rounds.  In round
`i ∈ {0,…,M}` we fold by a factor `kᵢ`, evaluate on the point set
`Lᵢ ⊆ F`, and repeat certain proximity checks `tᵢ` times. -/
structure Params (F : Type*) (M : ℕ) where
  k : Fin (M + 1) → ℕ
  ι : Fin (M + 1) → Finset F
  t : Fin (M + 1) → ℕ

/-- **Degree after `i` folds.**
The starting degree is `d`; every fold divides it by `kⱼ (j<i)` to obtain `dᵢ`.
We assume divisibility so the integer division is exact. -/
def degreeᵢ {M : ℕ} (degree : ℕ) (P : Params F M) (i : Fin (M + 1)) : ℕ :=
  degree / ∏ j < i, (P.k j)

/-- **`Rateᵢ= degreeᵢ/|Lᵢ|`** of the Reed–Solomon code used in round `i`.
A real number because most analytic bounds live in `ℝ`. -/
noncomputable def rateᵢ {M : ℕ} (degree : ℕ) (P : Params F M)
    (i : Fin (M + 1)) : ℝ :=
  (degreeᵢ degree P i : ℝ) / ((P.ι i).card : ℝ)

/-- Distance and list‑size targets per round. -/
structure Distances (M : ℕ) where
  δ : Fin (M + 1) → ℚ
  l : Fin (M + 1) → ℚ

/-- **Family of Reed–Solomon codes** actually expected by the verifier.
The index `i` says *which* round we refer to; all codes are computed from
the same source polynomial `f`. -/
structure Code
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (d : ℕ) {M : ℕ} (P : Params F M) (i : Fin (M + 1)) where
  domainᵢ : (i: Fin (M+1)) → (P.ι i ↪ F)
  codeᵢ : (i : Fin (M + 1)) → code F (P.ι i) (domainᵢ i) (degreeᵢ d P i)

/-- Predecessor inside `Fin (n+1)` (requires `i ≠ 0`). -/
def predFin {n : ℕ} (i : Fin (n + 1)) (h : i.val ≠ 0) : Fin (n + 1) :=
  ⟨Nat.pred i.val, by
    have hpred : Nat.pred i.val < i.val := Nat.pred_lt h
    exact Nat.lt_trans hpred i.isLt⟩

open OracleComp OracleSpec ProtocolSpec

section STIR
variable {n : ℕ}

structure Statement
  (F : Type)[Field F][Fintype F][DecidableEq F]
  (ι : Finset F)(d : ℕ) where
  eval : ι -> F


@[reducible]
def OStmtOut (F : Type) (ι : Finset F) (ιₛ : Type) : ιₛ → Type :=
  fun _ => ι → F

instance instStirOraclePerIndex
  {F : Type} [Field F] [Fintype F] [DecidableEq F]
  {ι : Finset F} {ιₛ : Type} :
  ∀ _ : ιₛ, OracleInterface (ι → F) :=
  fun _ => {
    Query := {x // x ∈ ι}
    Response := F
    oracle := fun f q => f q
  }

def stirRelation
  {F : Type} [Field F] [Fintype F] [DecidableEq F]
  {ι : Finset F} [Nonempty ι] {degree : ℕ} {ιₛ : Type} (domain : ι ↪ F) (δ : ℝ)
  : (Statement F ι degree × ∀ _ : ιₛ, ι → F) → Unit → Prop :=
  let C := code F ι domain degree
  fun ⟨stmt, _oracles⟩ _ =>
    δᵣ(stmt.eval, ↑C) ≥ δ



/-- **STIR main theorem** -/
theorem STIR
  {F : Type} [Field F] [Fintype F] [DecidableEq F] [VCVCompatible F]
  {ι : Finset F} [Nonempty ι]
  {domain : ι ↪ F} {degree : ℕ} (hd : ∃ m, degree = 2 ^ m) (secpar : ℕ)
  (δ : ℝ) (hδ0 : 0 < δ) (hδub : δ < 1 - 1.05 * Real.sqrt (degree / ι.card))
  (k : ℕ) (hk : ∃ m, k = 2 ^ m) (hk4 : 4 ≤ k)
  [hsmooth : Smooth domain k]-- ι is a smooth domain
  (hF : Fintype.card F ≥
        secpar * 2 ^ secpar * degree^2 * ι.card^(7/2) /
        Real.log (1 / rate degree ι))
  (vPSpec : ProtocolSpec.VectorSpec n)
  (oSpec : OracleSpec ι) [oSpec.FiniteRange]
  {ιₛ : Type}
  [OracleInterface (ι → F)]
  (ε_rbr : vPSpec.ChallengeIdx → ℝ≥0) :
  ∃ π : VectorIOP vPSpec F oSpec (Statement F ι degree) Unit (OStmtOut F ι ιₛ),
    IsSecureWithGap (stirRelation domain 0)
                    (stirRelation domain δ)
                    ε_rbr π :=
by
  sorry

end STIR


section RBR
open Finset BigOperators
variable {n : ℕ}


/-- **Round-by-round soundness of the STIR IOPP**-/
theorem stir_rbr_soundness
    {F : Type} [Field F] [Fintype F] [DecidableEq F] [VCVCompatible F]
    {d k : ℕ} {ι : Finset F} [hsmooth : Smooth domain k] -- ι is a smooth domain
    {M : ℕ} (P : Params F M) {f₀ : (P.ι 0) → F}
    {h_nonempty: ∀ i : Fin (M + 1), Nonempty (P.ι i)}
    {i : Fin (M + 1)} (C : Code d P i) (s : ℕ)
    (dist : Distances M)
    (h_not_code : f₀ ∉ toCode (toLinearCode ↑(C.codeᵢ 0)))
    (hδ₀Pos : 0 < dist.δ 0)
    (hδ₀Lt : dist.δ 0 ≤ δᵣ((f₀), toCode (toLinearCode ↑(C.codeᵢ 0))) ∧
      dist.δ 0 < (1 - Bstar (rateᵢ d P 0)))
    (hδᵢ : ∀ {j : Fin (M + 1)}, j ≠ 0 → 0 < dist.δ j ∧
        dist.δ j < (1 - rateᵢ d P j - 1 / (P.ι j).card) ∧
        dist.δ j < (1 - Bstar (rateᵢ d P j)))
    (h_list :
      ∀ {j : Fin (M + 1)}, j ≠ 0 →
        listDecodable (toCode (toLinearCode ↑(C.codeᵢ j))) (dist.δ j) (dist.l j))
    (vPSpec : ProtocolSpec.VectorSpec n)
    (oSpec : OracleSpec ι) [oSpec.FiniteRange]
    {ιₛ : Type} [OracleInterface (ι → F)]
    (ε_fold : ℝ≥0) (ε_out : Fin (M + 1) → ℝ≥0)
    (ε_shift : Fin (M + 1) → ℝ≥0) (ε_fin : ℝ≥0)
    (ε_sound : ℝ≥0) (ε_rbr : vPSpec.ChallengeIdx → ℝ≥0) :
    ∃ π : VectorIOP vPSpec F oSpec (Statement F ι d) Unit (OStmtOut F ι ιₛ),
      ε_fold ≤ (err' F ((degreeᵢ d P 0) / P.k 0) (rateᵢ d P 0)
                 (dist.δ 0) (P.k 0)).toReal ∧
      (∀ {j : Fin (M + 1)} (hⱼ : j.val ≠ 0),
        ε_out j ≤
          ((dist.l j : ℝ) ^ 2 / 2) *
            ((degreeᵢ d P j : ℝ) /
              (Fintype.card F - (P.ι j).card)) ^ s ∧
        let jPred := predFin j hⱼ;
        ε_shift j ≤
          ((1 - dist.δ jPred) ^ (P.t jPred) : ℝ) +
          (err' F (degreeᵢ d P j) (rateᵢ d P j) (dist.δ j) (P.t jPred) + s).toReal +
          (err' F ((degreeᵢ d P j) / P.k j) (rateᵢ d P j) (dist.δ j) (P.k j)).toReal) ∧
        ε_fin ≤ ((1 - dist.δ M) ^ (P.t M) : ℝ) :=
by
  sorry

end RBR

end StirIOP
