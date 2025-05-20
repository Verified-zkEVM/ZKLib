/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Least Authority
-/


import ArkLib.Data.CodingTheory.ConstraintReedSolomon
import ArkLib.Data.CodingTheory.FieldReedSolomon
import ArkLib.Data.CodingTheory.ListDecodeability
import ArkLib.Data.CodingTheory.ProximityBound
import ArkLib.Data.CodingTheory.RelativeHammingDistance
import ArkLib.Data.CodingTheory.SmoothDomain
import ArkLib.OracleReduction.VectorIOR
import ArkLib.ProofSystem.Whir.ProximityGen

open Finset ReedSolomon VectorIOP ListDecodable SmoothDomain ConstraintReedSolomon
open scoped BigOperators NNReal


namespace WhirIOP

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
         {ι : Finset F} {domain : ι ↪ F} {f : ι → F}

def toCode (LC : LinearCode ι F) : Code ι F := LC
/-- **Per‑round protocol parameters.**
For a fixed depth `M`, the reduction runs `M + 1` rounds.  In round
`i ∈ {0,…,M}` we fold by a factor `kᵢ`, evaluate on the point set
`Lᵢ ⊆ F`, and repeat certain proximity checks `tᵢ` times. -/
structure Params (F : Type*) (M : ℕ) where
  foldingParam : Fin M → ℕ
  degreeExp : Fin M → ℕ
  ι : Fin M → Finset F
  repeatParam : Fin M → ℕ

structure paramConditions {sumk m M : ℕ} {i : Fin M} (P : Params F M) where
  h_sumk : sumk = (∑ i : Fin M, P.foldingParam i) -- ∑ᵢ kᵢ
  h_sumkLt : sumk ≤ m -- ∑ᵢ kᵢ ≤ m
  h_smoothDom : ∀ i, (P.ι i).card ≥ 2 ^ P.degreeExp i -- |ιᵢ ≥ 2 ^ mᵢ|
  h_repeatPLt : ∀ i, (P.repeatParam i) < (P.ι i).card


/- /-- **Degree after `i` folds.**
The starting degree is `d`; every fold divides it by `kⱼ (j<i)` to obtain `dᵢ`.
We assume divisibility so the integer division is exact. -/
def degreeᵢ {M : ℕ} (degree : ℕ) (P : Params F M) (i : Fin M) : ℕ :=
  degree / ∏ j < i, (P.k j)

/-- **`Rateᵢ= degreeᵢ/|Lᵢ|`** of the Reed–Solomon code used in round `i`.
A real number because most analytic bounds live in `ℝ`. -/
noncomputable def rateᵢ {M : ℕ} (degree : ℕ) (P : Params F M)
    (i : Fin (M + 1)) : ℝ :=
  (degreeᵢ degree P i : ℝ) / ((P.ι i).card : ℝ) -/

/- /-- Distance and list‑size targets per round. -/
structure Distances (M : ℕ) (P : Params F M) (i s : ℕ) where
  δ : Fin M → ℚ
  l : (i : Fin M) → Fin (P.foldingParam i) → ℚ -/

/-- **Family of Reed–Solomon codes** actually expected by the verifier.
The index `i` says *which* round we refer to; all codes are computed from
the same source polynomial `f`. -/
structure Code
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    {M : ℕ} (P : Params F M) (i s : ℕ) where
    ιPowᵢ : (i : Fin M) → indexPow (P.ι i) (2 ^ s)
    domainᵢₛ : (i : Fin M) → (s : Fin (P.foldingParam i)) → (indexPow (P.ι i) (2 ^ s.val)) ↪ F
    codeᵢₛ : (i : Fin M) → (s : Fin (P.foldingParam i)) → code F (indexPow (P.ι i) (2 ^ s.val))
      (domainᵢₛ i s) (P.degreeExp i - s)

/-- Predecessor inside `Fin (n+1)` (requires `i ≠ 0`). -/
def predFin {n : ℕ} (i : Fin (n + 1)) (h : i.val ≠ 0) : Fin (n + 1) :=
  ⟨Nat.pred i.val, by
    have hpred : Nat.pred i.val < i.val := Nat.pred_lt h
    exact Nat.lt_trans hpred i.isLt⟩


section RBR
open Finset BigOperators OracleComp OracleSpec ProtocolSpec
variable {n : ℕ}

structure Statement
  (F : Type)[Field F][Fintype F][DecidableEq F]
  (ι : Finset F)(d : ℕ) where
  eval : ι -> F


@[reducible]
def OStmtOut (F : Type) (ι : Finset F) (ιₛ : Type) : ιₛ → Type :=
  fun _ => ι → F

instance instWhirOraclePerIndex
  {F : Type} [Field F] [Fintype F] [DecidableEq F]
  {ι : Finset F} {ιₛ : Type} :
  ∀ _ : ιₛ, OracleInterface (ι → F) :=
  fun _ => {
    Query := {x // x ∈ ι}
    Response := F
    oracle := fun f q => f q
  }

/-- **Round-by-round soundness of the WHIR IOPP**-/
theorem whir_rbr_soundness
    (F : Type) [Field F] [Fintype F] [DecidableEq F] [VCVCompatible F] (σ₀ : F)
    (d dstar : ℕ) (ι₀ : Finset F) [Nonempty ι₀] (domain₀ : ι₀ ↪ F) (f₀ : ι₀ → F)
    (M m₀ smoothk : ℕ) (hM : M > 0) (P : Params F M) (wPoly₀ : MvPolynomial (Fin (m₀ + 1)) F)
    -- {h_nonempty: ∀ i : Fin M, Nonempty (P.ι i)}
    (i s : ℕ) (C : Code P i s)
    (δ : (i : Fin M) → ℚ) (l : (i : Fin M) → Fin (P.foldingParam i) → ℚ) -- distance parameters
    [Smooth domain₀ smoothk] (cc₀ : constraintCode F ι₀ domain₀ smoothk m₀ wPoly₀ σ₀)
    (h_not_code :
    f₀ ∉ ↑(constraintCode1 F ι₀ domain₀ smoothk m₀ wPoly₀ σ₀)) -- f ∉ CRS[F,ι₀,m₀,wPoly₀,σ₀]
    (hδ₀Pos : 0 < δ ⟨0, hM⟩)
    (hδ₀Lt : δ ⟨0, hM⟩ < δᵣ(f₀, ↑(constraintCode1 F ι₀ domain₀ smoothk m₀ wPoly₀ σ₀)))
    (hδᵢ : ∀ { i : Fin M}, δ i > 0) -- TODO: and δᵢ < (1 - B*(rsCodeᵢₛ, 2))
    (h_list :
      ∀ {i' : Fin M} {s' : Fin (P.foldingParam i')},
        listDecodable (toCode (toLinearCode ↑(C.codeᵢₛ i' s'))) (δ i') (l i' s'))
    (vPSpec : ProtocolSpec.VectorSpec n)
    (oSpec : OracleSpec ι) [oSpec.FiniteRange]
    {ιₛ : Type} [OracleInterface (ι₀ → F)]
    (ε_fold : ℝ≥0) (ε_out : Fin (M + 1) → ℝ≥0)
    (ε_shift : Fin (M + 1) → ℝ≥0) (ε_fin : ℝ≥0)
    (ε_sound : ℝ≥0) (ε_rbr : vPSpec.ChallengeIdx → ℝ≥0) : d = 0 := by sorry
/-     ∃ π : VectorIOP vPSpec F oSpec (Statement F ι₀ d) Unit (OStmtOut F ι₀ ιₛ),
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
        ε_fin ≤ ((1 - dist.δ M) ^ (P.t M) : ℝ)  -/


end RBR

end WhirIOP
