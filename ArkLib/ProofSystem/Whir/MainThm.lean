/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Least Authority
-/


import ArkLib.Data.CodingTheory.ConstraintReedSolomon
import ArkLib.Data.CodingTheory.ListDecodeability
import ArkLib.Data.CodingTheory.RelativeHammingDistance
import ArkLib.Data.CodingTheory.SmoothDomainGeneric
import ArkLib.OracleReduction.VectorIOR
import ArkLib.ProofSystem.Whir.BlockRelDistanceGeneric
import ArkLib.ProofSystem.Whir.GenMutualCorrAgreement
import ArkLib.ProofSystem.Whir.ProximityGen

open Finset ReedSolomon VectorIOP ListDecodable SmoothDomain ConstraintReedSolomon
open scoped BigOperators NNReal


namespace WhirIOP

open SmoothDomain BlockRelDistance CorrelatedAgreement Generator
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
         {M : ℕ} [Fact (0 < M)] (ι : Fin M → Type) [∀ i : Fin M, Fintype (ι i)]
         [∀ i : Fin M, DecidableEq (ι i)]

-- def toCode (LC : LinearCode ι F) : Code ι F := LC
/-- **Per‑round protocol parameters.**
For a fixed depth `M`, the reduction runs `M + 1` rounds.  In round
`i ∈ {0,…,M}` we fold by a factor `kᵢ`, evaluate on the point set
`Lᵢ ⊆ F`, and repeat certain proximity checks `tᵢ` times. -/
structure Params (F : Type) where
  foldingParam : Fin M → ℕ
  degreeExp : Fin M → ℕ
  φ_i : (i : Fin M) → (ι i) ↪ F
  repeatParam : Fin M → ℕ

structure paramConditions (P : Params ι F) where
  m : ℕ -- m = P.degreeExp 0
  h_m : m = P.degreeExp ⟨0, Fact.out⟩
  h_sumkLt : ∑ i : Fin M, P.foldingParam i ≤ m
  h_degreeExp_i : ∀ i : Fin M, i ≠ ⟨0, Fact.out⟩ →
    P.degreeExp i = m - ∑ j : Fin i, P.foldingParam (Fin.castLT j (Nat.lt_trans j.isLt i.isLt))
  h_smooth : ∀ i : Fin M, Smooth (P.φ_i i)
  h_repeatPLt : ∀ i : Fin M, P.repeatParam i < Fintype.card (ι i)


class GenMutualCorrParams (P: Params ι F) (S_i: ∀ i : Fin M, Finset (ι i)) where

  δ_i : Fin M → ℝ≥0
  dist_ij : (i : Fin M) → Fin (P.foldingParam i) → ℝ≥0

  φ_ij : ∀ i : Fin M, ∀ j : Fin (P.foldingParam i), (indexPowT (S_i i) (P.φ_i i) j) ↪ F

  inst1 : ∀ i : Fin M, ∀ j : Fin (P.foldingParam i), Fintype (indexPowT (S_i i) (P.φ_i i) j)
  inst2 : ∀ i : Fin M, ∀ j : Fin (P.foldingParam i), Nonempty (indexPowT (S_i i) (P.φ_i i) j)
  inst3 : ∀ i : Fin M, ∀ j : Fin (P.foldingParam i), DecidableEq (indexPowT (S_i i) (P.φ_i i) j)
  inst4 : ∀ i : Fin M, ∀ j : Fin (P.foldingParam i), Smooth (φ_ij i j)

  Gen_ij : ∀ i : Fin M, ∀ j : Fin (P.foldingParam i),
    ProximityGenerator (indexPowT (S_i i) (P.φ_i i) j) F
  Gen_α_ij : ∀ i : Fin M, ∀ j : Fin (P.foldingParam i),
    ProximityGenerator (indexPowT (S_i i) (P.φ_i i) j) F

  hgen : ∀ i : Fin M, ∀ j : Fin (P.foldingParam i), ∀ α : F, Gen_α_ij i j =
    proximityGenerator_α (Gen_ij i j) α (φ_ij i j) (P.degreeExp i)

  BStar_ij : ∀ i : Fin M, ∀ j : Fin (P.foldingParam i),
    (Set ((indexPowT (S_i i) (P.φ_i i) j) → F)) → ℕ → ℝ≥0
  errStar_ij : ∀ i : Fin M, ∀ j : Fin (P.foldingParam i),
    (Set ((indexPowT (S_i i) (P.φ_i i) j) → F)) → ℕ → ℝ≥0 → ℝ≥0

  C_ij : ∀ i : Fin M, ∀ j : Fin (P.foldingParam i), Set ((indexPowT (S_i i) (P.φ_i i) j) → F)
  hcode : ∀ i : Fin M, ∀ j : Fin (P.foldingParam i), (C_ij i j) = (Gen_α_ij i j).C

  h : ∀ i : Fin M, ∀ j : Fin (P.foldingParam i), genMutualCorrAgreement (Gen_α_ij i j)
        (BStar_ij i j (C_ij i j) (Gen_α_ij i j).l)
        (errStar_ij i j (C_ij i j) (Gen_α_ij i j).l)

  hδLe : ∀ i : Fin M, (δ_i i) ≤ 1 - Finset.univ.sup (fun j => BStar_ij i j (C_ij i j) 2)

  hlistDecode : ∀ i : Fin M, ∀ j : Fin (P.foldingParam i),
    listDecodable (C_ij i j) (dist_ij i j) (δ_i i)


section RBR
open Finset BigOperators OracleComp OracleSpec ProtocolSpec
variable {n : ℕ}

structure Statement
  (F : Type)[Field F][Fintype F][DecidableEq F]
  (ι : Fin M → Type) [∀ i : Fin M, Fintype (ι i)]
  (degreeExp : Fin M → ℕ)
  where
    eval : (i : Fin M) → (ι i) → F


@[reducible]
def OStmtOut (F : Type) (ι₀ : Type) (ιₛ : Type) [Fintype ι₀][Fintype ιₛ] : ιₛ → Type :=
    fun _ => ι₀ → F

@[instance]
instance instWhirOraclePerIndex
  {F : Type} [Field F] [Fintype F] [DecidableEq F]
  {ι₀ : Type} [Fintype ι₀] {ιₛ :  Type} :
  ∀ _ : ιₛ, OracleInterface (ι₀ → F) :=
  fun _ => {
    Query := ι₀
    Response := F
    oracle := fun f q => f q
  }

/-- **Round-by-round soundness of the WHIR IOPP**-/
theorem whir_rbr_soundness
    {ι₀ : Type} {ιₛ : Type} [Fintype ι₀][Fintype ιₛ] [VCVCompatible F] {d dstar : ℕ}
    {P: Params ι F} {S_i : ∀ i : Fin M, Finset (ι i)} [∀ i : Fin M, Fact (0 < P.foldingParam i)]
    {hParams : paramConditions ι P} {h : GenMutualCorrParams ι P S_i}
    {m_0 : ℕ} (hm_0 : m_0 = P.degreeExp ⟨0, Fact.out⟩) {σ₀ : F}
    {wPoly₀ : MvPolynomial (Fin (m_0 + 1)) F}
    {δ : ℝ} {f_0 : (ι ⟨0, Fact.out⟩) → F}
    [Smooth (P.φ_i ⟨0, Fact.out⟩)] [Nonempty (ι ⟨0, Fact.out⟩)]
    (h_not_code :
    f_0 ∉
      (constraintCode F (ι ⟨0, Fact.out⟩) (P.φ_i ⟨0, Fact.out⟩) m_0 wPoly₀ σ₀))
        -- f ∉ CRS[F,ι₀,m₀,wPoly₀,σ₀]
    (hδ₀Lt : δ < δᵣ(f_0, (constraintCode F (ι ⟨0, Fact.out⟩) (P.φ_i ⟨0, Fact.out⟩) m_0 wPoly₀ σ₀)))
    (vPSpec : ProtocolSpec.VectorSpec n)
    (oSpec : OracleSpec ι₀) [oSpec.FiniteRange] [OracleInterface (ι₀ → F)]
    (ε_fold : (i : Fin M) → Fin (P.foldingParam i) → ℝ≥0) (ε_out : Fin M → ℝ≥0)
    (ε_shift : Fin M → ℝ≥0) (ε_fin : ℝ≥0) :
      ∃ π : VectorIOP vPSpec F oSpec (Statement F ι P.degreeExp) Unit (OStmtOut F ι₀ ιₛ),
        ∀ j : Fin (P.foldingParam ⟨0, Fact.out⟩),
          let errStar_0_j j :=
            h.errStar_ij ⟨0, Fact.out⟩ j (h.C_ij ⟨0, Fact.out⟩ j)  2 (h.δ_i ⟨0, Fact.out⟩)
          let j_pred : Fin (P.foldingParam ⟨0, Fact.out⟩) := ⟨j.val - 1, sorry⟩
          ε_fold ⟨0, Fact.out⟩ j ≤
            ((dstar • (h.dist_ij ⟨0, Fact.out⟩ j_pred)) / Fintype.card F)
              + (errStar_0_j j)
        ∧
        ∀ i : Fin M,
          ε_out i ≤
            2^(P.degreeExp i) • (h.dist_ij i ⟨0, Fact.out⟩)^2 / (2 • Fintype.card F)
        ∧
        ∀ i : Fin M, (h_i : i.val ≠ 0) →
        let i_pred : Fin M := ⟨i.val - 1, sorry⟩
        ε_shift i ≤ (1 - (h.δ_i i_pred))^(P.repeatParam i_pred) +
            ((h.dist_ij i ⟨0, Fact.out⟩) • (P.repeatParam i_pred) + 1) / Fintype.card F
        ∧
        ∀ i : Fin M, ∀ j : Fin (P.foldingParam i),
          let errStar_i_j i j := h.errStar_ij i j (h.C_ij i j) 2 (h.δ_i i)
          let j_pred : Fin (P.foldingParam i) := ⟨j.val -1, sorry⟩
          ε_fold i j ≤ d • (h.dist_ij i j_pred) / Fintype.card F + errStar_i_j i j
        ∧
        let lastM : Fin M := ⟨M-1, sorry⟩
        ε_fin ≤ (1 - (h.δ_i lastM))^(P.repeatParam lastM)
    := by sorry





end RBR

end WhirIOP
