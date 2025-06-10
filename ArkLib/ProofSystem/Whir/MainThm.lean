/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Least Authority
-/

import ArkLib.Data.CodingTheory.ConstraintReedSolomon
import ArkLib.Data.CodingTheory.ListDecodeability
import ArkLib.Data.CodingTheory.RelativeHammingDistance
import ArkLib.OracleReduction.VectorIOR
import ArkLib.ProofSystem.Whir.BlockRelDistanceGeneric
import ArkLib.ProofSystem.Whir.GenMutualCorrAgreement
import ArkLib.ProofSystem.Whir.ProximityGen

namespace WhirIOP

open BigOperators BlockRelDistance CorrelatedAgreement Generator Finset
     ListDecodable NNReal ReedSolomon SmoothDomain

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
         {M : ℕ} [Fact (0 < M)] (ι : Fin M → Type) [∀ i : Fin M, Fintype (ι i)]
         [∀ i : Fin M, DecidableEq (ι i)]

/-- ** Per‑round protocol parameters. **
For a fixed depth `M`, the reduction runs `M` rounds.
In round `i ∈ {0,…,M-1}` we fold by a factor `foldingParamᵢ`,
evaluate on the point set `ιᵢ` through the embedding `φᵢ : ιᵢ ↪ F`,
and repeat certain proximity checks `repeatParamᵢ` times. -/
structure Params (F : Type) where
  foldingParam : Fin M → ℕ
  varCount : Fin M → ℕ
  φ : (i : Fin M) → (ι i) ↪ F
  repeatParam : Fin M → ℕ

/-- ** Conditions that protocol parameters must satisfy. **
  h_m : m = varCount₀
  h_sumkLt : ∑ i : Fin M, varCountᵢ ≤ m
  h_varCount_i : ∀ i : Fin M, i ≠ 0, varCountᵢ = m - ∑ j < i foldingParamⱼ
  h_smooth : each φᵢ must be a smooth evaluation domain
  h_repeatPLt : ∀ i : Fin M, repeatParamᵢ ≤ |ιᵢ| -/
structure ParamConditions (P : Params ι F) where
  m : ℕ -- m = P.varCount 0
  h_m : m = P.varCount ⟨0, Fact.out⟩
  h_sumkLt : ∑ i : Fin M, P.foldingParam i ≤ m
  h_varCount_i : ∀ i : Fin M, i ≠ ⟨0, Fact.out⟩ →
    P.varCount i = m - ∑ j : Fin i, P.foldingParam (Fin.castLT j (Nat.lt_trans j.isLt i.isLt))
  h_smooth : ∀ i : Fin M, Smooth (P.φ i)
  h_repeatPLt : ∀ i : Fin M, P.repeatParam i ≤ Fintype.card (ι i)

/--
  `GenMutualCorrParams` binds together a set of smooth ReedSolomon codes
  `C_{i < M,j < foldingParamᵢ} = RS[F, ιᵢ^(2ʲ), (varCountᵢ - j)]` with
  `Gen_α_ij` which is a proximity generator with mutual correlated agreement
  for `C_ij` with proximity parameters `BStar_ij` and `errStar_ij`.

  Additionally, it includes the condition that
    C_ij is `(dist_ij,δᵢ)`-list decodeable,
  where `δᵢ = 1 - max_{j < foldingParamᵢ} BStar(C_ij,2)`
--/
class GenMutualCorrParams (P: Params ι F) (S: ∀ i : Fin M, Finset (ι i)) where

  δ : Fin M → ℝ≥0
  dist : (i : Fin M) → Fin (P.foldingParam i) → ℝ≥0

-- φ i j : ιᵢ^(2ʲ) ↪ F
  φ : ∀ i : Fin M, ∀ j : Fin (P.foldingParam i), (indexPowT (S i) (P.φ i) j) ↪ F

  inst1 : ∀ i : Fin M, ∀ j : Fin (P.foldingParam i), Fintype (indexPowT (S i) (P.φ i) j)
  inst2 : ∀ i : Fin M, ∀ j : Fin (P.foldingParam i), Nonempty (indexPowT (S i) (P.φ i) j)
  inst3 : ∀ i : Fin M, ∀ j : Fin (P.foldingParam i), DecidableEq (indexPowT (S i) (P.φ i) j)
  inst4 : ∀ i : Fin M, ∀ j : Fin (P.foldingParam i), Smooth (φ i j)

  Gen : ∀ i : Fin M, ∀ j : Fin (P.foldingParam i),
    ProximityGenerator (indexPowT (S i) (P.φ i) j) F
  Gen_α : ∀ i : Fin M, ∀ j : Fin (P.foldingParam i),
    ProximityGenerator (indexPowT (S i) (P.φ i) j) F

-- this ensures that Gen_α_ij is a proxmity generator for C_ij = RS[F, ιᵢ^(2^j), (varCountᵢ - j)]
-- wrt proximity generator Gen_α (α,l) = {1,α²,...,α^{l-1}}
  hgen : ∀ i : Fin M, ∀ j : Fin (P.foldingParam i), ∀ α : F, Gen_α i j =
    proximityGenerator_α (Gen i j) α (φ i j) (P.varCount i - j)

  BStar : ∀ i : Fin M, ∀ j : Fin (P.foldingParam i),
    (Set ((indexPowT (S i) (P.φ i) j) → F)) → ℕ → ℝ≥0
  errStar : ∀ i : Fin M, ∀ j : Fin (P.foldingParam i),
    (Set ((indexPowT (S i) (P.φ i) j) → F)) → ℕ → ℝ≥0 → ℝ≥0

  C : ∀ i : Fin M, ∀ j : Fin (P.foldingParam i), Set ((indexPowT (S i) (P.φ i) j) → F)
  hcode : ∀ i : Fin M, ∀ j : Fin (P.foldingParam i), (C i j) = (Gen_α i j).C

  h : ∀ i : Fin M, ∀ j : Fin (P.foldingParam i), genMutualCorrAgreement (Gen_α i j)
        (BStar i j (C i j) (Gen_α i j).l)
        (errStar i j (C i j) (Gen_α i j).l)

  hδLe : ∀ i : Fin M, (δ i) ≤ 1 - Finset.univ.sup (fun j => BStar i j (C i j) 2)

  hlistDecode : ∀ i : Fin M, ∀ j : Fin (P.foldingParam i),
    listDecodable (C i j) (δ i) (dist i j)

section RBR
open OracleComp OracleSpec ProtocolSpec NNRat
variable {n : ℕ}

/--Statement for the whir Vector IOPP consisting of a field `F`, M evaluation domains `ιᵢ` and
  M degree parameters `varCountᵢ` -/
structure Statement
  (F : Type)[Field F][Fintype F][DecidableEq F]
  (ι : Fin M → Type) [∀ i : Fin M, Fintype (ι i)]
  (varCount : Fin M → ℕ)

/--`OStmtOut` defines the oracle message type for a multi-indexed setting:
  given index type `ιₛ`, base input type `ι₀`, and field `F`, the output type at each index `i : ιₛ`
  is a function `ι₀ → F` representing an evaluation over `ι₀`.-/
@[reducible]
def OStmtOut (ιₛ ι₀ F : Type) : ιₛ → Type :=
    fun _ => ι₀ → F

/-- **Round-by-round soundness of the WHIR Vector IOPP**-/
theorem whir_rbr_soundness
    [VCVCompatible F] {d dstar : ℕ} {ιₛ ιₒ : Type}
  -- P : set of M parameters including foldingParamᵢ, varCountᵢ, φᵢ, repeatParamᵢ,
  -- where foldingParamᵢ > 0
    {P: Params ι F} {S : ∀ i : Fin M, Finset (ι i)} [∀ i : Fin M, Fact (0 < P.foldingParam i)]
  -- hParams : a set of conditions that parameters in P must satisfy
  -- h : a set of smooth ReedSolomon codes C_ij bundled with its proximity generators
  -- and condition for list decodeability
    {hParams : ParamConditions ι P} {h : GenMutualCorrParams ι P S}
    {m_0 : ℕ} (hm_0 : m_0 = P.varCount ⟨0, Fact.out⟩) {σ₀ : F}
    {wPoly₀ : MvPolynomial (Fin (m_0 + 1)) F} {δ : ℝ}
    [Smooth (P.φ ⟨0, Fact.out⟩)] [Nonempty (ι ⟨0, Fact.out⟩)]
  -- ∀ f₀ : ι₀ → F, f₀ ∉ CRS[F,ι₀,m₀,wPoly₀,σ₀]
    (h_not_code : ∀ f_0 : (ι ⟨0, Fact.out⟩) → F,
      f_0 ∉ (constraintCode F (ι ⟨0, Fact.out⟩) (P.φ ⟨0, Fact.out⟩) m_0 wPoly₀ σ₀))
  -- ∀ f₀ : ι₀ → F, δ₀ < δᵣ(f₀, CRS[F,ι₀,m₀,wPoly₀,σ₀]),
  -- where δᵣ denotes the relative Hammin distance
    (hδ₀Lt : ∀ f_0 : (ι ⟨0, Fact.out⟩) → F,
      (h.δ ⟨0, Fact.out⟩) <
        (δᵣ(f_0, (constraintCode F (ι ⟨0, Fact.out⟩) (P.φ ⟨0, Fact.out⟩) m_0 wPoly₀ σ₀)) : ℝ))
    (vPSpec : ProtocolSpec.VectorSpec n)
    (oSpec : OracleSpec ιₒ)
    [oSpec.FiniteRange] [O : ∀ i, OracleInterface (OStmtOut ιₛ (ι ⟨0, Fact.out⟩) F i) ]
    (ε_fold : (i : Fin M) → Fin (P.foldingParam i) → ℝ≥0) (ε_out : Fin M → ℝ≥0)
    (ε_shift : Fin M → ℝ≥0) (ε_fin : ℝ≥0) :
    -- ∃ a Vector IOPP π with Statement = (F ι varCount), Witness = Unit, OStmtOut = (ιₛ ι₀ F)
      ∃ π :
        VectorIOP vPSpec F oSpec (Statement F ι P.varCount) Unit (OStmtOut ιₛ (ι ⟨0, Fact.out⟩) F),
        let maxDeg := (Finset.univ : Finset (Fin m_0)).sup (fun i => wPoly₀.degreeOf (Fin.succ i))
      -- dstar = (1 + deg_Z(wPoly₀) + max_{i < m_0} deg_X(wPoly₀))
        let dstar := 1 + (wPoly₀.degreeOf 0) + maxDeg
        let d := max dstar 3
        -- ε_fold(0,j) ≤ dstar • dist(0,j-1) / |F| + errStar(C_0j, 2, δ₀)
        ∀ j : Fin (P.foldingParam ⟨0, Fact.out⟩),
          let errStar_0 j :=
            h.errStar ⟨0, Fact.out⟩ j (h.C ⟨0, Fact.out⟩ j)  2 (h.δ ⟨0, Fact.out⟩)
          let j_pred : Fin (P.foldingParam ⟨0, Fact.out⟩) := ⟨j.val - 1, sorry⟩
          ε_fold ⟨0, Fact.out⟩ j ≤
            ((dstar • (h.dist ⟨0, Fact.out⟩ j_pred)) / Fintype.card F)
              + (errStar_0 j)
        ∧
        -- ε_out(i) ≤ 2^(varCountᵢ) • dist(i,0)^2 / 2 • |F|
        ∀ i : Fin M,
          ε_out i ≤
            2^(P.varCount i) • (h.dist i ⟨0, Fact.out⟩)^2 / (2 • Fintype.card F)
        ∧
        -- ε_shift(i) ≤ (1 - δ_{i-1})^(repeatParam_{i-1})
        --  + (dist(i,0) • (repeatParam_{i-1} + 1)) / |F|
        ∀ i : Fin M, (h_i : i.val ≠ 0) →
        let i_pred : Fin M := ⟨i.val - 1, sorry⟩
        ε_shift i ≤ (1 - (h.δ i_pred))^(P.repeatParam i_pred) +
            ((h.dist i ⟨0, Fact.out⟩) • (P.repeatParam i_pred) + 1) / Fintype.card F
        ∧
        -- ε_fold(i,j) ≤ d • dist(i,j-1) / |F| + errStar(C_ij,2,δᵢ)
        ∀ i : Fin M, ∀ j : Fin (P.foldingParam i),
          let errStar i j := h.errStar i j (h.C i j) 2 (h.δ i)
          let j_pred : Fin (P.foldingParam i) := ⟨j.val -1, sorry⟩
          ε_fold i j ≤ d • (h.dist i j_pred) / Fintype.card F + errStar i j
        ∧
        -- ε_fin ≤ (1 - δ_{M-1})^(repeatParam_{M-1})
        let lastM : Fin M := ⟨M-1, sorry⟩
        ε_fin ≤ (1 - (h.δ lastM))^(P.repeatParam lastM)
    := by sorry

end RBR
end WhirIOP
