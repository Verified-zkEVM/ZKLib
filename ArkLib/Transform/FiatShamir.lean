/-
Copyright (c) 2024 ZKLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.OracleReduction.Composition.Sequential

/-!
  # The Fiat-Shamir Transformation

  This file defines the Fiat-Shamir transformation. This transformation takes in a (public-coin)
  interactive reduction (IR) `R` and transforms it into a non-interactive reduction via removing
  interaction from `R`. In particular, in the transformed reduction, queries to the verifier's
  challenges are replaced by queries to a random oracle.

  We will show that the transformation satisfies security properties as follows:

  - Completeness is preserved
  - State-restoration (knowledge) soundness implies (knowledge) soundness
  - Honest-verifier zero-knowledge implies zero-knowledge

  ## Notes

  Our formalization mostly follows the treatment in the Chiesa-Yogev textbook.

  There are many variants of Fiat-Shamir. The most theoretical one is that one hashes the entire
  statement and transcript up to the point of deriving a new challenge. This is inefficient and not
  actually how it is implemented in practice.

  In contrast, most implementations today use the hash function as a **cryptographic sponge**, which
  permits adding in bitstrings (serialized from the messages) and squeezing out new bitstrings (that
  are then de-serialized into challenges).
-/

open ProtocolSpec

variable {n : ℕ}

section Instances

variable {Message : Type}

instance : IsEmpty (ChallengeIndex ![(.P_to_V, Message)]) := by
  simp [ChallengeIndex]
  infer_instance

instance : Unique (MessageIndex ![(.P_to_V, Message)]) where
  default := ⟨0, by simp⟩
  uniq := fun i => by ext; simp

instance : ∀ i, VCVCompatible (Challenge ![(.P_to_V, Message)] i) :=
  fun i => isEmptyElim i

end Instances

/-- Turn each verifier's challenge into an oracle, where one needs to query
  with an input statement
  and a prior transcript to get a challenge (useful for Fiat-Shamir) -/
@[reducible, inline, specialize]
def instChallengeToOracleFiatShamir {pSpec : ProtocolSpec n} {i : pSpec.ChallengeIndex}
    {StmtIn : Type} [DecidableEq StmtIn] [h : ∀ j, DecidableEq (pSpec j).2]
    [VCVCompatible (pSpec.Challenge i)] : ToOracle (pSpec.Challenge i) where
  Query := StmtIn × Transcript i.1.castSucc pSpec
  Response := pSpec.Challenge i
  oracle := fun c _ => c
  query_decidableEq' := by simp [Transcript]; infer_instance

/-- The oracle interface for Fiat-Shamir.

This is the (inefficient) version where we hash the input statement and the entire transcript up to
the point of deriving a new challenge. We also add in an optional salt. -/
def fiatShamirSpec (pSpec : ProtocolSpec n) (StmtIn Salt : Type) [VCVCompatible StmtIn]
    [VCVCompatible Salt] [∀ i, VCVCompatible (pSpec i).2] : OracleSpec pSpec.ChallengeIndex where
  domain := fun i => StmtIn × Transcript i.1.succ pSpec × Salt
  range := fun i => pSpec.Challenge i
  domain_decidableEq' := inferInstance
  range_decidableEq' := inferInstance
  range_inhabited' := inferInstance
  range_fintype' := inferInstance

-- TODO: define a more efficient version where one hashes the most recent challenge along with the
-- messages since that challenge (the first challenge is obtained by hashing the statement & the
-- messages so far)

variable {pSpec : ProtocolSpec n} {ι : Type} {oSpec : OracleSpec ι}
  {StmtIn WitIn StmtOut WitOut : Type} [VCVCompatible StmtIn] [∀ i, VCVCompatible (pSpec i).2]
  (Salt : Type) [VCVCompatible Salt]

def Prover.fiatShamir (P : Prover pSpec oSpec StmtIn WitIn StmtOut WitOut) :
    NonInteractiveProver (oSpec ++ₒ fiatShamirSpec pSpec StmtIn Salt)
      StmtIn WitIn StmtOut WitOut (∀ i, pSpec.Message i) where
  PrvState := fun i => match i with
    | 0 => P.PrvState 0
    | _ => P.PrvState (Fin.last n)
  input := P.input
  --
  sendMessage := fun idx state => by
    simp [Unique.uniq _ idx, default] at state ⊢
    sorry
  -- This function is never invoked so we apply the elimination principle
  receiveChallenge := fun idx _ _ => isEmptyElim idx
  output := P.output

def Verifier.fiatShamir (V : Verifier pSpec oSpec StmtIn StmtOut) :
    NonInteractiveVerifier (oSpec ++ₒ fiatShamirSpec pSpec StmtIn Salt)
      StmtIn StmtOut (∀ i, pSpec.Message i) where
  verify := fun stmtIn messages =>
    let transcript := sorry
    V.verify stmtIn transcript

/-- TODO: change `unifSpec` to something more appropriate (maybe a `CryptographicSponge`) -/
def Reduction.fiatShamir (R : Reduction pSpec oSpec StmtIn WitIn StmtOut WitOut) :
    NonInteractiveReduction (oSpec ++ₒ fiatShamirSpec pSpec StmtIn Salt)
      StmtIn WitIn StmtOut WitOut (∀ i, pSpec.Message i) :=
  ⟨R.prover.fiatShamir Salt, R.verifier.fiatShamir Salt⟩

section Security

noncomputable section

open scoped NNReal

variable [DecidableEq ι]

theorem fiatShamir_completeness (relIn : StmtIn → WitIn → Prop) (relOut : StmtOut → WitOut → Prop)
    (completenessError : ℝ≥0) (R : Reduction pSpec oSpec StmtIn WitIn StmtOut WitOut) :
  R.completeness relIn relOut completenessError →
    (R.fiatShamir Salt).completeness relIn relOut completenessError := sorry

-- TODO: state-restoration (knowledge) soundness implies (knowledge) soundness after Fiat-Shamir

end

end Security
