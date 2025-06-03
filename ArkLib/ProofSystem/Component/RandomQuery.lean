/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.OracleReduction.Security.Basic

/-!
# Building blocks for oracle reductions - RandomQuery

We describe common (1-message) protocols that serve as building blocks for constructing oracle
reductions. Each of these components is an oracle reduction with a single message (from prover or
from verifier), and does a minimal amount of computation.

Assume that the beginning data consists of `Statement`, `OStatement`, and `Witness`, and a
relation `rel : Statement → OStatement → Witness → Prop`.
-/

open OracleSpec OracleComp OracleQuery

namespace RandomQuery

open OracleInterface

/-!
3. - There is no witness nor public statement. There are two `OStatement`s, `a` and `b`,
     of the same type. The relation is `a = b`.
   - The verifier samples random `q : OracleInterface.Query` for that type
   and sends it to the prover.
   - The verifier does not do any checks.
   - The final relation is that `a` and `b` are equal at that query.
-/

variable {ι : Type} (oSpec : OracleSpec ι) (OStatement : Type) [OracleInterface OStatement]
  [inst : VCVCompatible (Query OStatement)]

@[reducible]
def pSpec : ProtocolSpec 1 := ![(.V_to_P, Query OStatement)]

instance : ∀ i, OracleInterface ((pSpec OStatement).Message i) | ⟨0, h⟩ => nomatch h
@[reducible, simp] instance : ∀ i, VCVCompatible ((pSpec OStatement).Challenge i)
  | ⟨0, _⟩ => by dsimp [pSpec, ProtocolSpec.Challenge]; exact inst

/--
The prover is trivial: it has no messages to send.  It only receives the verifier's challenge `q`.
We keep track of `(a, b)` in the prover's state, along with the single random query `q`.
-/
def prover : OracleProver (pSpec OStatement) oSpec Unit Unit
    (Query OStatement) Unit
    (fun _ : Fin 2 => OStatement) (fun _ : Fin 2 => OStatement) where

  PrvState
  | 0 => OStatement × OStatement
  | 1 => OStatement × OStatement × (Query OStatement)

  input := fun ⟨(), oracles⟩ () => (oracles 0, oracles 1)

  sendMessage | ⟨0, h⟩ => nomatch h

  receiveChallenge | ⟨0, _⟩ => fun (a, b) q => (a, b, q)

  output := fun (a, b, q) => ((q, ![a, b]), ())

/--
The verifier queries both `a` and `b` at the random point `q`.
We check `OracleInterface.oracle a q = OracleInterface.oracle b q`.
-/
def verifier : OracleVerifier (pSpec OStatement) oSpec Unit (Query OStatement)
    (fun _ : Fin 2 => OStatement) (fun _ : Fin 2 => OStatement) where

  verify := fun _ chal => do
    let q : OracleInterface.Query OStatement := chal ⟨0, rfl⟩
    -- let resp ← liftM <| query
    --   (spec := (oSpec ++ₒ ([fun x ↦ OStatement]ₒ ++ₒ [(pSpec OStatement).Message]ₒ)))
    --   (Sum.inr <| Sum.inl (0 : Fin 2)) q
    pure q

  embed := Function.Embedding.inl

  hEq := by simp

/--
Combine the trivial prover and this verifier to form the oracle reduction:
the input oracles are `(a, b)`, and the output oracles are the same `(a, b)`.
-/
def oracleReduction :
  OracleReduction (pSpec OStatement) oSpec Unit Unit
    (Query OStatement) Unit
    (fun _ : Fin 2 => OStatement) (fun _ : Fin 2 => OStatement) where
  prover := prover oSpec OStatement
  verifier := verifier oSpec OStatement

@[reducible]
def relIn : (Unit × (∀ _ : Fin 2, OStatement)) → Unit → Prop := fun ⟨(), oracles⟩ () =>
  oracles 0 = oracles 1

/--
The final relation states that if the verifier's single query was `q`, then
`a` and `b` agree on that `q`, i.e. `OracleInterface.oracle a q = OracleInterface.oracle b q`.
-/
def relOut : ((Query OStatement) × (∀ _ : Fin 2, OStatement)) → Unit → Prop :=
  fun ⟨q, oStmt⟩ () => OracleInterface.oracle (oStmt 0) q = OracleInterface.oracle (oStmt 1) q

variable [oSpec.FiniteRange]

theorem completeness : OracleReduction.perfectCompleteness
    (relIn OStatement)
    (relOut OStatement)
    (oracleReduction oSpec OStatement) := by
  sorry

-- def langIn : Set (Unit × (∀ _ : Fin 2, OStatement)) := setOf fun ⟨(), oracles⟩ =>
--   oracles 0 = oracles 1

-- def langOut : Set ((Query OStatement) × (∀ _ : Fin 2, OStatement)) := setOf fun ⟨q, oracles⟩ =>
--   OracleInterface.oracle (oracles 0) q = OracleInterface.oracle (oracles 1) q

def stateFunction : (verifier oSpec OStatement).StateFunction (pSpec OStatement) oSpec
    (relIn OStatement).language (relOut OStatement).language where
  toFun
  | 0 => fun ⟨_, oracles⟩ _ => oracles 0 = oracles 1
  | 1 => fun ⟨_, oracles⟩ chal =>
    let q : Query OStatement := by simpa [pSpec] using chal ⟨0, by aesop⟩
    OracleInterface.oracle (oracles 0) q = OracleInterface.oracle (oracles 1) q
  toFun_empty := fun stmt hStmt => by simp_all [relIn, Function.language]
  toFun_next := fun i hDir ⟨stmt, oStmt⟩ tr h => by simp_all
  toFun_full := fun ⟨stmt, oStmt⟩ tr h => by
    simp_all [relOut, Function.language]
    intro a b hSupp
    simp [Verifier.run, OracleVerifier.toVerifier, verifier] at hSupp
    simp [hSupp.1, hSupp.2, h]

/-- The extractor is trivial since the output witness is `Unit`. -/
def extractor : RBRExtractor (pSpec OStatement) oSpec
    (Unit × (∀ _ : Fin 2, OStatement)) Unit :=
  fun _ _ _ _ => ()

-- The key fact governing the soundness of this reduction is a property of the form
-- `∀ a b : OStatement, a ≠ b → #{q | OracleInterface.oracle a q = OracleInterface.oracle b q} ≤ d`.
-- In other words, the oracle instance has distance at most `d`.

variable [Fintype (Query OStatement)] [DecidableEq (Response OStatement)]

instance : Fintype ((pSpec OStatement).Challenge ⟨0, by simp⟩) := by
  dsimp [pSpec, ProtocolSpec.Challenge]; infer_instance

open NNReal

theorem rbr_knowledge_soundness {d : ℕ} (h : OracleInterface.distanceLE OStatement d) :
    (verifier oSpec OStatement).rbrKnowledgeSoundness
      (relIn OStatement)
      (relOut OStatement)
      (fun _ => (d : ℝ≥0) / (Fintype.card (Query OStatement) : ℝ≥0)) := by
  unfold OracleVerifier.rbrKnowledgeSoundness Verifier.rbrKnowledgeSoundness
  refine ⟨stateFunction oSpec OStatement, extractor oSpec OStatement, ?_⟩
  intro ⟨_, oracles⟩ _ rbrP i
  have : i = ⟨0, by simp⟩ := by aesop
  subst i
  dsimp at oracles
  simp [Prover.runWithLogToRound, Prover.runToRound, stateFunction]
  classical
  unfold Function.comp
  simp [probEvent_liftM_eq_mul_inv, ProtocolSpec.Transcript.snoc, Fin.snoc, default]
  rw [div_eq_mul_inv]
  gcongr
  simp [Finset.filter_and]
  split_ifs with hOracles <;> simp
  exact h (oracles 0) (oracles 1) hOracles

end RandomQuery
