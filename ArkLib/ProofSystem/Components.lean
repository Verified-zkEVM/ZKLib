/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.OracleReduction.Security.Basic

/-!
# Building blocks for oracle reductions

We describe common (1-message) protocols that serve as building blocks for constructing oracle
reductions. Each of these components is an oracle reduction with a single message (from prover or
from verifier), and does a minimal amount of computation.

Assume that the beginning data consists of `Statement`, `OStatement`, and `Witness`, and a
relation `rel : Statement → OStatement → Witness → Prop`.
-/

/-!
1. - The prover sends an oracle of type `WitEquiv` (supposed to be the witness up to equivalence) to
     the verifier.
   - The verifier does nothing.
   - The output data has the same `Statement`, have output `OStatement` be the previous `OStatement`
     plus an oracle for `EncWit`, and have no witness.
   - The new relation is `rel` but replacing `Witness` with `EncWit`.

This is usually used as the first step of an oracle reduction, to replace the witness with an
oracle statement.
-/

open OracleSpec OracleComp OracleQuery

namespace SendWitness

variable {ι : Type} (oSpec : OracleSpec ι) (Statement Witness : Type)
  {ιₛᵢ : Type} (OStatement : ιₛᵢ → Type) [∀ i, OracleInterface (OStatement i)]
  (WitEquiv : Type) [OracleInterface WitEquiv] (equiv : Witness ≃ WitEquiv)

@[reducible]
def pSpec : ProtocolSpec 1 := ![(.P_to_V, WitEquiv)]

-- TODO: figure out why `OracleInterface` & `VCVCompatible` instances cannot be automatically
-- synthesized
instance : ∀ i, OracleInterface ((pSpec WitEquiv).Message i)
  | ⟨0, _⟩ => by dsimp; infer_instance
instance : ∀ i, VCVCompatible ((pSpec WitEquiv).Challenge i) | ⟨0, h⟩ => nomatch h

def prover : OracleProver (pSpec WitEquiv) oSpec Statement Witness Statement Unit
    OStatement (OStatement ⊕ᵥ (fun _ : Unit => WitEquiv)) where
  PrvState
  | 0 => Statement × (∀ i, OStatement i) × Witness
  | 1 => Statement × (∀ i, OStatement i) × WitEquiv
  input := fun ⟨stmt, oStmt⟩ wit => ⟨stmt, oStmt, wit⟩
  sendMessage | ⟨0, _⟩ => fun ⟨stmt, oStmt, wit⟩ => pure (equiv wit, ⟨stmt, oStmt, equiv wit⟩)
  receiveChallenge | ⟨0, h⟩ => nomatch h
  output := fun ⟨stmt, oStmt, encWit⟩ => (⟨stmt, (Sum.rec oStmt (fun _ => encWit))⟩, ())

def verifier : OracleVerifier (pSpec WitEquiv) oSpec Statement Statement
    OStatement (OStatement ⊕ᵥ (fun _ : Unit => WitEquiv)) where
  verify := fun stmt _ => pure stmt
  embed := by simp [pSpec, ProtocolSpec.MessageIdx]; sorry
  hEq := sorry

def oracleReduction : OracleReduction (pSpec WitEquiv) oSpec Statement Witness Statement Unit
    OStatement (OStatement ⊕ᵥ (fun _ : Unit => WitEquiv)) where
  prover := prover oSpec Statement Witness OStatement WitEquiv equiv
  verifier := verifier oSpec Statement OStatement WitEquiv

variable (relIn : Statement × (∀ i, OStatement i) → Witness → Prop)

def toRelOut : Statement × (∀ i, (OStatement ⊕ᵥ (fun _ : Unit => WitEquiv)) i) → Unit → Prop :=
  fun ⟨stmt, oStmt⟩ _ => relIn ⟨stmt, fun i => oStmt (Sum.inl i)⟩ (equiv.invFun <| oStmt (.inr ()))

variable [oSpec.FiniteRange]

theorem completeness : OracleReduction.perfectCompleteness
    relIn
    (toRelOut Statement Witness OStatement WitEquiv equiv relIn)
    (oracleReduction oSpec Statement Witness OStatement WitEquiv equiv) := by
  sorry
  -- simp [OracleReduction.perfectCompleteness]

end SendWitness

namespace SameOracle

/-!
2. - There is no witness (e.g. `Witness = Unit`), and there is a single `OStatement`.
   - The prover sends a message of the same type as `OStatement` to the verifier.
   - The verifier performs the check for `rel`, which can be expressed as an oracle computation.
   - The output data has no `Statement`, only two `OStatement`s: one from the beginning data,
     and the other is the message from the prover.
   - The output relation checks whether the two `OStatement`s are the same.
-/

variable {ι : Type} (oSpec : OracleSpec ι) (Statement : Type)
  {ιₛᵢ : Type} [Unique ιₛᵢ] (OStatement : ιₛᵢ → Type) [inst : ∀ i, OracleInterface (OStatement i)]

@[reducible]
def pSpec : ProtocolSpec 1 := ![(.P_to_V, OStatement default)]

instance : ∀ i, OracleInterface ((pSpec OStatement).Message i)
  | ⟨0, _⟩ => by dsimp; infer_instance
instance : ∀ i, VCVCompatible ((pSpec OStatement).Challenge i) | ⟨0, h⟩ => nomatch h

/--
The prover takes in the old oracle statement as input, and sends it as the protocol message.
-/
def prover : OracleProver (pSpec OStatement) oSpec Statement Unit Unit Unit
    OStatement (OStatement ⊕ᵥ OStatement) where
  PrvState | 0 => OStatement default | 1 => OStatement default

  input := fun ⟨_, oStmt⟩ () => oStmt default

  sendMessage | ⟨0, _⟩ => fun st => pure (st, st)

  receiveChallenge | ⟨0, h⟩ => nomatch h

  output := fun st =>
    (⟨(), fun x => match x with
      | .inl _ => by simpa [Unique.uniq] using st
      | .inr default => by simpa [Unique.uniq] using st⟩,
     ())

variable (rel : Statement × (∀ i, OStatement i) → Prop)
  (relComp : Statement → OracleComp [OStatement]ₒ Unit)
  -- (rel_eq : ∀ stmt oStmt, rel stmt oStmt ↔
  --   (OracleInterface.simOracle []ₒ (OracleInterface.oracle oStmt)).run = oStmt)

/--
The verifier checks that the relationship `rel oldStmt newStmt` holds.
It has access to the original and new `OStatement` via their oracle indices.
-/
def verifier : OracleVerifier (pSpec OStatement) oSpec Statement Unit
    OStatement (OStatement ⊕ᵥ OStatement) where

  verify := fun stmt _ => relComp stmt

  embed := sorry

  hEq := sorry

/--
Combine the prover and verifier into an oracle reduction.
The input has no statement or witness, but one `OStatement`.
The output is also no statement or witness, but two `OStatement`s.
-/
def oracleReduction :
    OracleReduction (pSpec OStatement) oSpec Statement Unit Unit Unit
      OStatement (OStatement ⊕ᵥ OStatement) where
  prover := prover oSpec Statement OStatement
  verifier := verifier oSpec Statement OStatement relComp

def relOut : Unit × (∀ i, (OStatement ⊕ᵥ OStatement) i) → Unit → Prop :=
  fun ⟨(), oracles⟩ () => oracles (.inl default) = oracles (.inr default)

variable [oSpec.FiniteRange]

/--
Proof of perfect completeness: if `rel old new` holds in the real setting,
it also holds in the ideal setting, etc.
-/
theorem completeness : OracleReduction.perfectCompleteness
    (fun x _ => rel x)
    (relOut OStatement)
    (oracleReduction oSpec Statement OStatement relComp) := by
  sorry

end SameOracle

namespace RandomQuery

open OracleInterface

/-!
3. - There is no witness nor public statement. There are two `OStatement`s, `a` and `b`,
     of the same type. The relation is `a = b`.
   - The verifier samples random `q : OracleInterface.Query` for that type and sends it to the prover.
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
The prover is trivial: it has no messages to send.  It only receives the verifier’s challenge `q`.
We keep track of `(a, b)` in the prover’s state, along with the single random query `q`.
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
The final relation states that if the verifier’s single query was `q`, then
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

def stateFunction : Reduction.StateFunction
    (relIn OStatement).language (relOut OStatement).language
    (verifier oSpec OStatement).toVerifier where
  fn
  | 0 => fun ⟨_, oracles⟩ _ => oracles 0 = oracles 1
  | 1 => fun ⟨_, oracles⟩ chal =>
    let q : Query OStatement := by simpa [pSpec] using chal ⟨0, by aesop⟩
    OracleInterface.oracle (oracles 0) q = OracleInterface.oracle (oracles 1) q
  fn_empty := fun stmt hStmt => by simp_all [relIn, Function.language]
  fn_next := fun i hDir ⟨stmt, oStmt⟩ tr h => by simp_all
  fn_full := fun ⟨stmt, oStmt⟩ tr h => by
    simp_all [relOut, Function.language]
    intro a b hSupp
    simp [Verifier.run, OracleVerifier.toVerifier, verifier] at hSupp
    simp [hSupp.1, hSupp.2, h]

/-- The extractor is trivial since the output witness is `Unit`. -/
def extractor : (i : Fin 2) → @Reduction.RBRExtractor _ (pSpec OStatement) _ oSpec
    (Unit × ((i : Fin 2) → (fun _ ↦ OStatement) i)) Unit i :=
  fun _ _ _ _ => ()

-- The key fact governing the soundness of this reduction is a property of the form
-- `∀ a b : OStatement, a ≠ b → #{q | OracleInterface.oracle a q = OracleInterface.oracle b q} ≤ d`.
-- In other words, the oracle instance has distance at most `d`.

variable [Fintype (Query OStatement)] [DecidableEq (Response OStatement)]

instance : Fintype ((pSpec OStatement).Challenge ⟨0, by simp⟩) := by
  dsimp [pSpec, ProtocolSpec.Challenge]; infer_instance

open NNReal

theorem rbr_knowledge_soundness {d : ℕ} (h : OracleInterface.distanceLE OStatement d) :
    OracleReduction.rbrKnowledgeSoundness
      (relIn OStatement)
      (relOut OStatement)
      (verifier oSpec OStatement)
      (fun _ => (d : ℝ≥0) / (Fintype.card (Query OStatement) : ℝ≥0)) := by
  unfold OracleReduction.rbrKnowledgeSoundness Reduction.rbrKnowledgeSoundness
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
