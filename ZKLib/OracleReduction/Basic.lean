/-
Copyright (c) 2024 ZKLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ZKLib.OracleReduction.Prelude
import ZKLib.OracleReduction.ToOracle
-- import Mathlib.Data.FinEnum

/-!
# Interactive (Oracle) Reductions

We define (public-coin) interactive oracle reductions (IORs). This is an interactive protocol
between a prover and a verifier with the following format:

  - At the beginning, the prover and verifier both hold a public statement `x` (and potentially have
    access to some public parameters `pp`). The prover may also hold some private state which in
    particular may contain a witness `w` to the statement `x`.

  - In each round, the verifier sends some random challenges, and the prover sends back responses to
    the challenges. The responses are received as oracles by the verifier. The verifier is only
    allowed to query these oracles in specific ways.

  - At the end of the interaction, the verifier outputs a decision.

Along the way, we also define Interactive Proofs (IPs) as a special kind of IOPs where
the verifier can see the full messages. Our formalization also allows both prover and verifier
to have access to some shared oracle.

Note: the definition of IORs as defined above generalizes those found in the literature. When the
output relation is the Boolean relation (where `StmtOut = Bool`), then we recover a generalized
version of Interactive Oracle Proofs (IOPs) [BCS16]. The particular IOP considered in [BCS16] may be
called "point IOP" due to its query structure. We also get "polynomial IOP" [BCG+19] and "tensor
IOP" [BCG20] (and other kinds of IOPs) from our definition.

-/

open OracleComp OracleSpec SubSpec

section Format

/-- Type signature for an interactive protocol, with `n` messages exchanged. -/
@[reducible]
def ProtocolSpec (n : ℕ) := Fin n → Direction × Type

variable {n : ℕ}

namespace ProtocolSpec

abbrev getDir (pSpec : ProtocolSpec n) (i : Fin n) := pSpec i |>.1

abbrev getType (pSpec : ProtocolSpec n) (i : Fin n) := pSpec i |>.2

/-- We set the rewrite to follow `getDir` instead of `Prod.fst`? -/
@[simp]
theorem getDir_apply (pSpec : ProtocolSpec n) (i : Fin n) : pSpec.getDir i = (pSpec i).1 := rfl

@[simp]
theorem getType_apply (pSpec : ProtocolSpec n) (i : Fin n) : pSpec.getType i = (pSpec i).2 := rfl

/-- Subtype of `Fin n` for the indices corresponding to messages in a protocol specification -/
@[reducible]
def MessageIndex (pSpec : ProtocolSpec n) :=
  {i : Fin n // (pSpec i).1 = Direction.P_to_V}

/-- Subtype of `Fin n` for the indices corresponding to challenges in a protocol specification -/
@[reducible]
def ChallengeIndex (pSpec : ProtocolSpec n) :=
  {i : Fin n // (pSpec i).1 = Direction.V_to_P}

instance {pSpec : ProtocolSpec n} : CoeHead (MessageIndex pSpec) (Fin n) where
  coe := fun i => i.1
instance {pSpec : ProtocolSpec n} : CoeHead (ChallengeIndex pSpec) (Fin n) where
  coe := fun i => i.1

/-- The type of the `i`-th message in a protocol specification -/
@[reducible, inline, specialize]
def Message (pSpec : ProtocolSpec n) (i : MessageIndex pSpec) :=
  pSpec.getType i.val

/-- The type of the `i`-th challenge in a protocol specification -/
@[reducible, inline, specialize]
def Challenge (pSpec : ProtocolSpec n) (i : ChallengeIndex pSpec) :=
  pSpec.getType i.val

/-- There is only one protocol specification with 0 messages (the empty one) -/
instance : Unique (ProtocolSpec 0) := inferInstance

/-- A (partial) transcript of a protocol specification, indexed by some `k : Fin (n + 1)`, is a
    list of messages from the protocol for all indices `i` less than `k`. -/
@[reducible, inline, specialize]
def Transcript (k : Fin (n + 1)) (pSpec : ProtocolSpec n) :=
  (i : Fin k) → pSpec.getType (Fin.castLE (by omega) i)

instance {k : Fin 1} : Unique (Transcript k (default : ProtocolSpec 0)) where
  default := fun i => ()
  uniq := by solve_by_elim

instance {pSpec : ProtocolSpec n} : Unique (Transcript 0 pSpec) where
  default := fun i => Fin.elim0 i
  uniq := fun T => by ext i; exact Fin.elim0 i

/-- The full transcript of an interactive protocol, which is a list of messages and challenges -/
@[reducible, inline, specialize]
def FullTranscript (pSpec : ProtocolSpec n) := (i : Fin n) → pSpec.getType i

/-- There is only one full transcript (the empty one) for an empty protocol -/
instance : Unique (FullTranscript (default : ProtocolSpec 0)) := inferInstance

variable {pSpec : ProtocolSpec n}

-- instance instFinEnumMessageIndex : FinEnum pSpec.MessageIndex :=
--   FinEnum.Subtype.finEnum fun x ↦ pSpec.getDir x = Direction.P_to_V
-- instance instFinEnumChallengeIndex : FinEnum pSpec.ChallengeIndex :=
--   FinEnum.Subtype.finEnum fun x ↦ pSpec.getDir x = Direction.V_to_P

/-- Nicely, a transcript up to the last round of the protocol is definitionally equivalent to a full
    transcript. -/
@[inline]
abbrev Transcript.toFull (T : Transcript (Fin.last n) pSpec) : FullTranscript pSpec := T

/-- Add a message to the end of a partial transcript. This is definitionally equivalent to
    `Fin.snoc`. -/
@[inline]
abbrev Transcript.snoc {m : Fin n} (msg : pSpec.getType m)
    (T : Transcript m.castSucc pSpec) : Transcript m.succ pSpec := Fin.snoc T msg

@[reducible, inline, specialize]
def FullTranscript.messages (transcript : FullTranscript pSpec) (i : MessageIndex pSpec) :=
  transcript i.val

@[reducible, inline, specialize]
def FullTranscript.challenges (transcript : FullTranscript pSpec) (i : ChallengeIndex pSpec) :=
  transcript i.val

/-- Turn each verifier's challenge into an oracle, where querying a unit type gives back the
  challenge -/
@[reducible, inline, specialize]
instance instChallengeToOracle {pSpec : ProtocolSpec n} {i : pSpec.ChallengeIndex} :
    ToOracle (pSpec.Challenge i) where
  Query := Unit
  Response := pSpec.Challenge i
  oracle := fun c _ => c

@[reducible, inline, specialize]
def getChallenge (pSpec : ProtocolSpec n) (i : pSpec.ChallengeIndex) :
    OracleComp [pSpec.Challenge]ₒ (pSpec.Challenge i) :=
  (query i () : OracleQuery [pSpec.Challenge]ₒ (pSpec.Challenge i))

end ProtocolSpec

open ProtocolSpec

-- Notation for the type signature of an interactive protocol
notation "𝒫——⟦" term "⟧⟶𝒱" => (Direction.P_to_V, term)
notation "𝒫⟵⟦" term "⟧——𝒱" => (Direction.V_to_P, term)

variable {ι : Type}

-- Add an indexer?
structure Indexer (pSpec : ProtocolSpec n) (oSpec : OracleSpec ι) (Index : Type)
    (Encoding : Type) where
  encode : Index → OracleComp oSpec Encoding
  [toOracle : ToOracle Encoding]

/-- The type signature for the prover's state at each round. For a protocol with `n` messages
  exchanged, there will be `(n + 1)` prover states, with the first state before the first message
  and the last state after the last message. -/
structure ProverState (n : ℕ) where
  PrvState : Fin (n + 1) → Type

  -- if honest prover, then expect that PrvState 0 = WitIn
  -- initState : PrvState 0

/-- Initialization of prover's state via inputting the statement and witness -/
structure ProverIn (StmtIn WitIn PrvState : Type) where
  input : StmtIn → WitIn → PrvState

/-- Represents the interaction of a prover for a given protocol specification.

In each step, the prover gets access to the current state, then depending on the direction of the
step, the prover either sends a message or receives a challenge, and updates its state accordingly.

For maximum simplicity, we only define the `sendMessage` function as an oracle computation. All
other functions are pure. We may revisit this decision in the future.
-/
structure ProverRound (pSpec : ProtocolSpec n) (oSpec : OracleSpec ι)
    extends ProverState n where
  /-- Send a message and update the prover's state -/
  sendMessage (i : MessageIndex pSpec) :
    PrvState i.1.castSucc → OracleComp oSpec (pSpec.Message i × PrvState i.1.succ)
  /-- Receive a challenge and update the prover's state -/
  receiveChallenge (i : ChallengeIndex pSpec) :
    PrvState i.1.castSucc → (pSpec.Challenge i) → PrvState i.1.succ

/-- The output of the prover, which is a function from the prover's state to the output witness -/
structure ProverOut (StmtOut WitOut PrvState : Type) where
  output : PrvState → StmtOut × WitOut

/-- A prover for an interactive protocol with `n` messages consists of a sequence of internal states
    and a tuple of four functions:
  - `PrvState 0`, ..., `PrvState n` are the types for the prover's state at each round
  - `input` initializes the prover's state by taking in the input statement and witness
  - `receiveChallenge` updates the prover's state given a challenge
  - `sendMessage` sends a message and updates the prover's state
  - `output` returns the output statement and witness from the prover's state

Note that the output statement by the prover is present only to facilitate composing two provers
together. For completeness, we will require that the prover's output statement is always equal to
the verifier's output statement. For soundness, we will only use the output statement generated by
the verifier. -/
structure Prover (pSpec : ProtocolSpec n) (oSpec : OracleSpec ι)
    (StmtIn WitIn StmtOut WitOut : Type) extends
      ProverState n,
      ProverIn StmtIn WitIn (PrvState 0),
      ProverRound pSpec oSpec,
      ProverOut StmtOut WitOut (PrvState (Fin.last n))

/-- A verifier of an interactive protocol is a function that takes in the input statement and the
  transcript, and performs an oracle computation that outputs a new statement -/
structure Verifier (pSpec : ProtocolSpec n) (oSpec : OracleSpec ι) (StmtIn StmtOut : Type) where
  verify : StmtIn → FullTranscript pSpec → OracleComp oSpec StmtOut

/-- A prover in an interactive **oracle** reduction is a prover in the non-oracle reduction whose
    input statement also consists of the underlying messages for the oracle statements -/
@[reducible, inline]
def OracleProver (pSpec : ProtocolSpec n) (oSpec : OracleSpec ι)
    (StmtIn WitIn StmtOut WitOut : Type)
    {ιₛᵢ : Type} (OStmtIn : ιₛᵢ → Type) {ιₛₒ : Type} (OStmtOut : ιₛₒ → Type) :=
  Prover pSpec oSpec (StmtIn × (∀ i, OStmtIn i)) WitIn (StmtOut × (∀ i, OStmtOut i)) WitOut

/--
A verifier of an interactive **oracle** reduction consists of:
  - an oracle computation `verify` that may make queries to each of the prover's messages and each
    of the oracles present in the statement (according to a specified interface defined by
    `ToOracle` instances).
  - output oracle statements `OStmtOut : ιₛₒ → Type`
  - an embedding `ιₛₒ ↪ ιₛᵢ ⊕ pSpec.MessageIndex`
  - a proof that the output oracle statements are a subset of the oracles present in the statement

The reason for the output indexing type & the embedding is that, since the verifier only gets oracle
access to the oracle statement & the prover's messages, its output oracle statements can only be a
subset of the oracles it has seen so far. -/
structure OracleVerifier (pSpec : ProtocolSpec n) (oSpec : OracleSpec ι)
    [Oₘ : ∀ i, ToOracle (pSpec.Message i)] (StmtIn StmtOut : Type)
    {ιₛᵢ : Type} (OStmtIn : ιₛᵢ → Type) [Oₛᵢ : ∀ i, ToOracle (OStmtIn i)]
    {ιₛₒ : Type} (OStmtOut : ιₛₒ → Type) where

  verify : StmtIn → (∀ i, pSpec.Challenge i) →
    OracleComp (oSpec ++ₒ ([OStmtIn]ₒ ++ₒ [pSpec.Message]ₒ)) StmtOut

  embed : ιₛₒ ↪ ιₛᵢ ⊕ pSpec.MessageIndex

  hEq : ∀ i, OStmtOut i = match embed i with
    | Sum.inl j => OStmtIn j
    | Sum.inr j => pSpec.Message j

-- Cannot find synthesization order...
-- instance {ιₛᵢ ιₘ ιₛₒ : Type} {OStmtIn : ιₛᵢ → Type} [Oₛᵢ : ∀ i, ToOracle (OStmtIn i)]
--     {Message : ιₘ → Type} [Oₘ : ∀ i, ToOracle (Message i)]
--     (OStmtOut : ιₛₒ → Type) (embed : ιₛₒ ↪ ιₛᵢ ⊕ ιₘ) :
--     ∀ i, OStmtOut i := fun i => by sorry

namespace OracleVerifier

variable {pSpec : ProtocolSpec n} {oSpec : OracleSpec ι}
    [Oₘ : ∀ i, ToOracle (pSpec.Message i)] {StmtIn StmtOut : Type}
    {ιₛᵢ : Type} {OStmtIn : ιₛᵢ → Type} [Oₛᵢ : ∀ i, ToOracle (OStmtIn i)]
    {ιₛₒ : Type} {OStmtOut : ιₛₒ → Type}
    (verifier : OracleVerifier pSpec oSpec StmtIn StmtOut OStmtIn OStmtOut)

/-- An oracle verifier can be seen as a (non-oracle) verifier by providing the oracle interface
  using its knowledge of the oracle statements and the transcript messages in the clear -/
def toVerifier : Verifier pSpec oSpec (StmtIn × ∀ i, OStmtIn i) (StmtOut × (∀ i, OStmtOut i)) where
  verify := fun ⟨stmt, oStmt⟩ transcript => do
    let stmtOut ← simulateQ (ToOracle.simOracle2 oSpec oStmt transcript.messages)
      (verifier.verify stmt transcript.challenges)
    letI oStmtOut := fun i => match h : verifier.embed i with
      | Sum.inl j => by simpa only [verifier.hEq, h] using (oStmt j)
      | Sum.inr j => by simpa only [verifier.hEq, h] using (transcript j)
    return (stmtOut, oStmtOut)

end OracleVerifier

/-- An **interactive reduction** for a given protocol specification `pSpec`, and relative to oracles
  defined by `oSpec`, consists of a prover and a verifier. -/
structure Reduction (pSpec : ProtocolSpec n) (oSpec : OracleSpec ι)
    (StmtIn WitIn StmtOut WitOut : Type) where
  prover : Prover pSpec oSpec StmtIn WitIn StmtOut WitOut
  verifier : Verifier pSpec oSpec StmtIn StmtOut

/-- An **interactive oracle reduction** for a given protocol specification `pSpec`, and relative to
  oracles defined by `oSpec`, consists of a prover and an **oracle** verifier. -/
structure OracleReduction (pSpec : ProtocolSpec n) [∀ i, ToOracle (pSpec.Message i)]
    (oSpec : OracleSpec ι) (StmtIn WitIn StmtOut WitOut : Type)
    {ιₛ : Type} (OStmtIn : ιₛ → Type) [Oₛ : ∀ i, ToOracle (OStmtIn i)]
    {ιₛₒ : Type} (OStmtOut : ιₛₒ → Type) where
  prover : OracleProver pSpec oSpec StmtIn WitIn StmtOut WitOut OStmtIn OStmtOut
  verifier : OracleVerifier pSpec oSpec StmtIn StmtOut OStmtIn OStmtOut

/-- An interactive oracle reduction can be seen as an interactive reduction, via coercing the
  oracle verifier to a (normal) verifier -/
def OracleReduction.toReduction {pSpec : ProtocolSpec n} {oSpec : OracleSpec ι}
    {StmtIn WitIn StmtOut WitOut : Type} [∀ i, ToOracle (pSpec.Message i)]
    {ιₛ : Type} {OStmtIn : ιₛ → Type} [Oₛ : ∀ i, ToOracle (OStmtIn i)]
    {ιₛₒ : Type} {OStmtOut : ιₛₒ → Type}
    (oracleReduction : OracleReduction pSpec oSpec StmtIn WitIn StmtOut WitOut OStmtIn OStmtOut) :
      Reduction pSpec oSpec (StmtIn × (∀ i, OStmtIn i)) WitIn
        (StmtOut × (∀ i, OStmtOut i)) WitOut :=
  ⟨oracleReduction.prover, oracleReduction.verifier.toVerifier⟩

/-- An **interactive proof (IP)** is an interactive reduction where the output statement is a
    boolean, the output witness is trivial (a `Unit`), and the relation checks whether the output
    statement is true. -/
abbrev Proof (pSpec : ProtocolSpec n) (oSpec : OracleSpec ι) (Statement Witness : Type) :=
  Reduction pSpec oSpec Statement Witness Bool Unit

/-- An **interactive oracle proof (IOP)** is an interactive oracle reduction where the output
    statement is a boolean, while both the output oracle statement & the output witness are
    trivial (`Unit` type).

    As a consequence, the output relation in an IOP is effectively a function `Bool → Prop`, which
    we can again assume to be the trivial one (sending `true` to `True`). -/
abbrev OracleProof (pSpec : ProtocolSpec n) (oSpec : OracleSpec ι)
    [Oₘ : ∀ i, ToOracle (pSpec.Message i)] (Statement Witness : Type)
    {ιₛ : Type} (OStatement : ιₛ → Type) [Oₛ : ∀ i, ToOracle (OStatement i)] :=
  OracleReduction pSpec oSpec Statement Witness Bool Unit OStatement (fun _ : Empty => Unit)

abbrev NonInteractiveProver (oSpec : OracleSpec ι)
    (StmtIn WitIn StmtOut WitOut : Type) (Message : Type) :=
  Prover ![(.P_to_V, Message)] oSpec StmtIn WitIn StmtOut WitOut

abbrev NonInteractiveVerifier (oSpec : OracleSpec ι) (StmtIn StmtOut : Type) (Message : Type) :=
  Verifier ![(.P_to_V, Message)] oSpec StmtIn StmtOut

/-- A **non-interactive reduction** is an interactive reduction with only a single message from the
  prover to the verifier (and none in the other direction). -/
abbrev NonInteractiveReduction (oSpec : OracleSpec ι)
    (StmtIn WitIn StmtOut WitOut : Type) (Message : Type) :=
  Reduction ![(.P_to_V, Message)] oSpec StmtIn WitIn StmtOut WitOut

end Format

section Stateless

open ProtocolSpec

-- Here we define the stateless form of an (oracle) reduction, where both the prover and the
-- verifier does not maintain any state. This is useful for specification purposes, as it reduces
-- the protocol to a more pure form. In this stateless form, the context (witness + statement +
-- oracle statement) is append-only

variable {n : ℕ} {ι : Type}

-- TODO: figure out if we should go with a `Context` struct like this

structure ContextType (ιS : Type) (ιO : Type) (ιW : Type) where
  Statement : ιS → Type
  OracleStatement : ιO → Type
  Witness : ιW → Type

def ContextType.toType {ιS ιO ιW : Type} (CtxType : ContextType ιS ιO ιW) : Type :=
  (∀ i, CtxType.Statement i) × (∀ i, CtxType.OracleStatement i) × (∀ i, CtxType.Witness i)

structure Context {ιS ιO ιW : Type} (CtxType : ContextType ιS ιO ιW) where
  statement : ∀ i, CtxType.Statement i
  oracleStatement : ∀ i, CtxType.OracleStatement i
  witness : ∀ i, CtxType.Witness i
  [toOracle : ∀ i, ToOracle (CtxType.OracleStatement i)]

structure Prover.Stateless (pSpec : ProtocolSpec n) (oSpec : OracleSpec ι)
    (Statement Witness : Type) where
  prove (i : pSpec.MessageIndex) : Statement → Witness →
    Transcript i.1.castSucc pSpec → OracleComp oSpec (pSpec.Message i)

-- #print Prover.Stateless

/-- In a stateless form prover, the output statement is simply the input statement concatenated with
    the transcript, the output witness stays the same, and the prover's state is the partial
    transcript. -/
def Prover.ofStateless {pSpec : ProtocolSpec n} {oSpec : OracleSpec ι}
    {Statement Witness : Type}
    (P : Prover.Stateless pSpec oSpec Statement Witness) :
      Prover pSpec oSpec Statement Witness (Statement × FullTranscript pSpec) Witness where
  PrvState := fun i => Statement × Transcript i pSpec × Witness
  input := fun stmt wit => ⟨stmt, default, wit⟩
  sendMessage := fun i ⟨stmt, transcript, wit⟩ => do
    let msg ← P.prove i stmt wit transcript
    return (msg, ⟨stmt, transcript.snoc msg, wit⟩)
  receiveChallenge := fun _ ⟨stmt, transcript, wit⟩ chal => ⟨stmt, transcript.snoc chal, wit⟩
  output := fun ⟨stmt, transcript, wit⟩ => ⟨⟨stmt, transcript⟩, wit⟩

@[reducible]
def OracleProver.Stateless (pSpec : ProtocolSpec n) (oSpec : OracleSpec ι)
    (Statement : Type) {ιₛᵢ : Type} (OStatement : ιₛᵢ → Type) (Witness : Type) :=
  Prover.Stateless pSpec oSpec (Statement × (∀ i, OStatement i)) Witness

def OracleProver.ofStateless {pSpec : ProtocolSpec n} {oSpec : OracleSpec ι}
    {Statement : Type} {ιₛᵢ : Type} {OStatement : ιₛᵢ → Type} {Witness : Type}
    (P : OracleProver.Stateless pSpec oSpec Statement OStatement Witness) :
      OracleProver pSpec oSpec Statement Witness (Statement × (∀ i, pSpec.Challenge i)) Witness
        OStatement (Sum.elim OStatement pSpec.Message) :=
  -- by simpa [OracleProver] using Prover.ofStateless P
  sorry

/-- A verifier in a stateless form only performs checks (i.e. `guard`s) on the input statement and
  transcript -/
structure Verifier.Stateless (pSpec : ProtocolSpec n) (oSpec : OracleSpec ι) (Statement : Type)
    where
  verify : Statement → FullTranscript pSpec → OracleComp oSpec Unit

def Verifier.ofStateless {pSpec : ProtocolSpec n} {oSpec : OracleSpec ι}
    {Statement : Type} (V : Verifier.Stateless pSpec oSpec Statement) :
      Verifier pSpec oSpec Statement (Statement × FullTranscript pSpec) where
  verify := fun stmt transcript => do
    -- First perform the guard check, then return the statement and transcript
    let _ ← V.verify stmt transcript
    return (stmt, transcript)

/-- An oracle verifier in a stateless form only performs checks (i.e. `guard`s) on the input
    statement and transcript -/
structure OracleVerifier.Stateless (pSpec : ProtocolSpec n) (oSpec : OracleSpec ι)
    (Statement : Type) {ιₛᵢ : Type} (OStatement : ιₛᵢ → Type)
    [Oₛᵢ : ∀ i, ToOracle (OStatement i)] [Oₘ : ∀ i, ToOracle (pSpec.Message i)] where
  verify : Statement → (∀ i, pSpec.Challenge i) →
    OracleComp (oSpec ++ₒ ([OStatement]ₒ ++ₒ [pSpec.Message]ₒ)) Unit

def OracleVerifier.ofStateless {pSpec : ProtocolSpec n} {oSpec : OracleSpec ι}
    {Statement : Type} {ιₛᵢ : Type} {OStatement : ιₛᵢ → Type}
    [Oₛᵢ : ∀ i, ToOracle (OStatement i)] [Oₘ : ∀ i, ToOracle (pSpec.Message i)]
    (V : OracleVerifier.Stateless pSpec oSpec Statement OStatement) :
      OracleVerifier pSpec oSpec Statement (Statement × ∀ i, pSpec.Challenge i) OStatement
        (ιₛₒ := ιₛᵢ ⊕ pSpec.MessageIndex) (Sum.elim OStatement pSpec.Message) where
  verify := fun stmt challenges => do
    -- First perform the guard check, then return the statement and transcript
    let _ ← V.verify stmt challenges
    return (stmt, challenges)

  embed := Function.Embedding.refl _

  hEq := fun i => by aesop

structure Reduction.Stateless (pSpec : ProtocolSpec n) (oSpec : OracleSpec ι)
    (Statement Witness : Type) where
  prover : Prover.Stateless pSpec oSpec Statement Witness
  verifier : Verifier.Stateless pSpec oSpec Statement

def Reduction.ofStateless {pSpec : ProtocolSpec n} {oSpec : OracleSpec ι}
    {Statement Witness : Type} (R : Reduction.Stateless pSpec oSpec Statement Witness) :
      Reduction pSpec oSpec Statement Witness (Statement × FullTranscript pSpec) Witness where
  prover := Prover.ofStateless R.prover
  verifier := Verifier.ofStateless R.verifier

structure OracleReduction.Stateless (pSpec : ProtocolSpec n) (oSpec : OracleSpec ι)
    (Statement : Type) {ιₛᵢ : Type} (OStatement : ιₛᵢ → Type) (Witness : Type)
    [Oₛᵢ : ∀ i, ToOracle (OStatement i)] [Oₘ : ∀ i, ToOracle (pSpec.Message i)] where
  prover : OracleProver.Stateless pSpec oSpec Statement OStatement Witness
  verifier : OracleVerifier.Stateless pSpec oSpec Statement OStatement

def Prover.Stateless.runToRound {pSpec : ProtocolSpec n} {oSpec : OracleSpec ι}
    -- {CtxType : ReductionContextType} {Ctx : ReductionContext CtxType}
    {Statement Witness : Type}
    (stmt : Statement) (wit : Witness) (i : Fin (n + 1))
    (P : Prover.Stateless pSpec oSpec Statement Witness) :
      OracleComp (oSpec ++ₒ [pSpec.Challenge]ₒ) (pSpec.Transcript i) :=
  Fin.inductionOn i (pure default)
    (fun j ih => match hDir : (pSpec j).1 with
    | .P_to_V => do
      let transcript ← ih
      let msg ← P.prove ⟨j, hDir⟩ stmt wit transcript
      return (← ih).snoc msg
    | .V_to_P => do
      let chal ← query (spec := [pSpec.Challenge]ₒ) ⟨j, hDir⟩ ()
      return (← ih).snoc chal)

end Stateless

section Classes

namespace ProtocolSpec

variable {n : ℕ}

/-- A protocol specification with the prover speaking first -/
class ProverFirst (pSpec : ProtocolSpec n) [NeZero n] where
  prover_first' : (pSpec 0).1 = .P_to_V

class VerifierFirst (pSpec : ProtocolSpec n) [NeZero n] where
  verifier_first' : (pSpec 0).1 = .V_to_P

class ProverLast (pSpec : ProtocolSpec n) [NeZero n] where
  prover_last' : (pSpec (n - 1)).1 = .P_to_V

/-- A protocol specification with the verifier speaking last -/
class VerifierLast (pSpec : ProtocolSpec n) [NeZero n] where
  verifier_last' : (pSpec (n - 1)).1 = .V_to_P

class ProverOnly (pSpec : ProtocolSpec 1) extends ProverFirst pSpec

/-- A non-interactive protocol specification with a single message from the prover to the verifier-/
alias NonInteractive := ProverOnly

class VerifierOnly (pSpec : ProtocolSpec 1) extends VerifierFirst pSpec

@[simp]
theorem prover_first (pSpec : ProtocolSpec n) [NeZero n] [h : ProverFirst pSpec] :
    (pSpec 0).1 = .P_to_V := h.prover_first'

@[simp]
theorem verifier_first (pSpec : ProtocolSpec n) [NeZero n] [h : VerifierFirst pSpec] :
    (pSpec 0).1 = .V_to_P := h.verifier_first'

@[simp]
theorem prover_last (pSpec : ProtocolSpec n) [NeZero n] [h : ProverLast pSpec] :
    (pSpec (n - 1)).1 = .P_to_V := h.prover_last'

@[simp]
theorem verifier_last (pSpec : ProtocolSpec n) [NeZero n] [h : VerifierLast pSpec] :
    (pSpec (n - 1)).1 = .V_to_P := h.verifier_last'

section SingleMessage

variable {pSpec : ProtocolSpec 1}

--  For protocols with a single message, first and last are the same
instance [ProverFirst pSpec] : ProverLast pSpec where
  prover_last' := by simp
instance [VerifierFirst pSpec] : VerifierLast pSpec where
  verifier_last' := by simp
instance [h : ProverLast pSpec] : ProverFirst pSpec where
  prover_first' := by simpa using h.prover_last'
instance [h : VerifierFirst pSpec] : VerifierFirst pSpec where
  verifier_first' := by simp

instance [ProverFirst pSpec] : Unique (pSpec.MessageIndex) where
  default := ⟨0, by simp⟩
  uniq := fun ⟨i, _⟩ => by congr; exact Unique.uniq _ i

instance [VerifierFirst pSpec] : Unique (pSpec.ChallengeIndex) where
  default := ⟨0, by simp⟩
  uniq := fun ⟨i, _⟩ => by congr; exact Unique.uniq _ i

instance [h : ProverFirst pSpec] : IsEmpty (pSpec.ChallengeIndex) where
  false | ⟨0, h'⟩ => by have := h.prover_first'; simp_all

instance [h : VerifierFirst pSpec] : IsEmpty (pSpec.MessageIndex) where
  false | ⟨0, h'⟩ => by have := h.verifier_first'; simp_all

instance [ProverFirst pSpec] : ∀ i, VCVCompatible (pSpec.Challenge i) := isEmptyElim
instance [VerifierFirst pSpec] : ∀ i, ToOracle (pSpec.Message i) := isEmptyElim

instance [ProverFirst pSpec] [h : ToOracle (pSpec 0).2] : ∀ i, ToOracle (pSpec.Message i)
  | ⟨0, _⟩ => inferInstance
instance [VerifierFirst pSpec] [h : VCVCompatible (pSpec 0).2] :
    ∀ i, VCVCompatible (pSpec.Challenge i)
  | ⟨0, _⟩ => inferInstance

end SingleMessage

@[simp]
theorem prover_last_of_two (pSpec : ProtocolSpec 2) [ProverLast pSpec] :
    pSpec.getDir 1 = .P_to_V := prover_last pSpec

@[simp]
theorem verifier_last_of_two (pSpec : ProtocolSpec 2) [VerifierLast pSpec] :
    pSpec.getDir 1 = .V_to_P := verifier_last pSpec

/-- A protocol specification with a single round of interaction consisting of two messages, with the
  prover speaking first and the verifier speaking last

This notation is currently somewhat ambiguous, given that there are other valid ways of defining a
"single-round" protocol, such as letting the verifier speaks first, letting the prover speaks
multiple times, etc. -/
class IsSingleRound (pSpec : ProtocolSpec 2) extends ProverFirst pSpec, VerifierLast pSpec

alias ProverThenVerifier := IsSingleRound

namespace IsSingleRound

variable {pSpec : ProtocolSpec 2}

/-- The first message is the only message from the prover to the verifier -/
instance [IsSingleRound pSpec] : Unique (pSpec.MessageIndex) where
  default := ⟨0, by simp⟩
  uniq := fun ⟨i, hi⟩ => by
    congr
    contrapose! hi
    have : i = 1 := by omega
    subst this
    simp only [verifier_last_of_two, ne_eq, reduceCtorEq, not_false_eq_true]

/-- The second message is the only challenge from the verifier to the prover -/
instance [IsSingleRound pSpec] : Unique (pSpec.ChallengeIndex) where
  default := ⟨1, by simp⟩
  uniq := fun ⟨i, hi⟩ => by
    congr
    contrapose! hi
    have : i = 0 := by omega
    subst this
    simp only [prover_first, ne_eq, reduceCtorEq, not_false_eq_true]

instance [IsSingleRound pSpec] [h : ToOracle (pSpec.Message default)] :
    (i : pSpec.MessageIndex) → ToOracle (pSpec.Message i) := fun i => by
  haveI : i = default := Unique.uniq _ i
  subst this
  exact h

instance [IsSingleRound pSpec] [h : VCVCompatible (pSpec.Challenge default)] :
    (i : pSpec.ChallengeIndex) → VCVCompatible (pSpec.Challenge i) := fun i => by
  haveI : i = default := Unique.uniq _ i
  subst this
  exact h

end IsSingleRound

@[inline, reducible]
def FullTranscript.mk2 {pSpec : ProtocolSpec 2} (msg0 : pSpec.getType 0) (msg1 : pSpec.getType 1) :
    FullTranscript pSpec := fun | ⟨0, _⟩ => msg0 | ⟨1, _⟩ => msg1

theorem FullTranscript.mk2_eq_snoc_snoc {pSpec : ProtocolSpec 2} (msg0 : pSpec.getType 0)
    (msg1 : pSpec.getType 1) :
      FullTranscript.mk2 msg0 msg1 = ((default : pSpec.Transcript 0).snoc msg0).snoc msg1 := by
  unfold FullTranscript.mk2 Transcript.snoc
  simp only [default, getType_apply, Nat.mod_succ, Nat.lt_one_iff,
    not_lt_zero', ↓reduceDIte, Fin.zero_eta, Fin.isValue, Nat.reduceMod, Nat.succ_eq_add_one,
    Nat.reduceAdd, Fin.mk_one]
  funext i
  by_cases hi : i = 0
  · subst hi; simp [Fin.snoc]
  · have : i = 1 := by omega
    subst this; simp [Fin.snoc]

end ProtocolSpec

section IsPure

variable {n : ℕ} {ι : Type} {pSpec : ProtocolSpec n} {oSpec : OracleSpec ι}
    {StmtIn WitIn StmtOut WitOut : Type}

class Prover.IsPure (P : Prover pSpec oSpec StmtIn WitIn StmtOut WitOut) where
    is_pure : ∃ sendMessage : ∀ _, _ → _, ∀ i st,
      P.sendMessage i st = pure (sendMessage i st)

class Verifier.IsPure (V : Verifier pSpec oSpec StmtIn StmtOut) where
    is_pure : ∃ verify : _ → _ → _, ∀ stmtIn transcript,
      V.verify stmtIn transcript = pure (verify stmtIn transcript)

class Reduction.IsPure (R : Reduction pSpec oSpec StmtIn WitIn StmtOut WitOut) where
    prover_is_pure : R.prover.IsPure
    verifier_is_pure : R.verifier.IsPure

end IsPure

end Classes
