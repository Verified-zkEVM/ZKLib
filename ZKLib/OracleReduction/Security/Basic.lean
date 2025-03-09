/-
Copyright (c) 2024 ZKLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ZKLib.OracleReduction.Execution

/-!
  # Security Definitions for IOR

  We define the following security properties for IOR:

  - Completeness.

  - (Knowledge) Soundness: We define many variants of soundness and knowledge soundness, including
    - (Standard) soundness
    - State-restoration soundness
    - Round-by-round soundness
  All definitions are in the adaptive prover setting.

  - Zero-knowledge: This will be defined in the future
-/

noncomputable section

namespace Reduction

open OracleComp OracleSpec ProtocolSpec
open scoped NNReal

variable {n : ℕ} {ι : Type} {pSpec : ProtocolSpec n} {oSpec : OracleSpec ι}
    {StmtIn WitIn StmtOut WitOut : Type} [∀ i, VCVCompatible (pSpec.Challenge i)]

section Completeness

variable [oSpec.FiniteRange]

/--
  A reduction satisfies **completeness** with error `completenessError ≥ 0` and with respect to
  input relation `relIn` and output relation `relOut`, if for all valid statement-witness pair
  `(stmtIn, witIn)` for `relIn`, the execution between the honest prover and the honest verifier
  will result in a valid pair `(stmtOut, witOut)` for `relOut`, except with probability
  `completenessError`.
-/

def completeness (relIn : StmtIn → WitIn → Prop)
    (relOut : StmtOut → WitOut → Prop)
    (reduction : Reduction pSpec oSpec StmtIn WitIn StmtOut WitOut)
    (completenessError : ℝ≥0) : Prop :=
  ∀ stmtIn : StmtIn,
  ∀ witIn : WitIn,
  relIn stmtIn witIn →
    [fun ⟨stmtOut, witOut, _⟩ => relOut stmtOut witOut
    | reduction.run stmtIn witIn] ≥ 1 - completenessError

/-- A reduction satisfies **perfect completeness** if it satisfies completeness with error `0`. -/
def perfectCompleteness (relIn : StmtIn → WitIn → Prop) (relOut : StmtOut → WitOut → Prop)
    (reduction : Reduction pSpec oSpec StmtIn WitIn StmtOut WitOut) : Prop :=
  completeness relIn relOut reduction 0

variable {relIn : StmtIn → WitIn → Prop} {relOut : StmtOut → WitOut → Prop}
    {reduction : Reduction pSpec oSpec StmtIn WitIn StmtOut WitOut}

/-- Perfect completeness means that the probability of the reduction outputting a valid
  statement-witness pair is _exactly_ 1 (instead of at least `1 - 0`). -/
@[simp]
theorem perfectCompleteness_eq_prob_one :
    reduction.perfectCompleteness relIn relOut ↔
      ∀ stmtIn witIn, relIn stmtIn witIn →
        [fun ⟨stmtOut, witOut, _⟩ => relOut stmtOut witOut
        | reduction.run stmtIn witIn] = 1 := by
  refine forall_congr' fun stmtIn => forall_congr' fun stmtOut => forall_congr' fun _ => ?_
  rw [ENNReal.coe_zero, tsub_zero, ge_iff_le, one_le_probEvent_iff,
    probEvent_eq_one_iff, Prod.forall]

-- /-- For a reduction without shared oracles (i.e. `oSpec = []ₒ`), perfect completeness occurs
--   when the reduction produces satisfying statement-witness pairs for all possible challenges. -/
-- theorem perfectCompleteness_forall_challenge [reduction.IsDeterministic] :
--       reduction.perfectCompleteness relIn relOut ↔
--         ∀ stmtIn witIn, relIn stmtIn witIn → ∀ chals : ∀ i, pSpec.Challenge i,
--           reduction.runWithChallenges stmtIn witIn chals = 1 := by


end Completeness

section Soundness

variable [oSpec.FiniteRange]

/- We define 3 variants each of soundness and knowledge soundness, all in the adaptive setting: (our
  definitions are automatically in the adaptive setting, since there is no `crs`?)

  1. (Plain) soundness
  2. Knowledge soundness
  3. State-restoration soundness
  4. State-restoration knowledge soundness
  5. Round-by-round soundness
  6. Round-by-round knowledge soundness
-/

/-- It's not clear whether we need the stronger `AdaptiveProver` type, since the soundness notions
  are stated with regards to an arbitrary statement anyway (for plain soundness, the statement is
  arbitrary among the ones that are not in the language). -/
structure AdaptiveProver (pSpec : ProtocolSpec n) (oSpec : OracleSpec ι)
    (StmtIn WitIn StmtOut WitOut : Type) extends Prover pSpec oSpec StmtIn WitIn StmtOut WitOut
    where
  chooseStmtIn : OracleComp oSpec StmtIn

/--
  A reduction satisfies **soundness** with error `soundnessError ≥ 0` and with respect to input
  language `langIn : Set StmtIn` and output language `langOut : Set StmtOut`, if for all input
  statment `stmtIn ∉ langIn`, all (malicious) provers with arbitrary types for `WitIn`, `WitOut`,
  and `PrvState`, and all arbitrary `witIn`, the execution between the prover and the honest
  verifier will result in an output statement `stmtOut` that is not in `langOut`, except with
  probability `soundnessError`.
-/
def soundness (langIn : Set StmtIn) (langOut : Set StmtOut)
    (verifier : Verifier pSpec oSpec StmtIn StmtOut)
    (soundnessError : ℝ≥0) : Prop :=
  ∀ WitIn WitOut : Type,
  ∀ witIn : WitIn,
  ∀ prover : Prover pSpec oSpec StmtIn WitIn StmtOut WitOut,
  ∀ stmtIn ∉ langIn,
    letI reduction := Reduction.mk prover verifier
    [fun ⟨stmtOut, _, _⟩ => stmtOut ∉ langOut
    | reduction.run stmtIn witIn] ≤ soundnessError

/--
  A straightline, deterministic, non-oracle-querying extractor takes in the initial statement, the
  output statement, the output witness, the IOR transcript, and the query log, and returns a
  corresponding initial witness.

  This form of extractor suffices for proving knowledge soundness of most hash-based IOPs.
-/
def StraightlineExtractor := StmtIn → StmtOut → WitOut →
    FullTranscript pSpec → QueryLog oSpec → WitIn

-- How would one define a rewinding extractor? It should have oracle access to the prover's
-- functions (receive challenges and send messages), and be able to observe & simulate the prover's
-- oracle queries

/--
  A reduction satisfies **(straightline) knowledge soundness** with error `knowledgeError ≥ 0` and
  with respect to input relation `relIn` and output relation `relOut`, if there exists a
  straightline extractor such that for all input statement `stmtIn`, witness `witIn`, and
  (malicious) prover `prover`, if the execution with the honest verifier results in a pair
  `(stmtOut, witOut)`, and the extractor produces some `witIn'`, then the probability that
  `(stmtIn, witIn')` is valid and yet `(stmtOut, witOut)` is not valid is at most `knowledgeError`.
-/
def knowledgeSoundness (relIn : StmtIn → WitIn → Prop) (relOut : StmtOut → WitOut → Prop)
    (verifier : Verifier pSpec oSpec StmtIn StmtOut) (knowledgeError : ℝ≥0) : Prop :=
  ∃ extractor : StraightlineExtractor,
  ∀ stmtIn : StmtIn,
  ∀ witIn : WitIn,
  ∀ prover : Prover pSpec oSpec StmtIn WitIn StmtOut WitOut,
    letI reduction := Reduction.mk prover verifier
    [fun ⟨stmtOut, witOut, transcript, proveQueryLog, _⟩ =>
      letI extractedWitIn := extractor stmtIn stmtOut witOut transcript proveQueryLog
      ¬ relIn stmtIn extractedWitIn ∧ relOut stmtOut witOut
    | reduction.runWithLog stmtIn witIn] ≤ knowledgeError

section Rewinding

/-- The oracle interface to call the prover as a black box -/
def OracleSpec.proverOracle (pSpec : ProtocolSpec n) (StmtIn : Type) :
    OracleSpec pSpec.MessageIndex := fun i => (StmtIn × pSpec.Transcript i, pSpec.Message i)

def SimOracle.proverImpl (P : Prover pSpec oSpec StmtIn WitIn StmtOut WitOut) :
    SimOracle.Stateless (OracleSpec.proverOracle pSpec StmtIn) oSpec := sorry

structure RewindingExtractor (pSpec : ProtocolSpec n) (oSpec : OracleSpec ι)
    (StmtIn StmtOut WitIn WitOut : Type) where
  /-- The state of the extractor -/
  ExtState : Type
  /-- Simulate challenge queries for the prover -/
  simChallenge : SimOracle.Stateful [pSpec.Challenge]ₒ [pSpec.Challenge]ₒ ExtState
  /-- Simulate oracle queries for the prover -/
  simOracle : SimOracle.Stateful oSpec oSpec ExtState
  /-- Run the extractor with the prover's oracle interface, allowing for calling the prover multiple
    times -/
  runExt : StmtOut → WitOut → StmtIn →
    StateT ExtState (OracleComp (OracleSpec.proverOracle pSpec StmtIn)) WitIn

def RewindingExtractor.run
    (P : AdaptiveProver pSpec oSpec StmtIn WitIn StmtOut WitOut)
    (E : RewindingExtractor pSpec oSpec StmtIn StmtOut WitIn WitOut) :
    OracleComp oSpec WitIn := sorry

end Rewinding

section StateRestoration

variable [DecidableEq StmtIn] [∀ i, DecidableEq (pSpec.Message i)]
    [∀ i, Sampleable (pSpec.Challenge i)]

-- /-- Version of `challengeOracle` that requires querying with the statement and prior messages.

-- This is a stepping stone toward the Fiat-Shamir transform. -/
def challengeOracle' (pSpec : ProtocolSpec n) (Statement : Type) :
    OracleSpec (pSpec.ChallengeIndex) :=
  fun i => (Statement × pSpec.Transcript i.1, pSpec.Challenge i)

class StateRestorationProver extends Prover pSpec oSpec StmtIn WitIn StmtOut WitOut
where
  stateRestorationQuery :
    OracleComp (oSpec ++ₒ challengeOracle' pSpec StmtIn) pSpec.FullTranscript

-- def runStateRestorationProver
--     (prover : StateRestorationProver pSpec oSpec StmtIn WitIn StmtOut WitOut)
--     (stmtIn : StmtIn) (witIn : WitIn) :
--     OracleComp (oSpec ++ₒ challengeOracle' pSpec (Statement := Statement))
--     (pSpec.FullTranscript × QueryLog (oSpec ++ₒ challengeOracle' pSpec (Statement := Statement)))
-- := do
--   let ⟨state, stmt, transcript⟩ ← prover.stateRestorationQuery stmtIn
--   return ⟨transcript, state⟩

-- def stateRestorationSoundness (verifier : Verifier pSpec oSpec StmtIn StmtOut)
--     [RelIn : Relation Statement Witness] (SRSoundnessError : ENNReal) : Prop :=
--   ∀ stmtIn ∉ RelIn.language,
--   ∀ witIn : Witness,
--   ∀ SRProver : StateRestorationProver pSpec oSpec,
--     let protocol := Reduction.mk (Witness := Witness)
--       SRProver.toProver verifier
--     sorry

end StateRestoration

section RoundByRound

instance : Fintype (pSpec.ChallengeIndex) := Subtype.fintype (fun i => pSpec.getDir i = .V_to_P)

structure StateFunction (langIn : Set StmtIn) (langOut : Set StmtOut)
    (verifier : Verifier pSpec oSpec StmtIn StmtOut)
    where
  fn : (m : Fin (n + 1)) → StmtIn → Transcript m pSpec → Prop
  /-- For all input statement not in the language, the state function is false for the empty
    transcript -/
  fn_empty : ∀ stmt ∉ langIn, fn 0 stmt default = False
  /-- If the state function is false for a partial transcript, and the next message is from the
    prover to the verifier, then the state function is also false for the new partial transcript
    regardless of the message -/
  fn_next : ∀ m, pSpec.getDir m = .P_to_V → ∀ stmt tr, fn m.castSucc stmt tr = False →
    ∀ msg, fn m.succ stmt (tr.snoc msg) = False
  /-- If the state function is false for a full transcript, the verifier will not output a statement
    in the output language -/
  fn_full : ∀ stmt tr, fn (.last n) stmt tr = False →
    [(· ∈ langOut) | verifier.run stmt tr] = 0

/--
  A protocol with `verifier` satisfies round-by-round soundness with error `rbrSoundnessError` and
  state function `stateFunction` if for all initial statement `stmtIn` not in the language of
  `relIn`, for all initial witness `witIn`, for all provers `prover`, for all `i : Fin n` that is a
  round corresponding to a challenge, the probability that the state function is false for the
  partial transcript output by the prover and the state function is true for the partial transcript
  appended by next challenge (chosen randomly) is at most `rbrSoundnessError i`.
-/
def rbrSoundness (langIn : Set StmtIn) (langOut : Set StmtOut)
    (verifier : Verifier pSpec oSpec StmtIn StmtOut)
    (stateFunction : StateFunction langIn langOut verifier)
    (rbrSoundnessError : pSpec.ChallengeIndex → ℝ≥0) : Prop :=
  ∀ stmtIn ∉ langIn,
  ∀ WitIn WitOut : Type,
  ∀ witIn : WitIn,
  ∀ prover : Prover pSpec oSpec StmtIn WitIn StmtOut WitOut,
  ∀ i : pSpec.ChallengeIndex,
    let ex : OracleComp (oSpec ++ₒ [pSpec.Challenge]ₒ) _ := do
      return (← prover.runWithLogToRound i.1.castSucc stmtIn witIn, ← pSpec.getChallenge i)
    [fun ⟨⟨transcript, _⟩, challenge⟩ =>
      ¬ stateFunction.fn i.1.castSucc stmtIn transcript ∧
        stateFunction.fn i.1.succ stmtIn (transcript.snoc challenge)
    | ex] ≤
      rbrSoundnessError i

/-- A round-by-round extractor with index `m` is given the input statement, a partial transcript
  of length `m`, the query log, and returns a witness to the statement.

  Note that the RBR extractor does not need to take in the output statement or witness. -/
def RBRExtractor (m : Fin (n + 1)) := StmtIn → Transcript m pSpec → QueryLog oSpec → WitIn

/--
  A protocol with `verifier` satisfies round-by-round knowledge soundness with error
  `rbrKnowledgeError` and state function `stateFunction` and extractor `extractor` if for all
  initial statement `stmtIn` not in the language of `relIn`, for all initial witness `witIn`, for
  all provers `prover`, for all `i : Fin n` that is a round corresponding to a challenge, the
  probability that the state function is false for the partial transcript output by the prover and
  the state function is true for the partial transcript appended by next challenge (chosen randomly)
  is at most `rbrKnowledgeError i`.
-/
def rbrKnowledgeSoundness (relIn : StmtIn → WitIn → Prop) (relOut : StmtOut → WitOut → Prop)
    (verifier : Verifier pSpec oSpec StmtIn StmtOut)
    (stateFunction : StateFunction relIn.language relOut.language verifier)
    (rbrKnowledgeError : pSpec.ChallengeIndex → ℝ≥0) : Prop :=
  ∃ extractor : (m : Fin (n + 1)) → RBRExtractor m,
  ∀ stmtIn : StmtIn,
  ∀ witIn : WitIn,
  ∀ prover : Prover pSpec oSpec StmtIn WitIn StmtOut WitOut,
  ∀ i : pSpec.ChallengeIndex,
    let ex : OracleComp (oSpec ++ₒ [pSpec.Challenge]ₒ) _ := (do
      let result ← prover.runWithLogToRound i.1.castSucc stmtIn witIn
      let chal ← pSpec.getChallenge i
      return (result, chal))
    [fun ⟨⟨transcript, _, proveQueryLog⟩, challenge⟩ =>
      letI extractedWitIn := extractor i.1.castSucc stmtIn transcript proveQueryLog
      ¬ relIn stmtIn extractedWitIn ∧
        ¬ stateFunction.fn i.1.castSucc stmtIn transcript ∧
          stateFunction.fn i.1.succ stmtIn (transcript.snoc challenge)
    | ex] ≤ rbrKnowledgeError i

end RoundByRound

section Classes

/-! We provide typeclasses for the security notions, so that we could synthesize them automatically
with verified transformations

For now, we only care about two properties: perfect completness and round-by-round knowledge
soundness -/

/-- Type class for (perfect) completeness for a reduction -/
class IsComplete (reduction : Reduction pSpec oSpec StmtIn WitIn StmtOut WitOut)
    (relIn : StmtIn → WitIn → Prop) (relOut : StmtOut → WitOut → Prop) where
  complete : perfectCompleteness relIn relOut reduction

/-- Type class for round-by-round knowledge soundness for a reduction -/
class IsRBRKnowledgeSound (verifier : Verifier pSpec oSpec StmtIn StmtOut)
    (relIn : StmtIn → WitIn → Prop) (relOut : StmtOut → WitOut → Prop) where
  rbrKnowledgeError : pSpec.ChallengeIndex → ℝ≥0
  stateFunction : StateFunction relIn.language relOut.language verifier
  is_rbr_knowledge_sound : rbrKnowledgeSoundness relIn relOut verifier
    stateFunction rbrKnowledgeError

end Classes

section Implications

/- TODO: add the following results
- `knowledgeSoundness` implies `soundness`
- `roundByRoundSoundness` implies `soundness`
- `roundByRoundKnowledgeSoundness` implies `roundByRoundSoundness`
- `roundByRoundKnowledgeSoundness` implies `knowledgeSoundness`

In other words, we have a lattice of security notions, with `knowledge` and `roundByRound` being
two strengthenings of soundness.
-/

/-- Knowledge soundness with knowledge error `knowledgeError < 1` implies soundness with the same
soundness error `knowledgeError`, and for the corresponding input and output languages. -/
theorem knowledgeSoundness_implies_soundness (relIn : StmtIn → WitIn → Prop)
    (relOut : StmtOut → WitOut → Prop)
    (verifier : Verifier pSpec oSpec StmtIn StmtOut)
    (knowledgeError : ℝ≥0) (hLt : knowledgeError < 1) :
      knowledgeSoundness relIn relOut verifier knowledgeError →
        soundness relIn.language relOut.language verifier knowledgeError := by
  simp [knowledgeSoundness, soundness, Function.language, Function.uncurry]
  intro extractor hKS WitIn' WitOut' witIn' prover stmtIn hStmtIn
  sorry
  -- have hKS' := hKS stmtIn witIn' prover
  -- clear hKS
  -- contrapose! hKS'
  -- constructor
  -- · convert hKS'; rename_i result
  --   obtain ⟨transcript, queryLog, stmtOut, witOut⟩ := result
  --   simp
  --   sorry
  -- · simp only [Function.language, Set.mem_setOf_eq, not_exists] at hStmtIn
  --   simp only [Functor.map, Seq.seq, PMF.bind_bind, Function.comp_apply, PMF.pure_bind, hStmtIn,
  --     PMF.bind_const, PMF.pure_apply, eq_iff_iff, iff_false, not_true_eq_false, ↓reduceIte,
  --     zero_add, ENNReal.coe_lt_one_iff, hLt]

/-- Round-by-round soundness with error `rbrSoundnessError` implies soundness with error
`∑ i, rbrSoundnessError i`, where the sum is over all rounds `i`. -/
theorem rbrSoundness_implies_soundness (langIn : Set StmtIn) (langOut : Set StmtOut)
    (verifier : Verifier pSpec oSpec StmtIn StmtOut)
    (stateFunction : StateFunction langIn langOut verifier)
    (rbrSoundnessError : pSpec.ChallengeIndex → ℝ≥0) :
      rbrSoundness langIn langOut verifier stateFunction rbrSoundnessError →
        soundness langIn langOut verifier (∑ i, rbrSoundnessError i) := by sorry

/-- Round-by-round knowledge soundness with error `rbrKnowledgeError` implies round-by-round
soundness with the same error `rbrKnowledgeError`. -/
theorem rbrKnowledgeSoundness_implies_rbrSoundness (relIn : StmtIn → WitIn → Prop)
    (relOut : StmtOut → WitOut → Prop)
    (verifier : Verifier pSpec oSpec StmtIn StmtOut)
    (stateFunction : StateFunction relIn.language relOut.language verifier)
    (rbrKnowledgeError : pSpec.ChallengeIndex → ℝ≥0) :
      rbrKnowledgeSoundness relIn relOut verifier stateFunction rbrKnowledgeError →
        rbrSoundness relIn.language relOut.language verifier stateFunction rbrKnowledgeError := by
  sorry

/-- Round-by-round knowledge soundness with error `rbrKnowledgeError` implies knowledge soundness
with error `∑ i, rbrKnowledgeError i`, where the sum is over all rounds `i`. -/
theorem rbrKnowledgeSoundness_implies_knowledgeSoundness
    (relIn : StmtIn → WitIn → Prop) (relOut : StmtOut → WitOut → Prop)
    (verifier : Verifier pSpec oSpec StmtIn StmtOut)
    (stateFunction : StateFunction relIn.language relOut.language verifier)
    (rbrKnowledgeError : pSpec.ChallengeIndex → ℝ≥0) :
      rbrKnowledgeSoundness relIn relOut verifier stateFunction rbrKnowledgeError →
        knowledgeSoundness relIn relOut verifier (∑ i, rbrKnowledgeError i) := by sorry

end Implications

end Soundness


section ZeroKnowledge

-- The simulator should have programming access to the shared oracles `oSpec`
structure Simulator (SimState : Type) where
  oracleSim : SimOracle.Stateful oSpec oSpec SimState
  proverSim : StmtIn → SimState → PMF (pSpec.FullTranscript × SimState)

/-
  We define honest-verifier zero-knowledge as follows:
  There exists a simulator such that for all (malicious) verifier, the distributions of transcripts
  generated by the simulator and the interaction between the verifier and the prover are
  (statistically) indistinguishable.
-/
-- def zeroKnowledge (prover : Prover pSpec oSpec) : Prop :=
--   ∃ simulator : Simulator,
--   ∀ verifier : Verifier pSpec oSpec,
--   ∀ stmtIn : Statement,
--   ∀ witIn : Witness,
--   relIn.isValid stmtIn witIn = true →
--     let result := (Reduction.mk prover verifier).run stmtIn witIn
--     let transcript := Prod.fst <$> Prod.snd <$> result
--     let simTranscript := simulator
--     -- let prob := spec.relOut.isValid' <$> output
--     sorry

end ZeroKnowledge

end Reduction


namespace OracleReduction

/- Completeness and soundness are the same as for non-oracle protocols. -/

open OracleComp OracleSpec Reduction
open scoped NNReal

variable {n : ℕ} {ι : Type} {pSpec : ProtocolSpec n} {oSpec : OracleSpec ι}
    [∀ i, ToOracle (pSpec.Message i)] [∀ i, VCVCompatible (pSpec.Challenge i)]
    {StmtIn WitIn StmtOut WitOut : Type}
    {ιₛᵢ : Type} {OStmtIn : ιₛᵢ → Type} [∀ i, ToOracle (OStmtIn i)]
    {ιₛₒ : Type} {OStmtOut : ιₛₒ → Type} [oSpec.FiniteRange]

def completeness
    (relIn : (StmtIn × ∀ i, OStmtIn i) → WitIn → Prop)
    (relOut : (StmtOut × (∀ i, OStmtOut i)) → WitOut → Prop)
    (oracleReduction : OracleReduction pSpec oSpec StmtIn WitIn StmtOut WitOut OStmtIn OStmtOut)
    (completenessError : ℝ≥0) : Prop :=
  Reduction.completeness relIn relOut oracleReduction.toReduction completenessError

def perfectCompleteness
    (relIn : (StmtIn × ∀ i, OStmtIn i) → WitIn → Prop)
    (relOut : (StmtOut × ∀ i, OStmtOut i) → WitOut → Prop)
    (oracleReduction : OracleReduction pSpec oSpec StmtIn WitIn StmtOut WitOut OStmtIn OStmtOut) :
      Prop :=
  Reduction.perfectCompleteness relIn relOut oracleReduction.toReduction

def soundness
    (langIn : Set (StmtIn × ∀ i, OStmtIn i))
    (langOut : Set (StmtOut × (∀ i, OStmtOut i)))
    (verifier : OracleVerifier pSpec oSpec StmtIn StmtOut OStmtIn OStmtOut)
    (soundnessError : ℝ≥0) : Prop :=
  Reduction.soundness langIn langOut verifier.toVerifier soundnessError

def knowledgeSoundness (verifier : OracleVerifier pSpec oSpec StmtIn StmtOut OStmtIn OStmtOut)
    (relIn : (StmtIn × ∀ i, OStmtIn i) → WitIn → Prop)
    (relOut : (StmtOut × (∀ i, OStmtOut i)) → WitOut → Prop)
    (knowledgeError : ℝ≥0) : Prop :=
  Reduction.knowledgeSoundness relIn relOut verifier.toVerifier knowledgeError

def rbrSoundness
    (langIn : Set (StmtIn × ∀ i, OStmtIn i))
    (langOut : Set (StmtOut × (∀ i, OStmtOut i)))
    (verifier : OracleVerifier pSpec oSpec StmtIn StmtOut OStmtIn OStmtOut)
    (stateFunction : StateFunction langIn langOut verifier.toVerifier)
    (rbrSoundnessError : pSpec.ChallengeIndex → ℝ≥0) : Prop :=
  Reduction.rbrSoundness langIn langOut verifier.toVerifier stateFunction rbrSoundnessError

def rbrKnowledgeSoundness
    (relIn : (StmtIn × ∀ i, OStmtIn i) → WitIn → Prop)
    (relOut : (StmtOut × (∀ i, OStmtOut i)) → WitOut → Prop)
    (verifier : OracleVerifier pSpec oSpec StmtIn StmtOut OStmtIn OStmtOut)
    (stateFunction : StateFunction relIn.language relOut.language verifier.toVerifier)
    (rbrKnowledgeError : pSpec.ChallengeIndex → ℝ≥0) : Prop :=
  Reduction.rbrKnowledgeSoundness relIn relOut verifier.toVerifier stateFunction rbrKnowledgeError

end OracleReduction

end
