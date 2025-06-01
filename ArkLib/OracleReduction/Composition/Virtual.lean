import ArkLib.OracleReduction.Security.Basic

/-!
  ## Semantics of Virtual (Oracle) Reductions

  Sequential composition is usually not enough to represent oracle reductions in a modular way. We
  also need to formalize **virtual** oracle reductions, which lift reductions from one (virtual)
  context into the another (real) context.

  This is what is meant when we informally say "apply so-and-so protocol to this quantity (derived
  from the input statement & witness)".

  Put in other words, we define a mapping between the input-output interfaces of two (oracle)
  reductions, without changing anything about the underlying reductions.

  Recall that the input-output interface of an oracle reduction consists of:
  - Input: `OuterStmtIn : Type`, `OuterOStmtIn : ιₛᵢ → Type`, and `OuterWitIn : Type`
  - Output: `OuterStmtOut : Type`, `OuterOStmtOut : ιₛₒ → Type`, and `OuterWitOut : Type`

  Say we have an oracle reduction. We want to transport it to a different interface.

  The transport is defined as the following mappings:

  - `projectStmt : OuterStmtIn → InnerStmtIn`
  - `projectOStmt : (simulation involving OuterOStmtIn to produce InnerOStmtIn)`
  - `projectWit : OuterWitIn → InnerWitIn`
  - `integrateStmt : OuterStmtIn × InnerStmtOut → OuterStmtOut`
  - `integrateOStmt : (simulation involving InnerOStmtOut to produce OuterOStmtOut)`
  - `integrateWit : OuterWitIn × InnerWitOut → OuterWitOut`

  Note that this is very similar to the concept of lenses in programming languages / category
  theory. Namely, transport on the inputs correspond to a `view`/`get` operation (our "project"),
  while transport on the output corresponds to a `modify`/`set` operation (our "integrate").

  What are some expected properties of the transport (via the connection to lenses)?

  First, we recall the expected properties of lenses:

  1. `get(lens, set(lens, value, store)) = value`
  2. `set(lens, new, set(lens, old, store)) = set(lens, new, store)`
  3. `set(lens, get(lens, store), store) = store`
  4. and more

  What should this mean here?
  - one property not mentioned above, is that the pre-image of `projectInput` should be invariant
    for `integrateOutput`.

  That is, if `projectInput(inp1) = projectInput(inp2) = inp*`, then `integrateOutput(inp1, out)
  = integrateOutput(inp2, out)` for all `out` which is a possible result of running the oracle
  reduction on `inp*`. This basically implies a decomposition of sorts between the input to be
  transported.
-/

open OracleSpec OracleComp ProtocolSpec

section Transport

open scoped NNReal

/-- A lens for transporting (non-oracle) statements between outer and inner contexts -/
structure StatementLens (OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut : Type) where
  projectStmt : OuterStmtIn → InnerStmtIn
  integrateStmt : OuterStmtIn × InnerStmtOut → OuterStmtOut

/-- A lens for transporting oracle statements between outer and inner contexts

We require knowledge of the (non-oracle) input statement in the outer context, along with the
(non-oracle) output statement in the inner context. -/
structure OStatementLens (OuterStmtIn InnerStmtOut : Type)
    {Outer_ιₛᵢ : Type} (OuterOStmtIn : Outer_ιₛᵢ → Type) [∀ i, OracleInterface (OuterOStmtIn i)]
    {Outer_ιₛₒ : Type} (OuterOStmtOut : Outer_ιₛₒ → Type) [∀ i, OracleInterface (OuterOStmtOut i)]
    {Inner_ιₛᵢ : Type} (InnerOStmtIn : Inner_ιₛᵢ → Type) [∀ i, OracleInterface (InnerOStmtIn i)]
    {Inner_ιₛₒ : Type} (InnerOStmtOut : Inner_ιₛₒ → Type) [∀ i, OracleInterface (InnerOStmtOut i)]
  where
  -- To access an input oracle statement in the inner context, we may simulate it using the input
  -- (non-oracle) statement of the outer context, along with oracle access to the outer input oracle
  -- statements
  projectOStmt : QueryImpl [InnerOStmtIn]ₒ
    (ReaderT OuterStmtIn (OracleComp [OuterOStmtIn]ₒ))
  -- To get back an output oracle statement in the outer context, we may simulate it using the input
  -- (non-oracle) statement of the outer context, the output (non-oracle) statement of the inner
  -- context, along with oracle access to the inner output oracle statements
  integrateOStmt : QueryImpl [OuterOStmtOut]ₒ
    (ReaderT (OuterStmtIn × InnerStmtOut) (OracleComp [InnerOStmtOut]ₒ))

/-- A lens for transporting witnesses between outer and inner contexts -/
structure WitnessLens (OuterWitIn OuterWitOut InnerWitIn InnerWitOut : Type) where
  projectWit : OuterWitIn → InnerWitIn
  integrateWit : OuterWitIn × InnerWitOut → OuterWitOut

/-- A lens for transporting between outer and inner contexts of a (non-oracle) reduction -/
structure ContextLens (OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut : Type)
    (OuterWitIn OuterWitOut InnerWitIn InnerWitOut : Type)
    extends StatementLens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut,
      WitnessLens OuterWitIn OuterWitOut InnerWitIn InnerWitOut

/-- A lens for transporting between outer and inner contexts of an oracle reduction -/
structure OracleContextLens (OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut : Type)
    {Outer_ιₛᵢ : Type} (OuterOStmtIn : Outer_ιₛᵢ → Type) [∀ i, OracleInterface (OuterOStmtIn i)]
    {Outer_ιₛₒ : Type} (OuterOStmtOut : Outer_ιₛₒ → Type) [∀ i, OracleInterface (OuterOStmtOut i)]
    {Inner_ιₛᵢ : Type} (InnerOStmtIn : Inner_ιₛᵢ → Type) [∀ i, OracleInterface (InnerOStmtIn i)]
    {Inner_ιₛₒ : Type} (InnerOStmtOut : Inner_ιₛₒ → Type) [∀ i, OracleInterface (InnerOStmtOut i)]
    (OuterWitIn OuterWitOut InnerWitIn InnerWitOut : Type) extends

      StatementLens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut,

      OStatementLens OuterStmtIn InnerStmtOut
        OuterOStmtIn OuterOStmtOut InnerOStmtIn InnerOStmtOut,

      WitnessLens OuterWitIn OuterWitOut InnerWitIn InnerWitOut

/-
  Recall the interface of an extractor:
  - Takes in `WitOut`, `StmtIn`, `Transcript`, `QueryLog`
  (note: no need for `StmtOut` as it can be derived from `StmtIn`, `Transcript`, and `QueryLog`)
  - Returns `WitIn`

  We need a lens for the extractor as well.

  Assume we have an inner extractor
    `E : InnerWitOut → InnerStmtIn → Transcript → QueryLog → InnerWitIn`

  We need to derive an outer extractor
    `E' : OuterWitOut → OuterStmtIn → Transcript → QueryLog → OuterWitIn`

  Note that `Transcript` and `QueryLog` are the same due to the lens only changing the
  input-output interface, and not the inside (oracle) reduction.

  So, `E' outerWitOut outerStmtIn transcript queryLog` needs to call
    `E (map to innerWitOut) (projectStmt outerStmtIn) transcript queryLog`
  and then post-process the result, which is some `innerWitIn`, to get some `outerWitIn`.

  This processing is exactly the same as a lens in the opposite direction between the outer and
  inner witness types.
-/

/-- Inverse lens between outer and inner witnesses (going the other direction with respect to
  input-output), for extractors / knowledge soundness -/
def WitnessLensInv (OuterWitIn OuterWitOut InnerWitIn InnerWitOut : Type) :=
  WitnessLens OuterWitOut OuterWitIn InnerWitOut InnerWitIn
  -- projectWitInv : InnerWitOut → OuterWitOut
  -- integrateWitInv : InnerWitIn × OuterWitOut → OuterWitIn

/-- Conditions for the lens / transformation to preserve completeness

For `integrate`, we require compatibility relations between the outer input statement/witness and
the inner output statement/witness -/
structure ContextLens.IsComplete {OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut : Type}
    {OuterWitIn OuterWitOut InnerWitIn InnerWitOut : Type}
    (outerRelIn : OuterStmtIn → OuterWitIn → Prop)
    (innerRelIn : InnerStmtIn → InnerWitIn → Prop)
    (outerRelOut : OuterStmtOut → OuterWitOut → Prop)
    (innerRelOut : InnerStmtOut → InnerWitOut → Prop)
    (compat : OuterStmtIn × OuterWitIn → InnerStmtOut × InnerWitOut → Prop)
    (lens : ContextLens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut
                        OuterWitIn OuterWitOut InnerWitIn InnerWitOut) where

  project_complete : ∀ stmtIn witIn,
    outerRelIn stmtIn witIn →
    innerRelIn (lens.projectStmt stmtIn) (lens.projectWit witIn)

  integrate_complete : ∀ outerStmtIn outerWitIn innerStmtOut innerWitOut,
    outerRelIn outerStmtIn outerWitIn →
    innerRelOut innerStmtOut innerWitOut →
    compat (outerStmtIn, outerWitIn) (innerStmtOut, innerWitOut) →
    outerRelOut (lens.integrateStmt (outerStmtIn, innerStmtOut))
                (lens.integrateWit (outerWitIn, innerWitOut))

/-- Conditions for the lens / transformation to preserve soundness -/
structure StatementLens.IsSound {OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut : Type}
    (outerLangIn : Set OuterStmtIn) (outerLangOut : Set OuterStmtOut)
    (innerLangIn : Set InnerStmtIn) (innerLangOut : Set InnerStmtOut)
    (compat : OuterStmtIn → InnerStmtOut → Prop)
    (stmtLens : StatementLens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut) where

  project_sound : ∀ outerStmtIn,
    outerStmtIn ∉ outerLangIn → stmtLens.projectStmt outerStmtIn ∉ innerLangIn

  integrate_sound : ∀ outerStmtIn innerStmtOut,
    outerStmtIn ∉ outerLangIn →
    innerStmtOut ∉ innerLangOut →
    compat outerStmtIn innerStmtOut →
      stmtLens.integrateStmt (outerStmtIn, innerStmtOut) ∈ outerLangOut

/-- Conditions for the lens / transformation to preserve knowledge soundness

(TODO: double-check) -/
structure ContextLens.IsKnowledgeSound
    {OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut : Type}
    {OuterWitIn OuterWitOut InnerWitIn InnerWitOut : Type}
    (outerRelIn : OuterStmtIn → OuterWitIn → Prop)
    (innerRelIn : InnerStmtIn → InnerWitIn → Prop)
    (outerRelOut : OuterStmtOut → OuterWitOut → Prop)
    (innerRelOut : InnerStmtOut → InnerWitOut → Prop)
    (compat : OuterStmtIn × OuterWitIn → InnerStmtOut × InnerWitOut → Prop)
    (lens : ContextLens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut
                        OuterWitIn OuterWitOut InnerWitIn InnerWitOut) where

  project_knowledge_sound : ∀ outerStmtIn outerWitIn,
    outerRelIn outerStmtIn outerWitIn →
    innerRelIn (lens.projectStmt outerStmtIn) (lens.projectWit outerWitIn)

  integrate_knowledge_sound : ∀ outerStmtIn outerWitIn innerStmtOut innerWitOut,
    outerRelIn outerStmtIn outerWitIn →
    innerRelOut innerStmtOut innerWitOut →
    outerRelOut (lens.integrateStmt (outerStmtIn, innerStmtOut))
                (lens.integrateWit (outerWitIn, innerWitOut))

/-
  The above two soundness / knowledge soundness conditions should be the same for all notions,
  i.e. regular, state-restoration, round-by-round, etc.,
  since we only act on the input-output interface
-/

variable {n : ℕ} {pSpec : ProtocolSpec n} {ι : Type} {oSpec : OracleSpec ι}
  {OuterStmtIn OuterWitIn OuterStmtOut OuterWitOut : Type}
  {InnerStmtIn InnerWitIn InnerStmtOut InnerWitOut : Type}
  [∀ i, VCVCompatible (pSpec.Challenge i)]

/-- The outer prover after transport invokes the inner prover on the projected input, and
  integrates the output -/
def Prover.transport
    (lens : ContextLens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut
      OuterWitIn OuterWitOut InnerWitIn InnerWitOut)
    (P : Prover pSpec oSpec InnerStmtIn InnerWitIn InnerStmtOut InnerWitOut) :
      Prover pSpec oSpec OuterStmtIn OuterWitIn OuterStmtOut OuterWitOut where
  PrvState := fun i => P.PrvState i × OuterStmtIn × OuterWitIn
  input := fun stmtIn witIn =>
    ⟨P.input (lens.projectStmt stmtIn) (lens.projectWit witIn), stmtIn, witIn⟩
  sendMessage := fun i ⟨prvState, stmtIn, witIn⟩ => do
    let ⟨msg, prvState'⟩ ← P.sendMessage i prvState
    return ⟨msg, ⟨prvState', stmtIn, witIn⟩⟩
  receiveChallenge := fun i ⟨prvState, stmtIn, witIn⟩ chal =>
    ⟨P.receiveChallenge i prvState chal, stmtIn, witIn⟩
  output := fun ⟨prvState, stmtIn, witIn⟩ =>
    let ⟨innerStmtOut, innerWitOut⟩ := P.output prvState
    ⟨lens.integrateStmt (stmtIn, innerStmtOut), lens.integrateWit (witIn, innerWitOut)⟩

/-- The outer verifier after transport invokes the inner verifier on the projected input, and
  integrates the output -/
def Verifier.transport
    (lens : StatementLens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut)
    (V : Verifier pSpec oSpec InnerStmtIn InnerStmtOut) :
      Verifier pSpec oSpec OuterStmtIn OuterStmtOut where
  verify := fun stmtIn transcript => do
    let innerStmtIn := lens.projectStmt stmtIn
    let innerStmtOut ← V.verify innerStmtIn transcript
    return lens.integrateStmt (stmtIn, innerStmtOut)

/-- The outer reduction after transport is the combination of the transport of the prover and
  verifier -/
def Reduction.transport
    (lens : ContextLens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut
      OuterWitIn OuterWitOut InnerWitIn InnerWitOut)
    (R : Reduction pSpec oSpec InnerStmtIn InnerWitIn InnerStmtOut InnerWitOut) :
      Reduction pSpec oSpec OuterStmtIn OuterWitIn OuterStmtOut OuterWitOut where
  prover := R.prover.transport lens
  verifier := R.verifier.transport lens.toStatementLens

open Reduction in
/-- The outer extractor after transport invokes the inner extractor on the projected input, and
  integrates the output -/
def StraightlineExtractor.transport
    (lens : ContextLens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut
      OuterWitIn OuterWitOut InnerWitIn InnerWitOut)
    (lensInv : WitnessLensInv OuterWitIn OuterWitOut InnerWitIn InnerWitOut)
    (E : @StraightlineExtractor _ pSpec _ oSpec InnerStmtIn InnerWitIn InnerWitOut) :
      @StraightlineExtractor _ pSpec _ oSpec OuterStmtIn OuterWitIn OuterWitOut :=
  fun outerWitOut outerStmtIn fullTranscript proveQueryLog verifyQueryLog =>
    let innerStmtIn := lens.projectStmt outerStmtIn
    let innerWitOut := lensInv.projectWit outerWitOut
    let innerWitIn := E innerWitOut innerStmtIn fullTranscript proveQueryLog verifyQueryLog
    lensInv.integrateWit (outerWitOut, innerWitIn)

open Reduction in
/-- The outer state function after transport invokes the inner state function on the projected
  input, and integrates the output -/
def StateFunction.transport [oSpec.FiniteRange]
    (lens : ContextLens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut
      OuterWitIn OuterWitOut InnerWitIn InnerWitOut)
    (innerLangIn : Set InnerStmtIn) (innerLangOut : Set InnerStmtOut)
    (V : Verifier pSpec oSpec InnerStmtIn InnerStmtOut)
    (S : @StateFunction _ pSpec _ oSpec _ InnerStmtIn InnerStmtOut innerLangIn innerLangOut V) :
      StateFunction (lens.projectStmt ⁻¹' innerLangIn)
        -- TODO: figure out the right induced language for `OuterStmtOut`
        (fun _ : OuterStmtOut => True) (V.transport lens.toStatementLens) where
  fn := sorry
  fn_empty := sorry
  fn_next := sorry
  fn_full := sorry

/-- Compatibility relation between the outer input statement and the inner output statement,
relative to a verifier.

We require that the inner output statement is a possible output of the verifier on the outer
input statement, for any given transcript. Note that we have to existentially quantify over
transcripts since we only reference the verifier, and there's no way to get the transcript without
a prover. -/
def Verifier.compatStatement {OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut : Type}
    (lens : StatementLens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut)
    (V : Verifier pSpec oSpec InnerStmtIn InnerStmtOut) :
      OuterStmtIn → InnerStmtOut → Prop :=
  fun outerStmtIn innerStmtOut =>
    innerStmtOut ∈ ⋃ transcript, (V.run (lens.projectStmt outerStmtIn) transcript).support

/-- Compatibility relation between the outer input context and the inner output context, relative
to a reduction.

We require that the inner output context (statement + witness) is a possible output of the reduction
on the outer input context (statement + witness). -/
def Reduction.compatContext {OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut : Type}
    {OuterWitIn OuterWitOut InnerWitIn InnerWitOut : Type}
    (lens : ContextLens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut
      OuterWitIn OuterWitOut InnerWitIn InnerWitOut)
    (R : Reduction pSpec oSpec InnerStmtIn InnerWitIn InnerStmtOut InnerWitOut) :
      OuterStmtIn × OuterWitIn → InnerStmtOut × InnerWitOut → Prop :=
  fun ⟨outerStmtIn, outerWitIn⟩ innerContextOut =>
    innerContextOut ∈
      Prod.fst <$> (R.run (lens.projectStmt outerStmtIn) (lens.projectWit outerWitIn)).support

section Theorems

/- Theorems about transport interacting with reduction execution and security properties -/

section Prover

/- Breaking down the intertwining of transport and prover execution -/

/-- Transporting the prover intertwines with the process round function -/
theorem Prover.transport_processRound
    {lens : ContextLens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut
                        OuterWitIn OuterWitOut InnerWitIn InnerWitOut}
    {i : Fin n}
    (P : Prover pSpec oSpec InnerStmtIn InnerWitIn InnerStmtOut InnerWitOut)
    {resultRound : OracleComp (oSpec ++ₒ [pSpec.Challenge]ₒ)
      (pSpec.Transcript i.castSucc × (P.transport lens).PrvState i.castSucc)} :
      (P.transport lens).processRound i resultRound
      = do
        let ⟨transcript, prvState, outerStmtIn, outerWitIn⟩ ← resultRound
        let ⟨newTranscript, newPrvState⟩ ← P.processRound i (do return ⟨transcript, prvState⟩)
        return ⟨newTranscript, ⟨newPrvState, outerStmtIn, outerWitIn⟩⟩ := by
  unfold processRound transport
  simp
  congr 1; funext
  split <;> simp

/-- Lemma needed for the proof of `Prover.transport_runToRound` -/
private lemma Prover.bind_map_processRound_pure {i : Fin n}
    (P : Prover pSpec oSpec InnerStmtIn InnerWitIn InnerStmtOut InnerWitOut)
    (comp : OracleComp (oSpec ++ₒ [pSpec.Challenge]ₒ)
        (pSpec.Transcript i.castSucc × P.PrvState i.castSucc))
    {α : Type} (f : pSpec.Transcript i.succ × P.PrvState i.succ → α) :
      (do let result ← comp; f <$> P.processRound i (pure result))
      = f <$> P.processRound i comp := by
  simp [processRound]

theorem Prover.transport_runToRound
    {lens : ContextLens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut
                        OuterWitIn OuterWitOut InnerWitIn InnerWitOut}
    {outerStmtIn : OuterStmtIn} {outerWitIn : OuterWitIn} {i : Fin (n + 1)}
    (P : Prover pSpec oSpec InnerStmtIn InnerWitIn InnerStmtOut InnerWitOut) :
      (P.transport lens).runToRound i outerStmtIn outerWitIn
      = do
        let ⟨transcript, prvState⟩ ←
          P.runToRound i (lens.projectStmt outerStmtIn) (lens.projectWit outerWitIn)
        return ⟨transcript, ⟨prvState, outerStmtIn, outerWitIn⟩⟩ := by
  unfold runToRound
  induction i using Fin.induction with
  | zero => simp [transport]
  | succ i ih => simp [transport_processRound, ih, bind_map_processRound_pure]

-- Requires more lemmas about `simulateQ` for logging oracles
theorem Prover.transport_runWithLogToRound
    {lens : ContextLens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut
                        OuterWitIn OuterWitOut InnerWitIn InnerWitOut}
    {outerStmtIn : OuterStmtIn} {outerWitIn : OuterWitIn} {i : Fin (n + 1)}
    (P : Prover pSpec oSpec InnerStmtIn InnerWitIn InnerStmtOut InnerWitOut) :
      (P.transport lens).runWithLogToRound i outerStmtIn outerWitIn
      = do
        let ⟨transcript, prvState, queryLog⟩ ←
          P.runWithLogToRound i (lens.projectStmt outerStmtIn) (lens.projectWit outerWitIn)
        return ⟨transcript, ⟨prvState, outerStmtIn, outerWitIn⟩, queryLog⟩ := by
  unfold runWithLogToRound
  induction i using Fin.induction with
  | zero => simp [transport]
  | succ i ih =>
    simp at ih
    simp only [ChallengeIdx, bind_pure_comp, Functor.map_map]
    sorry

/-- Running the transported outer prover is equivalent to running the inner prover on the projected
  input, and then integrating the output -/
theorem Prover.transport_run
    {lens : ContextLens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut
                        OuterWitIn OuterWitOut InnerWitIn InnerWitOut}
    {outerStmtIn : OuterStmtIn} {outerWitIn : OuterWitIn}
    (P : Prover pSpec oSpec InnerStmtIn InnerWitIn InnerStmtOut InnerWitOut) :
      (P.transport lens).run outerStmtIn outerWitIn
      = do
        let ⟨innerStmtOut, innerWitOut, fullTranscript⟩ ←
          P.run (lens.projectStmt outerStmtIn) (lens.projectWit outerWitIn)
        return ⟨lens.integrateStmt (outerStmtIn, innerStmtOut),
                lens.integrateWit (outerWitIn, innerWitOut),
                fullTranscript⟩ := by
  simp only [Prover.run, ChallengeIdx, transport_runToRound, bind_pure_comp, Functor.map_map]
  simp [transport]

/- Transporting the prover intertwines with the runWithLog function -/
theorem Prover.transport_runWithLog
    {lens : ContextLens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut
                        OuterWitIn OuterWitOut InnerWitIn InnerWitOut}
    {outerStmtIn : OuterStmtIn} {outerWitIn : OuterWitIn}
    (P : Prover pSpec oSpec InnerStmtIn InnerWitIn InnerStmtOut InnerWitOut) :
      (P.transport lens).runWithLog outerStmtIn outerWitIn
      = do
        let ⟨innerStmtOut, innerWitOut, fullTranscript, queryLog⟩ ←
          P.runWithLog (lens.projectStmt outerStmtIn) (lens.projectWit outerWitIn)
        return ⟨lens.integrateStmt (outerStmtIn, innerStmtOut),
                lens.integrateWit (outerWitIn, innerWitOut),
                fullTranscript,
                queryLog⟩ := by
  simp only [ChallengeIdx, runWithLog, transport_runWithLogToRound, bind_pure_comp, Functor.map_map]
  simp [transport]

end Prover

theorem Reduction.transport_run
    {lens : ContextLens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut
      OuterWitIn OuterWitOut InnerWitIn InnerWitOut}
    {outerStmtIn : OuterStmtIn} {outerWitIn : OuterWitIn}
    (R : Reduction pSpec oSpec InnerStmtIn InnerWitIn InnerStmtOut InnerWitOut) :
      (R.transport lens).run outerStmtIn outerWitIn = do
        let ⟨⟨prvInnerStmtOut, innerWitOut⟩, verInnerStmtOut, fullTranscript⟩ ←
          R.run (lens.projectStmt outerStmtIn) (lens.projectWit outerWitIn)
        return ⟨⟨lens.integrateStmt (outerStmtIn, prvInnerStmtOut),
                lens.integrateWit (outerWitIn, innerWitOut)⟩,
                lens.integrateStmt (outerStmtIn, verInnerStmtOut),
                fullTranscript⟩ := by
  unfold Reduction.run
  simp [Reduction.transport, Prover.transport_run, Verifier.transport, Verifier.run]

theorem Reduction.transport_runWithLog
    {lens : ContextLens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut
      OuterWitIn OuterWitOut InnerWitIn InnerWitOut}
    {outerStmtIn : OuterStmtIn} {outerWitIn : OuterWitIn}
    (R : Reduction pSpec oSpec InnerStmtIn InnerWitIn InnerStmtOut InnerWitOut) :
      (R.transport lens).runWithLog outerStmtIn outerWitIn = do
        let ⟨⟨prvInnerStmtOut, innerWitOut⟩, verInnerStmtOut, fullTranscript, queryLog⟩ ←
          R.runWithLog (lens.projectStmt outerStmtIn) (lens.projectWit outerWitIn)
        return ⟨⟨lens.integrateStmt (outerStmtIn, prvInnerStmtOut),
          lens.integrateWit (outerWitIn, innerWitOut)⟩,
          lens.integrateStmt (outerStmtIn, verInnerStmtOut), fullTranscript, queryLog⟩ := by
  unfold Reduction.runWithLog
  simp [Reduction.transport, Prover.transport_runWithLog, Verifier.transport, Verifier.run]

variable [oSpec.FiniteRange]

/--
  Transporting the reduction preserves completeness, assuming the lens satisfies its completeness
  conditions
-/
theorem Reduction.transport_completeness
    {relIn : OuterStmtIn → OuterWitIn → Prop} {relOut : OuterStmtOut → OuterWitOut → Prop}
    {relIn' : InnerStmtIn → InnerWitIn → Prop} {relOut' : InnerStmtOut → InnerWitOut → Prop}
    {completenessError : ℝ≥0}
    (lens : ContextLens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut
      OuterWitIn OuterWitOut InnerWitIn InnerWitOut)
    (R : Reduction pSpec oSpec InnerStmtIn InnerWitIn InnerStmtOut InnerWitOut)
    (lensComplete : lens.IsComplete relIn relIn' relOut relOut' (R.compatContext lens))
    (h : R.completeness relIn' relOut' completenessError) :
      (R.transport lens).completeness relIn relOut completenessError := by
  unfold completeness at h ⊢
  intro outerStmtIn outerWitIn hRelIn
  have hR := h (lens.projectStmt outerStmtIn) (lens.projectWit outerWitIn)
    (lensComplete.project_complete _ _ hRelIn)
  rw [Reduction.transport_run]
  refine le_trans hR ?_
  simp
  refine probEvent_mono ?_
  intro ⟨innerContextOut, a, b⟩ hSupport ⟨hRelOut, hRelOut'⟩
  have : innerContextOut ∈
      Prod.fst <$> (R.run (lens.projectStmt outerStmtIn) (lens.projectWit outerWitIn)).support := by
    simp
    exact ⟨a, b, hSupport⟩
  simp_all
  refine lensComplete.integrate_complete _ _ _ _ hRelIn hRelOut ?_
  rw [← hRelOut']
  simp [compatContext]; exact this

/-- Transporting the reduction preserves soundness, assuming the lens satisfies its soundness
  conditions -/
theorem Reduction.transport_soundness
    {outerLangIn : Set OuterStmtIn} {outerLangOut : Set OuterStmtOut}
    {innerLangIn : Set InnerStmtIn} {innerLangOut : Set InnerStmtOut}
    {soundnessError : ℝ≥0}
    (lens : StatementLens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut)
    (V : Verifier pSpec oSpec InnerStmtIn InnerStmtOut)
    -- TODO: figure out the right compatibility relation for the IsSound condition
    (lensSound : lens.IsSound outerLangIn outerLangOut innerLangIn innerLangOut (fun _ _ => True))
    (h : Reduction.soundness innerLangIn innerLangOut V soundnessError) :
      Reduction.soundness outerLangIn outerLangOut (V.transport lens) soundnessError := by
  unfold soundness at h ⊢
  intro outerStmtIn hOuterStmtIn OuterWitIn OuterWitOut outerWitIn prover
  sorry

/-
  Transporting the reduction preserves knowledge soundness, assuming the lens satisfies its
  knowledge soundness conditions
-/
theorem Reduction.transport_knowledgeSoundness
    {outerRelIn : OuterStmtIn → OuterWitIn → Prop} {outerRelOut : OuterStmtOut → OuterWitOut → Prop}
    {innerRelIn : InnerStmtIn → InnerWitIn → Prop} {innerRelOut : InnerStmtOut → InnerWitOut → Prop}
    {soundnessError : ℝ≥0}
    (lens : ContextLens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut
      OuterWitIn OuterWitOut InnerWitIn InnerWitOut)
    (lensKnowledgeSound : lens.IsKnowledgeSound outerRelIn innerRelIn outerRelOut innerRelOut
      (fun _ _ => True))
    (V : Verifier pSpec oSpec InnerStmtIn InnerStmtOut)
    (h : Reduction.knowledgeSoundness innerRelIn innerRelOut V soundnessError) :
      Reduction.knowledgeSoundness outerRelIn outerRelOut
        (V.transport lens.toStatementLens) soundnessError := by
  unfold knowledgeSoundness at h ⊢
  obtain ⟨E, h'⟩ := h
  stop
  refine ⟨E.transport lens lens.toContextLensInv, ?_⟩ -- lensInv needs to be correctly derived
  intro outerStmtIn outerWitIn hRelIn
  have hR := h (lens.projectStmt outerStmtIn) (lens.projectWit outerWitIn)
    (lensKnowledgeSound.project_knowledge_sound _ _ hRelIn)
  rw [Reduction.transport_run]
  sorry

/-
  Transporting the reduction preserves round-by-round soundness, assuming the lens satisfies its
  soundness conditions
-/
theorem Reduction.transport_rbr_soundness
    {outerLangIn : Set OuterStmtIn} {outerLangOut : Set OuterStmtOut}
    {innerLangIn : Set InnerStmtIn} {innerLangOut : Set InnerStmtOut}
    {rbrSoundnessError : pSpec.ChallengeIdx → ℝ≥0}
    (lens : StatementLens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut)
    (V : Verifier pSpec oSpec InnerStmtIn InnerStmtOut)
    -- TODO: figure out the right compatibility relation for the IsSound condition
    (lensSound : lens.IsSound outerLangIn outerLangOut innerLangIn innerLangOut (fun _ _ => True))
    (h : Reduction.rbrSoundness innerLangIn innerLangOut V rbrSoundnessError) :
      Reduction.rbrSoundness outerLangIn outerLangOut (V.transport lens) rbrSoundnessError := by
  unfold rbrSoundness at h ⊢
  sorry

/-
  Transporting the reduction preserves round-by-round knowledge soundness, assuming the lens
  satisfies its knowledge soundness conditions
-/
theorem Reduction.transport_rbr_knowledgeSoundness
    {outerRelIn : OuterStmtIn → OuterWitIn → Prop} {outerRelOut : OuterStmtOut → OuterWitOut → Prop}
    {innerRelIn : InnerStmtIn → InnerWitIn → Prop} {innerRelOut : InnerStmtOut → InnerWitOut → Prop}
    {rbrKnowledgeError : pSpec.ChallengeIdx → ℝ≥0}
    (lens : ContextLens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut
      OuterWitIn OuterWitOut InnerWitIn InnerWitOut)
    (lensKnowledgeSound : lens.IsKnowledgeSound outerRelIn innerRelIn outerRelOut innerRelOut
      (fun _ _ => True))
    (V : Verifier pSpec oSpec InnerStmtIn InnerStmtOut)
    (h : Reduction.rbrKnowledgeSoundness innerRelIn innerRelOut V rbrKnowledgeError) :
      Reduction.rbrKnowledgeSoundness outerRelIn outerRelOut
        (V.transport lens.toStatementLens) rbrKnowledgeError := by
  sorry

end Theorems


-- TODO: state definitions & theorems about oracle reduction as well


end Transport

section Test

open Polynomial

-- Testing out sum-check-like relations

noncomputable section

def OuterStmtIn_Test := ℤ[X] × ℤ[X] × ℤ
def InnerStmtIn_Test := ℤ[X] × ℤ

def outerRelIn_Test : OuterStmtIn_Test → Unit → Prop :=
  fun ⟨p, q, t⟩ _ => ∑ x ∈ {0, 1}, (p * q).eval x = t
def innerRelIn_Test : InnerStmtIn_Test → Unit → Prop :=
  fun ⟨f, t⟩ _ => ∑ x ∈ {0, 1}, f.eval x = t

def OuterStmtOut_Test := ℤ[X] × ℤ[X] × ℤ × ℤ
def InnerStmtOut_Test := ℤ[X] × ℤ × ℤ

def outerRelOut_Test : OuterStmtOut_Test → Unit → Prop :=
  fun ⟨p, q, t, r⟩ _ => (p * q).eval r = t
def innerRelOut_Test : InnerStmtOut_Test → Unit → Prop :=
  fun ⟨f, t, r⟩ _ => f.eval r = t

def testLens :
    ContextLens OuterStmtIn_Test OuterStmtOut_Test InnerStmtIn_Test InnerStmtOut_Test
                Unit Unit Unit Unit where
  projectStmt := fun ⟨p, q, t⟩ => ⟨p * q, t⟩
  integrateStmt := fun ⟨⟨p, q, _⟩, ⟨_, t', u⟩⟩ => (p, q, t', u)
  projectWit := fun (_ : Unit) => (() : Unit)
  integrateWit := fun (_ : Unit × Unit) => (() : Unit)

def testLensComplete : testLens.IsComplete
      outerRelIn_Test innerRelIn_Test outerRelOut_Test innerRelOut_Test
      (fun ⟨⟨p, q, _⟩, ()⟩ ⟨⟨f, _⟩, ()⟩ => p * q = f) where
  project_complete := fun ⟨p, q, t⟩ () hRelIn => by
    simp [outerRelIn_Test] at hRelIn
    simp [innerRelIn_Test, testLens, hRelIn]
  integrate_complete := fun ⟨p, q, t⟩ _ ⟨f, t', r⟩ _ hRelIn hRelOut' hCompat => by
    simp [outerRelIn_Test] at hRelIn
    simp [innerRelOut_Test] at hRelOut'
    simp at hCompat
    simp [outerRelOut_Test, testLens, hRelIn, ← hRelOut', hCompat]

end

end Test
