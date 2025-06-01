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

  - `focusStmt : OuterStmtIn → InnerStmtIn`
  - `focusOStmt : (simulation involving OuterOStmtIn to produce InnerOStmtIn)`
  - `focusWit : OuterWitIn → InnerWitIn`
  - `integrateStmt : OuterStmtIn × InnerStmtOut → OuterStmtOut`
  - `integrateOStmt : (simulation involving InnerOStmtOut to produce OuterOStmtOut)`
  - `integrateWit : OuterWitIn × InnerWitOut → OuterWitOut`

  Note that this is very similar to the concept of lenses in programming languages / category
  theory. Namely, transport on the inputs correspond to a `view`/`get` operation (our "focus"),
  while transport on the output corresponds to a `modify`/`set` operation (our "integrate").

  What are some expected properties of the transport (via the connection to lenses)?

  First, we recall the expected properties of lenses:

  1. `get(lens, set(lens, value, store)) = value`
  2. `set(lens, new, set(lens, old, store)) = set(lens, new, store)`
  3. `set(lens, get(lens, store), store) = store`
  4. and more

  What should this mean here?
  - one property not mentioned above, is that the pre-image of `focusInput` should be invariant
    for `integrateOutput`.

  That is, if `focusInput(inp1) = focusInput(inp2) = inp*`, then `integrateOutput(inp1, out)
  = integrateOutput(inp2, out)` for all `out` which is a possible result of runnign the oracle
  reduction on `inp*`. This basically implies a decomposition of sorts between the input to be
  transported.
-/

open OracleSpec OracleComp ProtocolSpec

section Transport

open scoped NNReal

/-- A lens for transporting (non-oracle) statements between outer and inner contexts -/
structure StatementLens (OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut : Type) where
  focusStmt : OuterStmtIn → InnerStmtIn
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
  focusOStmt : QueryImpl [InnerOStmtIn]ₒ
    (ReaderT OuterStmtIn (OracleComp [OuterOStmtIn]ₒ))
  -- To get back an output oracle statement in the outer context, we may simulate it using the input
  -- (non-oracle) statement of the outer context, the output (non-oracle) statement of the inner
  -- context, along with oracle access to the inner output oracle statements
  integrateOStmt : QueryImpl [OuterOStmtOut]ₒ
    (ReaderT (OuterStmtIn × InnerStmtOut) (OracleComp [InnerOStmtOut]ₒ))

/-- A lens for transporting witnesses between outer and inner contexts -/
structure WitnessLens (OuterWitIn OuterWitOut InnerWitIn InnerWitOut : Type) where
  focusWit : OuterWitIn → InnerWitIn
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
    `E (map to innerWitOut) (focusStmt outerStmtIn) transcript queryLog`
  and then post-process the result, which is some `innerWitIn`, to get some `outerWitIn`.

  This processing is exactly the same as a lens in the opposite direction between the outer and
  inner witness types.
-/

/-- Inverse lens between outer and inner witnesses (going the other direction with respect to
  input-output), for extractors / knowledge soundness -/
def WitnessLensInv (OuterWitIn OuterWitOut InnerWitIn InnerWitOut : Type) :=
  WitnessLens OuterWitOut OuterWitIn InnerWitOut InnerWitIn
  -- focusWitInv : InnerWitOut → OuterWitOut
  -- integrateWitInv : InnerWitIn × OuterWitOut → OuterWitIn

/-- Conditions for the lens / transformation to preserve completeness -/
structure ContextLensComplete (OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut : Type)
    (OuterWitIn OuterWitOut InnerWitIn InnerWitOut : Type)
    (outerRelIn : OuterStmtIn → OuterWitIn → Prop)
    (innerRelIn : InnerStmtIn → InnerWitIn → Prop)
    (outerRelOut : OuterStmtOut → OuterWitOut → Prop)
    (innerRelOut : InnerStmtOut → InnerWitOut → Prop)
    extends
      ContextLens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut
                  OuterWitIn OuterWitOut InnerWitIn InnerWitOut where

  focus_complete : ∀ stmtIn witIn,
    outerRelIn stmtIn witIn →
    innerRelIn (focusStmt stmtIn) (focusWit witIn)

  integrate_complete : ∀ stmtIn witIn stmtOut' witOut',
    outerRelIn stmtIn witIn →
    innerRelOut stmtOut' witOut' →
    outerRelOut (integrateStmt (stmtIn, stmtOut')) (integrateWit (witIn, witOut'))

/-- Conditions for the lens / transformation to preserve soundness -/
structure ContextLensSound (OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut : Type)
    (outerLangIn : Set OuterStmtIn) (outerLangOut : Set OuterStmtOut)
    (innerLangIn : Set InnerStmtIn) (innerLangOut : Set InnerStmtOut)
    extends StatementLens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut where

  focus_sound : ∀ outerStmtIn,
    outerStmtIn ∉ outerLangIn → focusStmt outerStmtIn ∉ innerLangIn

  integrate_sound : ∀ outerStmtIn innerStmtOut,
    outerStmtIn ∉ outerLangIn → innerStmtOut ∉ innerLangOut →
      integrateStmt (outerStmtIn, innerStmtOut) ∈ outerLangOut

/-- Conditions for the lens / transformation to preserve knowledge soundness

(TODO: double-check) -/
structure ContextLensKnowledgeSound
    (OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut : Type)
    (OuterWitIn OuterWitOut InnerWitIn InnerWitOut : Type)
    (outerRelIn : OuterStmtIn → OuterWitIn → Prop)
    (innerRelIn : InnerStmtIn → InnerWitIn → Prop)
    (outerRelOut : OuterStmtOut → OuterWitOut → Prop)
    (innerRelOut : InnerStmtOut → InnerWitOut → Prop)
    extends
      ContextLens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut
                  OuterWitIn OuterWitOut InnerWitIn InnerWitOut where

  focus_knowledge_sound : ∀ outerStmtIn outerWitIn,
    outerRelIn outerStmtIn outerWitIn → innerRelIn (focusStmt outerStmtIn) (focusWit outerWitIn)

  integrate_knowledge_sound : ∀ outerStmtIn outerWitIn innerStmtOut innerWitOut,
    outerRelIn outerStmtIn outerWitIn →
    innerRelOut innerStmtOut innerWitOut →
    outerRelOut (integrateStmt (outerStmtIn, innerStmtOut))
                (integrateWit (outerWitIn, innerWitOut))

/-
  The above two soundness / knowledge soundness conditions should be the same for all notions,
  i.e. regular, state-restoration, round-by-round, etc.,
  since we only act on the input-output interface
-/

variable {n : ℕ} {pSpec : ProtocolSpec n} {ι : Type} [DecidableEq ι] {oSpec : OracleSpec ι}
  {OuterStmtIn OuterWitIn OuterStmtOut OuterWitOut : Type}
  {InnerStmtIn InnerWitIn InnerStmtOut InnerWitOut : Type}
  [∀ i, VCVCompatible (pSpec.Challenge i)] [oSpec.FiniteRange]

/-- How does the prover change? Only in input & output, and keep around the input statement &
  witness -/
def Prover.transport
    (lens : ContextLens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut
      OuterWitIn OuterWitOut InnerWitIn InnerWitOut)
    (P : Prover pSpec oSpec InnerStmtIn InnerWitIn InnerStmtOut InnerWitOut) :
      Prover pSpec oSpec OuterStmtIn OuterWitIn OuterStmtOut OuterWitOut where
  PrvState := fun i => P.PrvState i × OuterStmtIn × OuterWitIn
  input := fun stmtIn witIn =>
    ⟨P.input (lens.focusStmt stmtIn) (lens.focusWit witIn), stmtIn, witIn⟩
  sendMessage := fun i ⟨prvState, stmtIn, witIn⟩ => do
    let ⟨msg, prvState'⟩ ← P.sendMessage i prvState
    return ⟨msg, ⟨prvState', stmtIn, witIn⟩⟩
  receiveChallenge := fun i ⟨prvState, stmtIn, witIn⟩ chal =>
    ⟨P.receiveChallenge i prvState chal, stmtIn, witIn⟩
  output := fun ⟨prvState, stmtIn, witIn⟩ =>
    let ⟨innerStmtOut, innerWitOut⟩ := P.output prvState
    ⟨lens.integrateStmt (stmtIn, innerStmtOut), lens.integrateWit (witIn, innerWitOut)⟩

def Verifier.transport
    (lens : StatementLens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut)
    (V : Verifier pSpec oSpec InnerStmtIn InnerStmtOut) :
      Verifier pSpec oSpec OuterStmtIn OuterStmtOut where
  verify := fun stmtIn transcript => do
    let innerStmtIn := lens.focusStmt stmtIn
    let innerStmtOut ← V.verify innerStmtIn transcript
    return lens.integrateStmt (stmtIn, innerStmtOut)

def Reduction.transport
    (lens : ContextLens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut
      OuterWitIn OuterWitOut InnerWitIn InnerWitOut)
    (R : Reduction pSpec oSpec InnerStmtIn InnerWitIn InnerStmtOut InnerWitOut) :
      Reduction pSpec oSpec OuterStmtIn OuterWitIn OuterStmtOut OuterWitOut where
  prover := R.prover.transport lens
  verifier := R.verifier.transport lens.toStatementLens

open Reduction in
def StraightlineExtractor.transport
    (lens : ContextLens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut
      OuterWitIn OuterWitOut InnerWitIn InnerWitOut)
    (lensInv : WitnessLensInv OuterWitIn OuterWitOut InnerWitIn InnerWitOut)
    (E : @StraightlineExtractor _ pSpec _ oSpec InnerStmtIn InnerWitIn InnerWitOut) :
      @StraightlineExtractor _ pSpec _ oSpec OuterStmtIn OuterWitIn OuterWitOut :=
  fun outerWitOut outerStmtIn fullTranscript proveQueryLog verifyQueryLog =>
    let innerStmtIn := lens.focusStmt outerStmtIn
    let innerWitOut := lensInv.focusWit outerWitOut
    let innerWitIn := E innerWitOut innerStmtIn fullTranscript proveQueryLog verifyQueryLog
    lensInv.integrateWit (outerWitOut, innerWitIn)

theorem Prover.run_transport
    {lens : ContextLens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut
      OuterWitIn OuterWitOut InnerWitIn InnerWitOut}
    {outerStmtIn : OuterStmtIn} {outerWitIn : OuterWitIn}
    (P : Prover pSpec oSpec InnerStmtIn InnerWitIn InnerStmtOut InnerWitOut) :
      (P.transport lens).run outerStmtIn outerWitIn = do
        let ⟨innerStmtOut, innerWitOut, fullTranscript⟩ ←
          P.run (lens.focusStmt outerStmtIn) (lens.focusWit outerWitIn)
        return ⟨lens.integrateStmt (outerStmtIn, innerStmtOut),
                lens.integrateWit (outerWitIn, innerWitOut),
                fullTranscript⟩ := by
  unfold Prover.run Prover.runToRound
  simp [Prover.transport]
  sorry

theorem Reduction.run_transport
    {lens : ContextLens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut
      OuterWitIn OuterWitOut InnerWitIn InnerWitOut}
    {outerStmtIn : OuterStmtIn} {outerWitIn : OuterWitIn}
    (R : Reduction pSpec oSpec InnerStmtIn InnerWitIn InnerStmtOut InnerWitOut) :
      (R.transport lens).run outerStmtIn outerWitIn = do
        let ⟨⟨prvInnerStmtOut, innerWitOut⟩, verInnerStmtOut, fullTranscript⟩ ←
          R.run (lens.focusStmt outerStmtIn) (lens.focusWit outerWitIn)
        return ⟨⟨lens.integrateStmt (outerStmtIn, prvInnerStmtOut),
                lens.integrateWit (outerWitIn, innerWitOut)⟩,
                lens.integrateStmt (outerStmtIn, verInnerStmtOut),
                fullTranscript⟩ := by
  unfold Reduction.run
  simp [Reduction.transport, Prover.run_transport, Verifier.transport]
  sorry

theorem Reduction.runWithLog_transport
    {lens : ContextLens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut
      OuterWitIn OuterWitOut InnerWitIn InnerWitOut}
    {outerStmtIn : OuterStmtIn} {outerWitIn : OuterWitIn}
    (R : Reduction pSpec oSpec InnerStmtIn InnerWitIn InnerStmtOut InnerWitOut) :
      (R.transport lens).runWithLog outerStmtIn outerWitIn = do
        let ⟨⟨prvInnerStmtOut, innerWitOut⟩, verInnerStmtOut, fullTranscript, queryLog⟩ ←
          R.runWithLog (lens.focusStmt outerStmtIn) (lens.focusWit outerWitIn)
        return ⟨⟨lens.integrateStmt (outerStmtIn, prvInnerStmtOut),
          lens.integrateWit (outerWitIn, innerWitOut)⟩,
          lens.integrateStmt (outerStmtIn, verInnerStmtOut), fullTranscript, queryLog⟩ := by
  unfold Reduction.runWithLog
  simp [Reduction.transport, Prover.run_transport, Verifier.transport]
  sorry

/--
  Informally, if `(outerStmtIn, outerWitIn) ∈ relIn`, we want `(innerStmtIn, innerWitIn) ∈ relIn'`.
  Using the completeness guarantee, we get that `(innerStmtOut, innerWitOut) ∈ relOut'`.
  From these, we need to deduce that `(outerStmtOut, outerWitOut) ∈ relOut`.
-/
theorem Reduction.transport_completeness
    {relIn : OuterStmtIn → OuterWitIn → Prop} {relOut : OuterStmtOut → OuterWitOut → Prop}
    {relIn' : InnerStmtIn → InnerWitIn → Prop} {relOut' : InnerStmtOut → InnerWitOut → Prop}
    {completenessError : ℝ≥0}
    (lens : ContextLensComplete OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut
      OuterWitIn OuterWitOut InnerWitIn InnerWitOut relIn relIn' relOut relOut')
    (R : Reduction pSpec oSpec InnerStmtIn InnerWitIn InnerStmtOut InnerWitOut)
    (h : R.completeness relIn' relOut' completenessError) :
      (R.transport lens.toContextLens).completeness relIn relOut completenessError := by
  unfold completeness at h ⊢
  intro outerStmtIn outerWitIn hRelIn
  have hR := h (lens.focusStmt outerStmtIn) (lens.focusWit outerWitIn)
    (lens.focus_complete _ _ hRelIn)
  rw [Reduction.run_transport]
  refine le_trans hR ?_
  simp
  refine probEvent_mono ?_
  intro _ _ hRelOut' -- This hRelOut' is for InnerStmtOut and InnerWitOut
  sorry -- Need to correctly apply lens.relOut_implied_by
  -- exact lens.relOut_implied_by _ _ _ _ hRelIn hRelOut'

/-- -/
theorem Reduction.transport_soundness
    {langIn : Set OuterStmtIn} {langOut : Set OuterStmtOut}
    {langIn' : Set InnerStmtIn} {langOut' : Set InnerStmtOut}
    {soundnessError : ℝ≥0}
    (lens : ContextLensSound OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut
      langIn langOut langIn' langOut')
    (V : Verifier pSpec oSpec InnerStmtIn InnerStmtOut)
    (h : Reduction.soundness langIn' langOut' V soundnessError) :
      Reduction.soundness langIn langOut
        (V.transport lens.toStatementLens) soundnessError := by
  unfold soundness at h ⊢
  intro outerStmtIn hOuterStmtIn OuterWitIn OuterWitOut outerWitIn prover
  sorry

theorem Reduction.transport_knowledgeSoundness
    {relIn : OuterStmtIn → OuterWitIn → Prop} {relOut : OuterStmtOut → OuterWitOut → Prop}
    {relIn' : InnerStmtIn → InnerWitIn → Prop} {relOut' : InnerStmtOut → InnerWitOut → Prop}
    {soundnessError : ℝ≥0}
    (lens : ContextLensKnowledgeSound OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut
      OuterWitIn OuterWitOut InnerWitIn InnerWitOut relIn relIn' relOut relOut')
    (V : Verifier pSpec oSpec InnerStmtIn InnerStmtOut)
    (h : Reduction.knowledgeSoundness relIn' relOut' V soundnessError) :
      Reduction.knowledgeSoundness relIn relOut
        (V.transport lens.toContextLens.toStatementLens) soundnessError := by
  unfold knowledgeSoundness at h ⊢
  obtain ⟨E, h'⟩ := h
  stop
  refine ⟨E.transport lens lens.toContextLensInv, ?_⟩ -- lensInv needs to be correctly derived
  intro outerStmtIn outerWitIn hRelIn
  have hR := h (lens.focusStmt outerStmtIn) (lens.focusWit outerWitIn)
    (lens.focus_knowledge_sound _ _ hRelIn)
  rw [Reduction.run_transport]
  sorry

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
  focusStmt := fun ⟨p, q, t⟩ => ⟨p * q, t⟩
  integrateStmt := fun ⟨⟨p, q, _⟩, ⟨_, t', u⟩⟩ => (p, q, t', u)
  focusWit := fun (_ : Unit) => (() : Unit)
  integrateWit := fun (_ : Unit × Unit) => (() : Unit)

def testLensComplete :
    ContextLensComplete OuterStmtIn_Test OuterStmtOut_Test InnerStmtIn_Test InnerStmtOut_Test
                        Unit Unit Unit Unit
                        outerRelIn_Test innerRelIn_Test outerRelOut_Test innerRelOut_Test where
  toContextLens := testLens
  focus_complete := fun ⟨p, q, t⟩ () hRelIn => by
    simp [outerRelIn_Test] at hRelIn
    simp [innerRelIn_Test, testLens, hRelIn] -- Using testLens.focusStmt
  integrate_complete := fun ⟨p, q, t⟩ () ⟨f, t', r⟩ () hRelIn hRelOut' => by
    simp [outerRelIn_Test] at hRelIn
    simp [innerRelOut_Test] at hRelOut'
    simp [outerRelOut_Test, testLens, hRelIn, hRelOut'] -- Using testLens.integrateStmt
    sorry

end

end Test
