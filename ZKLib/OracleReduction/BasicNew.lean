import ZKLib.OracleReduction.ToOracle


/-!

# Interactive Oracle Reductions

We give a **new** modeling of IORs based on session types.

-/

inductive ProtocolStep where
  | P_to_V (nextStep : ProtocolStep)
  | V_to_P (nextStep : ProtocolStep)
  | Final

inductive Protocol where
  | mk (steps : List ProtocolStep)



-- Potential new abstraction takes in input statement, input witness, return first message, takes a
-- challenge, returns output statement & output witness

-- def NewProverType := StmtIn × WitIn → (FirstMessage × (FirstChallenge → StmtOut × WitOut))

-- def NewVerifierType := StmtIn × (FirstMessage → FirstChallenge × (StmtOut))

universe u₁ u₂ u₃ u₄ u₅

variable (m₁ : Type → Type 1) [Monad m₁]
variable (m₂ : Type 1 → Type 2) [Monad m₂]
variable (m₃ : Type 2 → Type 3) [Monad m₃]
variable (m₄ : Type 3 → Type 4) [Monad m₄]

#check StateM

#check OracleComp

variable (m : Type → Type) [Monad m] (StmtIn Message1 Challenge Message2 StmtOut : Type)

def ProverSigmaProtocol := StmtIn → m (Message1 × m (Challenge → m (Message2 × m (StmtOut))))

def ProverSigmaProtocol' :=
  StmtIn → m₄ (Message1 × m₃ (Challenge → m₂ (Message2 × m₁ (StmtOut))))

variable {PrvState : Fin 4 → Type}

-- Does this match the old type?

-- Old type would have:
-- input: Statement → PrvState 0
-- sendMessage1: PrvState 0 → m (Message1 × PrvState 1)
-- receiveChallenge: PrvState 1 → Challenge → m (Message2 × PrvState 2)
-- sendMessage2: PrvState 2 → m (Message2 × PrvState 3)
-- output: PrvState 3 → NewStatement

-- You would compose these together as follows
-- do
-- let st0 := input stmt
-- let (msg1, st1) ← sendMessage1 st0
-- (the other party generates a challenge)
-- let st2 := receiveChallenge st1 challenge
-- let (msg2, st3) ← sendMessage2 st2
-- let newStmt := output st3
-- return newStmt

-- de-sugaring do-notation, this would be:
-- (input is some `challenge`)
-- (pure input stmt) >>= fun st0 =>
-- sendMessage1 st0 >>= fun (msg1, st1) =>
-- (pure receiveChallenge st1 challenge) >>= fun st2 =>
-- sendMessage2 st2 >>= fun (msg2, st3) =>
-- (pure output st3)

def exampleProverSigmaProtocol
    (input : StmtIn → PrvState 0)
    (sendMessage1 : PrvState 0 → m (Message1 × PrvState 1))
    (receiveChallenge : PrvState 1 → Challenge → PrvState 2)
    (sendMessage2 : PrvState 2 → m (Message2 × PrvState 3))
    (output : PrvState 3 → StmtOut) :
    ProverSigmaProtocol m StmtIn Message1 Challenge Message2 StmtOut :=
  fun stmt => (do
    let st0 := input stmt
    let (msg1, st1) ← sendMessage1 st0
    return (msg1, (do
      return (fun challenge => (do
        let st2 := receiveChallenge st1 challenge
        let (msg2, st3) ← sendMessage2 st2
        return (msg2, (do return output st3)))))))

def ProverSigmaProtocol.run
    (stmtIn : StmtIn) (challenge : Challenge)
    (prover : ProverSigmaProtocol m StmtIn Message1 Challenge Message2 StmtOut) :
    m (Message1 × Message2 × StmtOut) := do
  let (msg1, rest) ← prover stmtIn
  let (msg2, stmtOut) ← (← rest) challenge
  return (msg1, msg2, ← stmtOut)

-- What about composition?
variable (StmtMid : Type)

def ProverFirstRound := StmtIn → m (Message1 × m (StmtMid))

def ProverRest := StmtMid → m (Challenge → m (Message2 × m (StmtOut)))

def composeProvers
    (proverFirst : ProverFirstRound m StmtIn Message1 StmtMid)
    (proverRest : ProverRest m Challenge Message2 StmtOut StmtMid) :
    ProverSigmaProtocol m StmtIn Message1 Challenge Message2 StmtOut :=
  fun stmt => do
    let (msg1, rest) ← proverFirst stmt
    let stmtMid ← rest
    let cont ← proverRest stmtMid
    return (msg1, (do return cont))


section StatelessSessionTypes -- New section for the stateless session-type like definitions

variable {n : ℕ} {ι : Type} {oSpec : OracleSpec ι}

-- /-- Represents the type of the Prover's interaction logic from step `k` onwards.
--     The context (initial state, prior messages/challenges) is implicit in the function closure.
--     Steps can perform Oracle computations.
--     When `k = n`, it produces the final output. -/
-- def ProverContinuation (pSpec : ProtocolSpec n) (k : Fin (n + 1)) (PrvState0 StmtOut WitOut : Type) : Type :=
--   match k.val with
--   | k_val =>
--     if h_k_lt_n : k_val < n then
--       let current_step_index : Fin n := ⟨k_val, h_k_lt_n⟩
--       match pSpec.getDir current_step_index with
--       | .P_to_V => -- Prover sends message k
--         -- Computes (message k, continuation for k+1)
--         OracleComp oSpec (pSpec.getType current_step_index × ProverContinuation pSpec k.succ PrvState0 StmtOut WitOut)
--       | .V_to_P => -- Prover receives challenge k
--         -- Expects challenge k, then computes continuation for k+1
--         pSpec.getType current_step_index → OracleComp oSpec (ProverContinuation pSpec k.succ PrvState0 StmtOut WitOut)
--     else -- k_val = n, interaction finished
--       -- Base case: computes final output
--       OracleComp oSpec (StmtOut × WitOut)

-- /-- A stateless Prover defined using continuations, allowing oracle queries.
--     It's a function that takes the initial statement and an arbitrary initial prover state
--     and returns the interaction logic starting from step 0. -/
-- def StatelessProver (pSpec : ProtocolSpec n) (oSpec : OracleSpec ι) (StmtIn PrvState0 StmtOut WitOut : Type) : Type :=
--   StmtIn → PrvState0 → ProverContinuation pSpec 0 PrvState0 StmtOut WitOut

-- /-- Represents the type of the Verifier's interaction logic from step `k` onwards.
--     The context (initial statement, prior messages/challenges) is implicit in the function closure.
--     Steps can perform Oracle computations.
--     When `k = n`, it produces the final output. -/
-- def VerifierContinuation (pSpec : ProtocolSpec n) (oSpec : OracleSpec ι) (k : Fin (n + 1)) (StmtIn StmtOut : Type) : Type :=
--   match k.val with
--   | k_val =>
--     if h_k_lt_n : k_val < n then
--       let current_step_index : Fin n := ⟨k_val, h_k_lt_n⟩
--       match pSpec.getDir current_step_index with
--       | .P_to_V => -- Verifier receives message k
--         -- Expects message k, then computes continuation for k+1
--         pSpec.getType current_step_index → OracleComp oSpec (VerifierContinuation pSpec oSpec k.succ StmtIn StmtOut)
--       | .V_to_P => -- Verifier sends challenge k
--         -- Computes (challenge k, continuation for k+1)
--         OracleComp oSpec (pSpec.getType current_step_index × VerifierContinuation pSpec oSpec k.succ StmtIn StmtOut)
--     else -- k_val = n, interaction finished
--       -- Base case: computes final output StmtOut
--       OracleComp oSpec StmtOut

-- /-- A stateless Verifier defined using continuations, allowing oracle queries.
--     It's a function that takes the initial statement and returns
--     the interaction logic starting from step 0. -/
-- def StatelessVerifier (pSpec : ProtocolSpec n) (oSpec : OracleSpec ι) (StmtIn StmtOut : Type) : Type :=
--   StmtIn → VerifierContinuation pSpec oSpec 0 StmtIn StmtOut

-- -- Example Protocol: Non-interactive, Prover sends Nat > StmtIn
-- namespace ExampleProtocol

-- def pSpec : ProtocolSpec 1 := ![(.P_to_V, Nat)]

-- def StmtIn := Nat
-- def WitIn := Nat
-- def PrvState0 := WitIn
-- def StmtOutP := Unit
-- def WitOutP := Unit
-- def StmtOutV := Bool

-- -- An honest prover for the example protocol
-- def honestProver : StatelessProver pSpec default StmtIn PrvState0 StmtOutP WitOutP :=
--   fun (_ : StmtIn) (wit : WitIn) =>
--     -- Step 0 (k=0): Prover sends message
--     let message : Nat := wit -- Send the witness
--     let nextContinuation : ProverContinuation pSpec 1 PrvState0 StmtOutP WitOutP :=
--       -- Step 1 (k=1): Base case, return final output
--       pure ((), ()) -- Return (Unit, Unit)
--     pure (message, nextContinuation)

-- -- A verifier for the example protocol
-- def verifier : StatelessVerifier pSpec default StmtIn StmtOutV :=
--   fun (stmt : StmtIn) =>
--     -- Step 0 (k=0): Verifier receives message
--     fun (message : Nat) =>
--       -- Step 1 (k=1): Base case, compute final output
--       let nextContinuation : VerifierContinuation pSpec default 1 StmtIn StmtOutV :=
--         pure (message > stmt) -- Check if message > statement
--       pure nextContinuation

-- end ExampleProtocol

end StatelessSessionTypes
