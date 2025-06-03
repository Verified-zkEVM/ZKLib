import ArkLib.OracleReduction.Security.Basic

/-!
  # Simple (Oracle) Reduction: Check if a predicate on a statement is satisfied

  This is a zero-round (oracle) reduction.

  1. Reduction version: the input relation is constant on witness, and becomes a predicate on the
  statement. Verifier checks this statement, and returns yes / no.

  Verifier may decide to keep the statement or not (send it to Unit)?

  2. Oracle reduction version: the input relation is constant on witness, and there is an oracle
  computation having as oracles the oracle statements, and taking in the (non-oracle) statement as
  an input (i.e. via `ReaderT`), and returning a `Prop`.

  Verifier performs this oracle computation, and may decide to keep the (oracle) statement or not
-/
