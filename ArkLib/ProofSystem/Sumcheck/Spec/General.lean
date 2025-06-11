/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.ProofSystem.Sumcheck.Spec.SingleRound

/-!
# The Sum-check Protocol

We define the sum-check protocol as a series of Interactive Oracle Reductions (IORs), where the
underlying polynomials are represented using Mathlib's noncomputable types `Polynomial` and
`MvPolynomial`. See `SingleRound.lean` for a single round of the protocol, and the definition of the
sum-check relations.

In the future, we will have files that deal with implementations of the protocol, and we will prove
that those implementations derive security from that of the abstract protocol.

## Protocol Specification

The sum-check protocol is parameterized by the following:
- `R`: the underlying ring (for soundness, required to be finite and a domain)
- `n + 1 : ℕ+`: the number of variables (also number of rounds)
- `deg : ℕ`: the individual degree bound for the polynomial
- `D : Fin m ↪ R`: the set of `m` evaluation points for each variable (for some `m`), represented as
  an injection `Fin m ↪ R`. The image of `D` as a finite subset of `R` is written as
  `Finset.univ.map D`.
- `oSpec : OracleSpec ι`: the set of underlying oracles (e.g. random oracles) that may be needed for
  other reductions. However, the sum-check protocol does _not_ use any oracles.

The sum-check relation has no witness. The statement for the `i`-th round, where `i : Fin (n + 2)`,
 contains:
- `target : R`, which is the target value for sum-check
- `challenges : Fin i → R`, which is the list of challenges sent from the verifier to the prover in
  previous rounds

There is a single oracle statement, which is:
- `poly : MvPolynomial (Fin (n + 2)) R`, the multivariate polynomial that is summed over

The sum-check relation for the `i`-th round checks that:

  `∑ x ∈ (univ.map D) ^ᶠ (n + 1 - i), poly ⸨challenges, x⸩ = target`.

Note that the last statement (when `i = n`) is the output statement of the sum-check protocol.

For `i = 0, ..., n`, the `i`-th round of the sum-check protocol consists of the following:

1. The prover sends a univariate polynomial `pᵢ ∈ R⦃≤ deg⦄[X]` of degree at most `deg`. If the
   prover is honest, then we have:

    `pᵢ(X) = ∑ x ∈ (univ.map D) ^ᶠ (n - i), poly ⸨X ⦃i⦄, challenges, x⸩`.

  Here, `poly ⸨X ⦃i⦄, challenges, x⸩` is the polynomial `poly` evaluated at the concatenation of the
  prior challenges `challenges`, the `i`-th variable as the new indeterminate `X`, and the rest of
  the values `x ∈ (univ.map D) ^ᶠ (n - i)`.

  In the oracle protocol, this polynomial `pᵢ` is turned into an oracle for which the verifier can
  query for evaluations at arbitrary points.

2. The verifier then sends the `i`-th challenge `rᵢ` sampled uniformly at random from `R`.

3. The (oracle) verifier then performs queries for the evaluations of `pᵢ` at all points in
   `(univ.map D)`, and checks that: `∑ x in (univ.map D), pᵢ.eval x = target`.

   If the check fails, then the verifier outputs `failure`.

   Otherwise, it outputs a statement for the next round as follows:
   - `target` is updated to `pᵢ.eval rᵢ`
   - `challenges` is updated to the concatenation of the previous challenges and `rᵢ`

## Notes & TODOs

An annoying issue is that we need to index over `i : Fin (n + 2)`, not `i : Fin (n + 1)`. This is
because existing `Fin` functions works better with `n + 1` which is clearly positive, and not `i :
Fin (n + 1)` (which would imply `n > 0`, but this fact is not apparent).

Note that to represent sum-check as a series of IORs, we will need to implicitly constrain the
degree of the polynomials via using subtypes, such as `Polynomial.degreeLE` and
`MvPolynomial.degreeOf`. This is because the oracle verifier only gets oracle access to evaluating
the polynomials, but does not see the polynomials in the clear.

When this is compiled to an interactive proof, the corresponding polynomial commitment schemes will
enforce that the declared degree bound holds, via letting the (non-oracle) verifier perform explicit
degree checks.

There are some generalizations that we could consider later:

- Generalize to `degs : Fin (n + 2) → ℕ` and `domain : Fin (n + 2) → (Fin m ↪ R)`, e.g. can vary the
  degree bound and the summation domain for each variable

- Generalize the challenges to come from a suitable subset of `R` (e.g. subtractive sets), and not
  necessarily the whole domain. This is used in lattice-based protocols.

- Sumcheck over modules instead of just rings. This will require extending `MvPolynomial` to have
  such a notion of evaluation, something like `evalModule (x : σ → M) (p : MvPolynomial σ R) : M`,
  where we have `[Module R M]`.

## References

[JACM:LFKN92]

[C:BooChiSot21]

-/

namespace Sumcheck

open Polynomial MvPolynomial OracleSpec OracleComp ProtocolSpec Finset

noncomputable section

namespace Spec

variable (R : Type) [CommSemiring R] (d : ℕ) {m : ℕ} (D : Fin m ↪ R) (n : ℕ)

def pSpec : ProtocolSpec ((n + 1) * 2) :=
  fun i => if i % 2 = 0 then (.P_to_V, R⦃≤ d⦄[X]) else (.V_to_P, R)

instance : ∀ i, OracleInterface ((pSpec R d n).Message i) := fun ⟨i, hDir⟩ => by
  by_cases h : i % 2 = 0
  · simp [pSpec, h]; infer_instance
  · simp [pSpec, h]; simp [MessageIdx, pSpec, h] at hDir

instance [VCVCompatible R] : ∀ i, VCVCompatible ((pSpec R d n).Challenge i) := fun ⟨i, hDir⟩ => by
  by_cases h : i % 2 = 0
  · simp [pSpec, h]; simp [pSpec, h] at hDir
  · simp [pSpec, h]; infer_instance

def StmtIn := R

@[reducible]
def OStmtIn : Unit → Type := fun _ => R⦃≤ d⦄[X (Fin (n + 1))]

def WitIn := Unit

def StmtOut := R × (Fin (n + 1) → R)

@[reducible]
def OStmtOut : Unit → Type := fun _ => R⦃≤ d⦄[X (Fin (n + 1))]

def WitOut := Unit

def relIn : (StmtIn R) × (∀ i, OStmtIn R d n i) → WitIn → Prop :=
  fun ⟨target, polyOracle⟩ _ => ∑ x ∈ (univ.map D) ^ᶠ (n + 1), (polyOracle ()).val ⸨x⸩ = target

def relOut : (StmtOut R n) × (∀ i, OStmtOut R d n i) → WitOut → Prop :=
  fun ⟨⟨target, challenges⟩, polyOracle⟩ _ => (polyOracle ()).1 ⸨challenges⸩ = target

def prover : OracleProver (pSpec R d n) []ₒ (StmtIn R) WitIn (StmtOut R n) WitOut
    (OStmtIn R n d) (OStmtOut R n d) := sorry

def verifier : OracleVerifier (pSpec R d n) []ₒ (StmtIn R) (StmtOut R n)
    (OStmtIn R n d) (OStmtOut R n d) := sorry

def reduction : OracleReduction (pSpec R d n) []ₒ (StmtIn R) WitIn (StmtOut R n) WitOut
    (OStmtIn R n d) (OStmtOut R n d) :=
  .mk (prover R d n) (verifier R d n)

variable [VCVCompatible R]

-- /-- Perfect completeness for the (full) sum-check protocol -/
-- theorem reduction_complete : (reduction R d n).perfectCompleteness
--     (relIn R d D n) (relOut R d n) := sorry

-- def stateFunction : Reduction.StateFunction (pSpec R deg n) []ₒ
--   (relIn R n deg D) (relOut R n deg)

-- /-- Round-by-round knowledge soundness for the (full) sum-check protocol -/
-- theorem reduction_sound :

end Spec

-- end for noncomputable section
end

end Sumcheck
