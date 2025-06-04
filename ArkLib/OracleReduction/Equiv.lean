import ArkLib.OracleReduction.Security.Basic
import ArkLib.OracleReduction.LiftContext.Basic

/-!
  # Equivalence / Isomorphism of Oracle Reductions

  We define observational equivalence between provers and verifiers in an I(O)R.

  We also define equivalence between IORs, in the sense that the statements and witnesses are
  equivalent, and their mapping commute with the reduction (both for the prover and the verifier).

  NOTE: this is now a special case of `liftContext`

  -----------------------------------------------------------------------------------------------

  We will also need to convert between specification and executable models.

  In the best case, we have an isomorphism of the datatypes, which also intertwines with the
  implementation of the prover & verifier.

  However, we may need to deal with more complicated situation. For instance, can we transfer
  results between minor modifications to the protocol? What about when the isomorphism is not exact?

  For the simplest case, it seems we want the following:

  - Assume we have an I(O)R (i.e. the abstract specification): from `RIn₁ : StmtIn₁ × WitIn₁ → Prop`
      to `ROut₁ : StmtOut₁ × WitOut₁ → Prop`.

    We have another I(O)R (i.e. the executable implementation): from `RIn₂ : StmtIn₂ × WitIn₂ →
      Prop` to `ROut₂ : StmtOut₂ × WitOut₂ → Prop`.

    Assume there are mappings in opposite directions:
    `f{Stmt/Wit}{In/Out}₁ : {Stmt/Wit}{In/Out}₁ → {Stmt/Wit}{In/Out}₂` &
    `g{Stmt/Wit}{In/Out}₂ : {Stmt/Wit}{In/Out}₂ → {Stmt/Wit}{In/Out}₁`.
    (for IOR, also mappings between the oracle statements)

  - Then we may transfer security properties from the first to the second I(O)R provided that:
    - Under these mappings, the relations are equivalent
    - Under these mappings, the prover & verifier are equivalent

  - Note that we do not need to require `f/g` to form an equivalence, since this may be too
    restrictive in practice (i.e. concrete polynomial datatypes may contain zero-padding of the
    highest coefficients).

-/

-- First, what does it mean for two oracle computations to be equivalent?

namespace OracleComp

open OracleSpec

variable {ι ιₜ : Type} {spec : OracleSpec ι} {specₜ : OracleSpec ιₜ} {α σ : Type} [spec.FiniteRange]

#check OracleComp.PolyQueries

def oa1 : ProbComp (ℕ × ℕ) := do
  let x ← query (spec := unifSpec) 0 ()
  let y ← query (spec := unifSpec) 1 ()
  return (x, y)

def oa2 : ProbComp (ℕ × ℕ) := do
  let y ← query (spec := unifSpec) 1 ()
  let x ← query (spec := unifSpec) 0 ()
  return (x, y)

theorem oa1_eq_oa2 : oa1 = oa2 := by
  simp [oa1, oa2]
  sorry

@[simp]
theorem unifSpec_range (n : ℕ) : unifSpec.range n = Fin (n + 1) := rfl

def distEquiv (oa ob : OracleComp spec α) : Prop :=
  evalDist oa = evalDist ob

theorem oa1_distEquiv_oa2 : distEquiv oa1 oa2 := by
  simp [oa1, oa2, distEquiv]
  ext i
  rcases i with none | ⟨x, y⟩
  · simp [tsum_eq_sum (s := Finset.univ) (by simp)]
    simp [OptionT.run, OptionT.lift, OptionT.mk, Functor.map, Option.elimM]
    sorry
  · simp [tsum_eq_sum (s := Finset.univ) (by simp)]
    simp [OptionT.run, OptionT.lift, OptionT.mk, Functor.map]
    -- simp [tsum_eq_sum (s := Finset.univ) (by simp)]
    -- cases on x and y
    sorry

open SimOracle in
def obsEquiv (oa ob : OracleComp spec α) : Prop :=
  ∀ f : (i : ι) → spec.domain i → spec.range i,
    simulateQ (fnOracle spec f) oa = simulateQ (fnOracle spec f) ob

-- Note: observational equivalence does not imply distributional equivalence, since the distribution
-- of each new query is independently random

theorem oa1_obsEquiv_oa2 : obsEquiv oa1 oa2 := by
  simp only [obsEquiv, unifSpec_range, oa1, Nat.reduceAdd, Fin.val_eq_zero, bind_pure_comp,
    simulateQ_bind, simulateQ_query, simulateQ_map, oa2]
  intro f
  simp only [SimOracle.fnOracle, unifSpec_range, SimOracle.statelessOracle, liftM, monadLift,
    MonadLift.monadLift, StateT.lift, Nat.reduceAdd, bind_pure_comp, map_pure, Prod.map_apply,
    id_eq]
  sorry

end OracleComp

section Relation

variable {Stmt Wit Stmt' Wit' : Type}

def Relation.equiv (f : Stmt ≃ Stmt') (g : Wit ≃ Wit') (R : Stmt → Wit → Prop) (R' : Stmt' → Wit' → Prop) : Prop :=
  ∀ stmt : Stmt, ∀ wit : Wit, R stmt wit ↔ R' (f stmt) (g wit)

theorem Relation.equiv_symm (f : Stmt ≃ Stmt') (g : Wit ≃ Wit') (R : Stmt → Wit → Prop) (R' : Stmt' → Wit' → Prop) :
  Relation.equiv f g R R' ↔ Relation.equiv f.symm g.symm R' R := by
  simp [Relation.equiv]
  constructor
  · intro h
    intro stmt' wit'
    simpa using (h (f.symm stmt') (g.symm wit')).symm
  · intro h
    intro stmt wit
    simpa using (h (f stmt) (g wit)).symm

-- TODO: define quotienting (i.e. statement is a product type and relation only depends on one component)

end Relation

namespace Reduction



end Reduction
