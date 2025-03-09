/-
Copyright (c) 2024 ZKLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import VCVio
import ZKLib.Data.MvPolynomial.Notation
-- import ZKLib.Data.MlPoly.Basic

/-!
  # Definitions and Instances for `ToOracle`

  We define `ToOracle` and give instances for the following:

  - Univariate and multivariate polynomials. These instances turn polynomials into oracles for which
    one can query at a point, and the response is the evaluation of the polynomial on that point.

  - Vectors. This instance turns vectors into oracles for which one can query specific positions.
-/

/-- `⊕ᵥ` is notation for `Sum.elim`, e.g. sending `α → γ` and `β → γ` to `α ⊕ β → γ`. -/
infixr:35 " ⊕ᵥ " => Sum.elim

open OracleComp OracleSpec OracleQuery

variable {ι ιₜ : Type}

@[reducible]
def SimOracle.Stateful (spec : OracleSpec ι) (specₜ : OracleSpec ιₜ) (σ : Type) :=
  QueryImpl spec (StateT σ (OracleComp specₜ))

@[reducible]
def SimOracle.Stateless (spec : OracleSpec ι) (specₜ : OracleSpec ιₜ) :=
  QueryImpl spec (OracleComp specₜ)

@[reducible]
def SimOracle.Impl (spec : OracleSpec ι) := QueryImpl spec Option

namespace SimOracle

variable {ι₁ ι₂ ιₜ₁ ιₜ₂ : Type} {spec : OracleSpec ι} {spec₁ : OracleSpec ι₁}
  {spec₂ : OracleSpec ι₂} {specₜ : OracleSpec ιₜ} {specₜ₁ : OracleSpec ιₜ₁}
  {specₜ₂ : OracleSpec ιₜ₂} {σ τ α β : Type}

variable [DecidableEq ι]

open OracleSpec

def fnOracle (spec : OracleSpec ι) (f : (i : ι) → spec.domain i → spec.range i) :
    SimOracle.Impl spec where
  impl | query i t => f i t

def statelessOracle (baseSpec : OracleSpec ιₜ) (spec : OracleSpec ι)
    (f : (i : ι) → spec.domain i → spec.range i) :
    SimOracle.Stateless (baseSpec ++ₒ spec) baseSpec where
  impl
  | query (.inl i) t => query i t
  | query (.inr i) t => pure (f i t)

-- instance : (loggingOracle (spec := spec)).IsTracking where
--   state_indep | query _ _, _ => rfl

def append' (so₁ : SimOracle.Stateful spec₁ specₜ₁ σ) (so₂ : SimOracle.Stateful spec₂ specₜ₂ τ) :
    SimOracle.Stateful (spec₁ ++ₒ spec₂) (specₜ₁ ++ₒ specₜ₂) (σ × τ) where
  impl
  | query (.inl i) t => fun (s₁, s₂) ↦ do
      let (u, s₁') ← so₁.impl (query i t) s₁; return (u, s₁', s₂)
  | query (.inr i) t => fun (s₁, s₂) ↦ do
      let (u, s₂') ← so₂.impl (query i t) s₂; return (u, s₁, s₂')

def dedup {ι : Type} (spec : OracleSpec ι) : SimOracle.Stateless (spec ++ₒ spec) spec where
  impl
  | query (.inl i) t => query i t
  | query (.inr i) t => query i t

-- theorem append'_dedup (so₁ : SimOracle spec₁ specₜ σ) (so₂ : SimOracle spec₂ specₜ τ) :
--     append so₁ so₂ = (dedup specₜ ∘ₛ append' so₁ so₂).equivState (.prodPUnit _) := by
--   sorry

-- /-- Answer all oracle queries to `oSpec` with a deterministic function `f` having the same domain
--   and range as `oSpec`. -/
-- def fnOracle {ι : Type} (spec : OracleSpec ι)
--     (f : (i : ι) → spec.domain i → spec.range i) : SimOracle spec []ₒ PUnit :=
--   statelessOracle fun (query i q) ↦ pure (f i q)

def lift {ι₁ ι₂ ι : Type} {σ : Type} (oSpec₁ : OracleSpec ι₁) (oSpec₂ : OracleSpec ι₂)
    (oSpec : OracleSpec ι) (so : SimOracle.Stateful oSpec₁ oSpec₂ σ) :
      SimOracle.Stateful (oSpec ++ₒ oSpec₁) (oSpec ++ₒ oSpec₂) σ where
  impl := fun q s => match q with
    | query (.inl i) q => do return ⟨← query i q, s⟩
    | query (.inr i) q => so.impl (query (spec := oSpec₁) i q) s

-- def liftLeft' {ι₁ ι₂ ι : Type} {σ : Type} {oSpec₁ : OracleSpec ι₁} {oSpec₂ : OracleSpec ι₂}
--     (oSpec : OracleSpec ι) (so : SimOracle oSpec₁ oSpec₂ σ) :
--       SimOracle (oSpec ++ₒ oSpec₁) (oSpec ++ₒ oSpec₂) σ :=
--   (append' idOracle so).equivState (.punitProd σ)

def liftLeftNil {ι : Type} {σ : Type} (oSpec : OracleSpec ι) :
    SimOracle.Stateful ([]ₒ ++ₒ oSpec) oSpec σ where impl
  | query (.inr i) q => fun s ↦ do return ⟨← query i q, s⟩

def liftRightNil {ι : Type} {σ : Type} (oSpec : OracleSpec ι) :
    SimOracle.Stateful (oSpec ++ₒ []ₒ) oSpec σ where impl
  | query (.inl i) q => fun s ↦ do return ⟨← query i q, s⟩

end SimOracle

/-- `ToOracle` is a type class that provides an oracle interface for a type `Message`. It
    consists of a query type `Query`, a response type `Response`, and a function `oracle` that
    transforms a message `m : Message` into a function `Query → Response`. -/
@[ext]
class ToOracle (Message : Type) where
  Query : Type
  Response : Type
  oracle : Message → Query → Response

namespace ToOracle

open SimOracle

def toOracleSpec {ι : Type} (v : ι → Type) [O : ∀ i, ToOracle (v i)] :
    OracleSpec ι := fun i => ((O i).Query, (O i).Response)

notation "[" term "]ₒ" => toOracleSpec term

instance {ι : Type} (v : ι → Type) [O : ∀ i, ToOracle (v i)]
    [h : ∀ i, DecidableEq (Query (v i))]
    [h' : ∀ i, DecidableEq (Response (v i))] :
    [v]ₒ.DecidableEq where
  domain_decidableEq' := h
  range_decidableEq' := h'

instance {ι : Type} (v : ι → Type) [O : ∀ i, ToOracle (v i)]
    [h : ∀ i, Fintype (Response (v i))]
    [h' : ∀ i, Inhabited (Response (v i))] :
    [v]ₒ.FiniteRange where
  range_fintype' := h
  range_inhabited' := h'

@[reducible, inline]
instance {ι₁ : Type} {T₁ : ι₁ → Type} [∀ i, ToOracle (T₁ i)]
    {ι₂ : Type} {T₂ : ι₂ → Type} [∀ i, ToOracle (T₂ i)] : ∀ i, ToOracle (Sum.elim T₁ T₂ i) :=
  fun i => match i with
    | .inl i => by dsimp; infer_instance
    | .inr i => by dsimp; infer_instance

def append {ι₁ : Type} {T₁ : ι₁ → Type} [∀ i, ToOracle (T₁ i)]
    {ι₂ : Type} {T₂ : ι₂ → Type} [∀ i, ToOracle (T₂ i)] : OracleSpec (ι₁ ⊕ ι₂) :=
  [Sum.elim T₁ T₂]ₒ

/-- Combines multiple oracle specifications into a single oracle by routing queries to the
      appropriate underlying oracle. Takes:
    - A base oracle specification `oSpec`
    - An indexed type family `T` with `ToOracle` instances
    - Values of that type family
  Returns a stateless oracle that routes queries to the appropriate underlying oracle. -/
def simOracle {ι : Type} (oSpec : OracleSpec ι) {ι' : Type} {T : ι' → Type}
    [∀ i, ToOracle (T i)] (t : (i : ι') → T i) : SimOracle.Stateless (oSpec ++ₒ [T]ₒ) oSpec :=
  SimOracle.statelessOracle _ _ (fun i q => oracle (t i) q)

/-- Combines multiple oracle specifications into a single oracle by routing queries to the
      appropriate underlying oracle. Takes:
    - A base oracle specification `oSpec`
    - Two indexed type families `T₁` and `T₂` with `ToOracle` instances
    - Values of those type families
  Returns a stateless oracle that routes queries to the appropriate underlying oracle. -/
def simOracle2 {ι : Type} (oSpec : OracleSpec ι)
    {ι₁ : Type} {T₁ : ι₁ → Type} [∀ i, ToOracle (T₁ i)]
    {ι₂ : Type} {T₂ : ι₂ → Type} [∀ i, ToOracle (T₂ i)]
    (t₁ : ∀ i, T₁ i) (t₂ : ∀ i, T₂ i) : SimOracle.Stateless (oSpec ++ₒ ([T₁]ₒ ++ₒ [T₂]ₒ)) oSpec :=
  SimOracle.statelessOracle _ _ (fun i q => match i with
    | .inl i => oracle (t₁ i) q
    | .inr i => oracle (t₂ i) q)

end ToOracle

/-! ## `ToOracle` Instances -/
section Polynomial

open Polynomial MvPolynomial

variable {R : Type} [CommSemiring R] {d : ℕ} {σ : Type}

/-- Univariate polynomials can be accessed via evaluation queries. -/
@[reducible, inline]
instance instToOraclePolynomial : ToOracle R[X] where
  Query := R
  Response := R
  oracle := fun poly point => poly.eval point

/-- Univariate polynomials with degree at most `d` can be accessed via evaluation queries. -/
@[reducible, inline]
instance instToOraclePolynomialDegreeLE : ToOracle (R⦃≤ d⦄[X]) where
  Query := R
  Response := R
  oracle := fun ⟨poly, _⟩ point => poly.eval point

/-- Univariate polynomials with degree less than `d` can be accessed via evaluation queries. -/
@[reducible, inline]
instance instToOraclePolynomialDegreeLT : ToOracle (R⦃< d⦄[X]) where
  Query := R
  Response := R
  oracle := fun ⟨poly, _⟩ point => poly.eval point

/-- Multivariate polynomials can be accessed via evaluation queries. -/
@[reducible, inline]
instance instToOracleMvPolynomial : ToOracle (R[X σ]) where
  Query := σ → R
  Response := R
  oracle := fun poly point => eval point poly

/-- Multivariate polynomials with individual degree at most `d` can be accessed via evaluation
queries. -/
@[reducible, inline]
instance instToOracleMvPolynomialDegreeLE : ToOracle (R⦃≤ d⦄[X σ]) where
  Query := σ → R
  Response := R
  oracle := fun ⟨poly, _⟩ point => eval point poly

end Polynomial

section Vector

variable {n : ℕ} {α : Type}

/-- Vectors of the form `Fin n → α` can be accessed via queries on their indices. -/
instance instToOracleForallFin : ToOracle (Fin n → α) where
  Query := Fin n
  Response := α
  oracle := fun vec i => vec i

/-- Vectors of the form `List.Vector α n` can be accessed via queries on their indices. -/
instance instToOracleListVector : ToOracle (List.Vector α n) where
  Query := Fin n
  Response := α
  oracle := fun vec i => vec[i]

/-- Vectors of the form `Vector α n` can be accessed via queries on their indices. -/
instance instToOracleVector : ToOracle (Vector α n) where
  Query := Fin n
  Response := α
  oracle := fun vec i => vec[i]

end Vector

section Test

variable {ι : Type} {spec : OracleSpec ι} {R : Type} [CommSemiring R]

open Polynomial ToOracle SimOracle OracleSpec in
theorem poly_query_list_mapM {m : ℕ} (D : Fin m ↪ R) (p : R[X]) :
    simulateQ (simOracle spec (fun _ : Unit => p))
      (List.finRange m |>.mapM (fun i => query (spec := [fun _ : Unit => R[X]]ₒ) () (D i)))
    = (pure (List.finRange m |>.map (fun i => p.eval (D i))) : OracleComp spec (List R)) := by
  simp [simOracle, OracleSpec.SubSpec.liftM_query_eq_liftM_liftM, StateT.run'_eq,
    simulateQ, StateT.run]
  sorry

end Test
