/-
Copyright (c) 2024 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import Mathlib.FieldTheory.Tower
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.RingTheory.Adjoin.Basic
import Mathlib.Algebra.Group.Units.Defs
import Mathlib.Algebra.Field.Defs
import Mathlib.RingTheory.Ideal.Span
import Mathlib.Order.WithBot
import Mathlib.Algebra.Order.Monoid.Unbundled.Defs
import Mathlib.Data.ZMod.Basic

/-!
# Binary Tower Fields

Define the binary tower field GF(2^{2^k}) as an iterated quadratic extension of GF(2).

## Main Definitions

- `BinaryTower k` : the binary tower field GF(2^{2^k}) as an iterated quadratic extension of GF(2).

- `ConcreteBinaryTower k` : the concrete implementation of `BinaryTower k` using `BitVec`.

## TODOs

- Define additive NTT basis

## References

- [Wie88] Doug Wiedemann. “An Iterated Quadratic Extension of GF(2)”. In: The Fibonacci Quarterly
  26.4 (1988), pp. 290–295.

- [FP97] John L. Fan and Christof Paar. “On efficient inversion in tower fields of characteristic
  two”. In: Proceedings of IEEE International Symposium on Information Theory. 1997.

- [LCH14] Sian-Jheng Lin, Wei-Ho Chung, and Yunghsiang S. Han. “Novel Polynomial Basis and Its
  Application to Reed–Solomon Erasure Codes”. In: IEEE 55th Annual Symposium on Foundations of
  Computer Science. 2014, pp. 316–325. doi: 10.1109/FOCS.2014.41.

- [DP23] Diamond, Benjamin E., and Jim Posen. "Succinct arguments over towers of binary fields."
  Cryptology ePrint Archive (2023).

- [DP24] Diamond, Benjamin E., and Jim Posen. "Polylogarithmic Proofs for Multilinears over Binary
  Towers." Cryptology ePrint Archive (2024).

-/

noncomputable section

open Polynomial
open AdjoinRoot

notation:10 "GF(" term:10 ")" => GaloisField term 1

theorem non_zero_divisors_iff (M₀ : Type*) [Mul M₀] [Zero M₀] :
    NoZeroDivisors M₀ ↔ ∀ {a b : M₀}, a * b = 0 → a = 0 ∨ b = 0 :=
  ⟨fun h => h.1, fun h => ⟨h⟩⟩

instance neZero_one_of_nontrivial_comm_monoid_zero {M₀ : Type*}
  [CommMonoidWithZero M₀] [Nontrivial M₀] : NeZero (1 : M₀) :=
{
  out := by
    -- Get witness of nontriviality
    obtain ⟨x, y, h_neq⟩ := ‹Nontrivial M₀›
    by_contra h_eq -- Assume ¬NeZero 1, i.e., 1 = 0

    -- Show that everything collapses
    have all_eq : ∀ a b : M₀, a = b := by
      intro a b
      calc
        a = a * 1 := by simp only [mul_one]
        _ = a * 0 := by simp only [h_eq]
        _ = 0 := by rw [mul_zero]
        _ = b * 0 := by simp only [mul_zero]
        _ = b * 1 := by rw [h_eq]
        _ = b := by simp only [mul_one]

    -- This contradicts nontriviality
    exact h_neq (all_eq x y)
}

instance unit_of_nontrivial_comm_monoid_with_zero_is_not_zero
    {R : Type*} [CommMonoidWithZero R] [Nontrivial R] {a : R}
    (h_unit : IsUnit a) : NeZero a := by
  by_contra h_zero
  -- Convert ¬NeZero a to a = 0
  simp [neZero_iff] at h_zero
  -- From IsUnit a, get unit u where ↑u = a
  obtain ⟨u, h_unit_eq⟩ := h_unit
  have u_mul_inv := u.val_inv
  rw [h_unit_eq] at u_mul_inv
  rw [h_zero] at u_mul_inv
  -- Now we have 0 * u.inv = 1
  have zero_mul_inv_eq_0 : (0: R) * u.inv = (0: R) :=
    zero_mul (self := inferInstance) (a := (u.inv: R))
  have zero_mul_inv_eq_1 : (0: R) * u.inv = (1: R) := u_mul_inv
  rw [zero_mul_inv_eq_0] at zero_mul_inv_eq_1

  have one_ne_zero: NeZero (1: R) := by exact neZero_one_of_nontrivial_comm_monoid_zero
  simp [one_ne_zero] at zero_mul_inv_eq_1

/-- Any element in `GF(2)` is either `0` or `1`. -/
theorem GF_2_value_eq_zero_or_one (x : GF(2)) : x = 0 ∨ x = 1 := by
  -- Step 1: Use the isomorphism between `GF(2)` and `ZMod 2`
  let φ := GaloisField.equivZmodP 2

  -- Step 2: Enumerate the elements of `ZMod 2` explicitly
  have hZMod : ∀ y : ZMod 2, y = 0 ∨ y = 1 := by
    intro y
    fin_cases y
    · left; rfl -- choose the left side of the OR (∨) and prove it with rfl (reflexivity)
    · right; rfl -- choose the right side of the OR (∨) and prove it with rfl (reflexivity)

  -- Step 3: Transfer this property to `GF(2)` via the isomorphism
  have h := hZMod (φ x)
  cases' h with h_x_is_0 h_x_is_1
  · left
    exact (φ.map_eq_zero_iff).mp h_x_is_0 -- Since `φ` is an isomorphism, `φ x = 0` implies `x = 0`
  · right
    exact (φ.map_eq_one_iff).mp h_x_is_1 -- Similarly, `φ x = 1` implies `x = 1`

theorem GF_2_one_add_one_eq_zero : (1 + 1 : GF(2)) = 0 := by
  -- equivalence of algebras: ≃ₐ, includes A ≃ B, A ≃* B, A ≃+ B, A ≃+* B
  let φ: GF(2) ≃ₐ[ZMod 2] ZMod 2 := GaloisField.equivZmodP 2

  -- convert to algebra homomorphism (A₁ →ₐ[R] A₂) then to ring homomorphism (A →+* B)
  let ringHomMap := φ.toAlgHom.toRingHom

  -- Simps.apply: turn an equivalence of algebras into a mapping
  -- (Mathlib/Algebra/Algebra/Equiv.lean#L336)
  have h_ring_hom_sum : φ (1 + 1 : GF(2)) = φ 1 + φ 1 := by
    exact RingHom.map_add ringHomMap 1 1 -- requires f : α →+* β

  have h_one : φ 1 = 1 := by
    exact φ.map_one
  have h_zero : φ 0 = 0 := by
    exact φ.map_zero
  have h_1_add_1_ring_hom : φ (1 + 1 : GF(2)) = 1 + 1 := by
    rw [h_ring_hom_sum, h_one]
  have one_add_one_eq_zero_in_zmod2 : (1 + 1 : ZMod 2) = 0 := by
    have zmod_2_eq_nat: (1 + 1: ZMod 2) = (2: ℕ) := by rfl
    rw [zmod_2_eq_nat]
    exact ZMod.natCast_self 2
  have h_1_add_1_eq_zero_in_GF_2 : (1 + 1: GF(2)) = 0 := by
    -- Use injectivity of φ to transfer the result back to GF(2)
    apply φ.injective
    calc φ (1 + 1 : GF(2))
      _ = 1 + 1 := h_1_add_1_ring_hom
      _ = 0 := one_add_one_eq_zero_in_zmod2
      _ = φ 0 := by rw [←h_zero]

  exact h_1_add_1_eq_zero_in_GF_2

theorem withBot_lt_one_cases (x : WithBot ℕ) (h : x < (1: ℕ)) : x = ⊥ ∨ x = (0: ℕ) := by
  match x with
  | ⊥ =>
    left -- focus on the left constructof of the goal (in an OR statement)
    rfl
  | some n =>
    have h_n_lt_1 : n < 1 := WithBot.coe_lt_coe.mp h
    have h_n_zero : n = 0 := Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ h_n_lt_1)
    right -- focus on the right constructof the goal (in an OR statement)
    rw [h_n_zero]
    rfl

-- Field R
theorem is_unit_iff_deg_0 {R : Type*} [Field R] {p : R[X]} : p.degree = 0 ↔ IsUnit p := by
  constructor
  · -- (→) If degree = 0, then p is a unit
    intro h_deg_zero
    let a := coeff p 0
    have p_is_C: p = C a := eq_C_of_degree_eq_zero h_deg_zero
    -- Show a ≠ 0 (since degree = 0 ≠ ⊥)
    have h_a_ne_zero : a ≠ 0 := by
      by_contra h_a_zero
      rw [h_a_zero, C_0] at p_is_C
      have h_deg_bot : p.degree = ⊥ := by rw [p_is_C, degree_zero]
      rw [h_deg_bot] at h_deg_zero -- ⊥ = 0
      contradiction
    -- requires non-zero multiplicative inverse (DivisionRing)
    let a_mul_inv_eq_1 := DivisionRing.mul_inv_cancel a h_a_ne_zero
    let inv_mul_a_eq_1: a⁻¹ * a = 1 := by -- requires commutativity (CommRing)
      rw [mul_comm] at a_mul_inv_eq_1  -- a⁻¹ * a = a * a⁻¹
      exact a_mul_inv_eq_1
    -- contruct instance of isUnit
    have a_is_unit: IsUnit a := by
      -- isUnit_iff_exists: IsUnit x ↔ ∃ b, x * b = 1 ∧ b * x = 1
      apply isUnit_iff_exists.mpr -- modus ponens right
      use a⁻¹
    rw [p_is_C]  -- p = C a
    exact isUnit_C.mpr a_is_unit
  · -- (←) If p is a unit, then degree = 0
    intro h_unit
    exact degree_eq_zero_of_isUnit h_unit

-- degree of a, b where a * b = p, p ≠ 0, and p, a, b are not units is at least 1
theorem non_trivial_factors_of_non_trivial_poly_have_deg_ge_1 {R : Type*} [Field R]
    {p a b : R[X]}
    (h_prod : p = a * b)
    (h_p_nonzero : p ≠ 0)
    (h_a_non_unit : ¬IsUnit a)
    (h_b_non_unit : ¬IsUnit b) :
    1 ≤ a.degree ∧ 1 ≤ b.degree := by
  by_contra h_deg_a_not_nat
  have h_deg_a_ge_1_or_deg_b_ge_1 := not_and_or.mp h_deg_a_not_nat -- ¬1 ≤ a.degree ∨ ¬1 ≤ b.degree
  cases h_deg_a_ge_1_or_deg_b_ge_1 with
  | inl h_deg_a_lt_1 =>
    push_neg at h_deg_a_lt_1
    have a_deg_cases := withBot_lt_one_cases a.degree h_deg_a_lt_1
    cases a_deg_cases with
    | inl h_a_deg_bot =>
      have h_a_eq_zero := degree_eq_bot.mp h_a_deg_bot
      rw [h_a_eq_zero] at h_prod
      exact h_p_nonzero (by rw [h_prod, zero_mul]) -- contradiction: p ≠ 0 vs p = 0
    | inr h_a_deg_zero =>
      exact h_a_non_unit (is_unit_iff_deg_0.mp h_a_deg_zero)
  | inr h_deg_b_lt_1 =>
    push_neg at h_deg_b_lt_1 -- b.degree < 1
    have b_deg_cases := withBot_lt_one_cases b.degree h_deg_b_lt_1
    cases b_deg_cases with
    | inl h_b_deg_bot =>
      have h_b_eq_zero := degree_eq_bot.mp h_b_deg_bot
      rw [h_b_eq_zero] at h_prod
      exact h_p_nonzero (by rw [h_prod, mul_zero]) -- contradiction: p ≠ 0 vs p = 0
    | inr h_b_deg_zero =>
      exact h_b_non_unit (is_unit_iff_deg_0.mp h_b_deg_zero)

structure PolyInstanceResult (F : Type _) [Field F] (specialElement : F) where
  poly : Polynomial F
  monic : Monic poly
  not_unit : ¬IsUnit poly
  deg_poly_is_2: poly.degree = 2
  nat_deg_poly_is_2 : poly.natDegree = 2
  coeffOfX_0 : poly.coeff 0 = 1
  coeffOfX_1 : poly.coeff 1 = specialElement

def PolyInstances (F : Type _) [Field F] (specialElement : F) :
    PolyInstanceResult F specialElement :=

  let t1 := C specialElement
  have deg_t1_le_0 : t1.degree ≤ 0 := by exact degree_C_le
  let newPoly : F[X] := X^2 + (t1 * X + 1)

  have deg_X2 : (X^2 : F[X]).degree = 2 := by simp [degree_X_pow]
  have deg_1_le_0 : (1 : F[X]).degree ≤ 0 := by simp [degree_one]
  have deg_q_lt_2 : (t1 * X + 1).degree < 2 :=
    have deg_left_le_1 : (t1 * X).degree ≤ 1 := by
      simp [degree_C_mul_X_le] -- Goal: t1.degree + 1 ≤ 1
      calc
        t1.degree + 1 ≤ 0 + 1 := add_le_add_right deg_t1_le_0 1
        _ = 1 := by norm_num

    have deg_right : (1 : F[X]).degree = 0 := degree_one
      -- Apply `degree_add_le`
    calc
      (t1 * X + 1).degree ≤ max (t1 * X).degree (1 : F[X]).degree := degree_add_le _ _
      _ ≤ max (t1 * X).degree 0 := by simp [deg_left_le_1, deg_right]
      _ ≤ 1 := by
        apply max_le
        · exact deg_left_le_1
        · norm_num  -- Since 0 ≤ 1
      _ < 2 := by norm_num

  have deg_right_lt_deg_left : (t1 * X + 1).degree < (X^2 : F[X]).degree := by
    simp [deg_X2, deg_q_lt_2]

  have deg_poly_is_2 : newPoly.degree = 2 := by
    simp [newPoly]  -- Expand `newPoly` as `X^2 + (t1 * X + 1)`
    have deg_sum_reduced := degree_add_eq_left_of_degree_lt deg_right_lt_deg_left
    rw [deg_sum_reduced]
    exact deg_X2

  have nat_deg_poly_is_2 : newPoly.natDegree = 2 := by
    rw [natDegree_eq_of_degree_eq_some deg_poly_is_2]

  have poly_is_not_zero : newPoly ≠ 0 := by
    by_contra newPoly_is_zero
    have deg_bot := degree_eq_bot.mpr newPoly_is_zero -- degree newPoly = ⊥
    rw [deg_bot] at deg_poly_is_2 -- ⊥ = 2
    contradiction

  let instNoZeroDiv : NoZeroDivisors (F) := inferInstance
  let instNontrivial : Nontrivial (F) := inferInstance
  let polyRingIsMulZero: MulZeroClass (F[X]) := inferInstance
  let polyRingIsCommGroupWithZero : CommMonoidWithZero (F[X]) := inferInstance
  let polyRingIsNontrivial : Nontrivial (F[X]) := inferInstance
  let instNotUnitPoly : ¬IsUnit newPoly := by
    by_contra h_unit
    have deg_poly_is_0 := degree_eq_zero_of_isUnit h_unit

    have zero_is_two : (0: WithBot ℕ) = 2 := by
      rw [deg_poly_is_0] at deg_poly_is_2
      exact deg_poly_is_2

    contradiction

  have newPolyIsMonic: Monic newPoly := by
    -- Goal: ⊢ (X ^ 2 + (t1 * X + 1)).Monic
    have leadingCoeffIs1 : newPoly.leadingCoeff = 1 := by
      calc
        newPoly.leadingCoeff = (t1 * X + 1 + X^2).leadingCoeff := by
          rw [add_comm (t1 * X + 1) (X^2)]
        _ = (X^2).leadingCoeff := by rw [leadingCoeff_add_of_degree_lt deg_right_lt_deg_left]
        _ = 1 := by rw [monic_X_pow]
    exact leadingCoeffIs1

  have coeffOfX_0 : newPoly.coeff 0 = 1 := by
    simp [newPoly]

  have coeffOfX_1 : newPoly.coeff 1 = specialElement := by
    calc newPoly.coeff 1 = (X^2 + (t1 * X + 1)).coeff 1 := by simp [newPoly]
      _ = (X^2).coeff 1 + (t1 * X).coeff 1 + (1: F[X]).coeff 1 := by
        rw [coeff_add, add_assoc, coeff_add]
      _ = (X^2).coeff 1 + (t1 * X).coeff 1 + 0 := by
        have coeff_1_of_1: (1: F[X]).coeff 1 = 0 := by
          have deg_1_lt_1 : (1: F[X]).degree < 1 := by
            rw [degree_one]
            norm_num
          exact coeff_eq_zero_of_degree_lt deg_1_lt_1 -- coeff 1 One.one = 0
        rw [coeff_1_of_1]
      _ = (t1 * X^1).coeff 1 := by
        rw [coeff_X_pow (k := 2) (n := 1)]
        norm_num
      _ = specialElement := by -- ⊢ (t1 * X).coeff 1 = specialElement
        unfold t1
        have h_coeff_eq := coeff_C_mul_X_pow (x := specialElement) (k := 1) (n := 1)
        -- h_coeff_eq : (C specialElement * X ^ 1).coeff 1 = if 1 = 1 then specialElement else 0
        rw [if_pos rfl] at h_coeff_eq -- resolve 1 = 1
        exact h_coeff_eq

  let result : PolyInstanceResult F specialElement := {
    poly := newPoly,
    monic := newPolyIsMonic,
    not_unit := instNotUnitPoly,
    deg_poly_is_2 := deg_poly_is_2,
    nat_deg_poly_is_2 := nat_deg_poly_is_2,
    coeffOfX_0 := coeffOfX_0,
    coeffOfX_1 := coeffOfX_1
  }
  result

structure BinaryTowerResult (F : Type _) (k : ℕ) where
  vec       : (List.Vector F (k + 1))
  instMul   : (Mul F)
  instZero  : (Zero F)
  instField : (Field F)
  instNontrivial:(Nontrivial F)
  newPoly   : (Polynomial F)
  instInh   : (Inhabited F)
  instDomain: (IsDomain F)
  isNotUnitPoly: (¬IsUnit newPoly)
  instNoZeroDiv : (NoZeroDivisors F)
  instIrreduciblePoly : (Irreducible (p := (newPoly : Polynomial F)))

def BinaryTower (k : ℕ) : Σ' (F : Type _), BinaryTowerResult F k :=
  match k with
  | 0 =>
    let curBTField := GF(2)
    let newList : List.Vector (GF(2)) 1 := List.Vector.cons (1 : GF(2)) List.Vector.nil
    let specialElement : GF(2) := newList.1.headI
    let polyInstances := PolyInstances curBTField specialElement
    let newPoly := polyInstances.poly
    let newPolyIsMonic := polyInstances.monic
    let instNotUnitPoly := polyInstances.not_unit

    let instNoZeroDiv : NoZeroDivisors (GF(2)) := inferInstance
    let instNontrivial : Nontrivial (GF(2)) := inferInstance
    let polyRingIsMulZero: MulZeroClass (Polynomial (GF(2))) := inferInstance
    let polyRingIsCommGroupWithZero : CommMonoidWithZero (Polynomial (GF(2))) := inferInstance
    let polyRingIsNontrivial : Nontrivial (Polynomial (GF(2))) := inferInstance

    let instIrreduciblePoly : Irreducible newPoly := by
      by_contra h_not_irreducible
      -- ¬Irreducible p ↔ ∃ c₁ c₂, p.coeff 0 = c₁ * c₂ ∧ p.coeff 1 = c₁ + c₂
      obtain ⟨c₁, c₂, h_mul, h_add⟩ :=
        (Monic.not_irreducible_iff_exists_add_mul_eq_coeff
          newPolyIsMonic polyInstances.nat_deg_poly_is_2).mp h_not_irreducible
      rw [polyInstances.coeffOfX_0] at h_mul -- 1 = c₁ * c₂
      rw [polyInstances.coeffOfX_1] at h_add -- specialElement = c₁ + c₂
      -- since c₁, c₂ ∈ GF(2), c₁ * c₂ = 1 => c₁ = c₂ = 1
      have c1_c2_eq_one : c₁ = 1 ∧ c₂ = 1 := by
        -- In GF(2), elements are only 0 or 1
        have c1_cases : c₁ = 0 ∨ c₁ = 1 := by exact GF_2_value_eq_zero_or_one c₁
        have c2_cases : c₂ = 0 ∨ c₂ = 1 := by exact GF_2_value_eq_zero_or_one c₂

        -- Case analysis on c₁ and c₂
        rcases c1_cases with c1_zero | c1_one
        · -- If c₁ = 0
          rw [c1_zero] at h_mul
          -- Then 0 * c₂ = 1, contradiction
          simp at h_mul
        · -- If c₁ = 1
          rcases c2_cases with c2_zero | c2_one
          · -- If c₂ = 0
            rw [c2_zero] at h_mul
            -- Then 1 * 0 = 1, contradiction
            simp at h_mul
          · -- If c₂ = 1
            -- Then we have our result
            exact ⟨c1_one, c2_one⟩

      -- Now we can show specialElement = 0
      have specialElement_eq_zero : specialElement = 0 := by
        rw [h_add]  -- Use c₁ + c₂ = specialElement
        rw [c1_c2_eq_one.1, c1_c2_eq_one.2]  -- Replace c₁ and c₂ with 1
        -- In GF(2), 1 + 1 = 0
        apply GF_2_one_add_one_eq_zero

      -- But we know specialElement = 1
      have specialElement_eq_one : specialElement = 1 := by
        unfold specialElement
        simp [newList]

      rw [specialElement_eq_zero] at specialElement_eq_one
      -- (0: GF(2)) = (1: GF(2))

      have one_ne_zero_in_gf2 : (1: GF(2)) ≠ (0: GF(2)) := by
        exact NeZero.out
      contradiction

    let result: BinaryTowerResult curBTField 0 :={
      vec := newList,
      instMul := inferInstance,
      instZero := inferInstance,
      instField := inferInstance,
      instNontrivial := instNontrivial,
      newPoly := newPoly,
      instInh := inferInstance,
      instDomain := inferInstance,
      isNotUnitPoly := instNotUnitPoly,
      instNoZeroDiv := instNoZeroDiv,
      instIrreduciblePoly := instIrreduciblePoly
    }

    ⟨ curBTField, result ⟩
  | k + 1 =>
    let ⟨ prevBTField, elts, _, _, _, _, prevPoly, _, _, _, _, instPrevPolyIrreducible ⟩
      := BinaryTower k

    let instFactIrrPoly : Fact (Irreducible prevPoly) := ⟨instPrevPolyIrreducible⟩
    let curBTField := AdjoinRoot prevPoly
    let instFieldAdjoinRootOfPoly : Field curBTField := by
      exact AdjoinRoot.instField (f := prevPoly)

    let adjoinRootOfPoly : AdjoinRoot prevPoly = curBTField := by
      simp [curBTField]

    -- Lift to new BTField level
    let specialElement := AdjoinRoot.root prevPoly
    let polyInstances := PolyInstances curBTField specialElement
    let newPoly := polyInstances.poly
    let newPolyIsMonic := polyInstances.monic
    let instNotUnitPoly: ¬IsUnit newPoly := polyInstances.not_unit
    let instNoZeroDiv : NoZeroDivisors curBTField := inferInstance
    let newElts := elts.map (fun x => (AdjoinRoot.of prevPoly).toFun x)
    let polyRingIsMulZero: MulZeroClass (Polynomial prevBTField) := inferInstance
    let instFieldcurBTField : Field curBTField := by exact AdjoinRoot.instField (f := prevPoly)
    let instMul: Mul curBTField := inferInstance
    let instZero: Zero curBTField := inferInstance
    let instMulZeroClass : MulZeroClass curBTField := inferInstance
    let instInh: Inhabited curBTField := inferInstance
    let instDomain: IsDomain curBTField := inferInstance
    -- TODO: prove irreducibility for newPoly
    let instIrreduciblePoly: Irreducible (p := (newPoly: Polynomial curBTField)) := sorry

    let result: BinaryTowerResult curBTField (k + 1) := {
      vec := specialElement ::ᵥ newElts,
      instMul := instMul,
      instZero := instZero,
      instField := instFieldAdjoinRootOfPoly,
      instNontrivial := inferInstance,
      newPoly := newPoly,
      instInh := instInh,
      instDomain := instDomain,
      isNotUnitPoly := instNotUnitPoly,
      instNoZeroDiv := instNoZeroDiv,
      instIrreduciblePoly := instIrreduciblePoly
    }

    ⟨ curBTField, result ⟩

namespace BinaryTower

@[simp]
def BTField (k : ℕ) := (BinaryTower k).1

@[simp]
instance BTFieldIsField (k : ℕ) : Field (BTField k) := (BinaryTower k).2.instField

@[simp]
instance CommRing (k : ℕ) : CommRing (BTField k) := Field.toCommRing

@[simp]
instance Inhabited (k : ℕ) : Inhabited (BTField k) := (BinaryTower k).2.instInh

@[simp]
def list (k : ℕ) : List.Vector (BTField k) (k + 1) := (BinaryTower k).2.vec

@[simp]
def poly (k : ℕ) : Polynomial (BTField k) := (BinaryTower k).2.newPoly

@[coe]
theorem field_eq_adjoinRoot_poly (k : ℕ) (k_pos : k > 0) : AdjoinRoot (poly (k - 1)) = BTField k := by
  induction k with
  | zero => absurd k_pos ; simp
  | succ k _ => sorry

instance coe_field_adjoinRoot (k : ℕ) (k_pos : k > 0) : Coe (AdjoinRoot (poly (k - 1))) (BTField k) where
  coe := Eq.mp (field_eq_adjoinRoot_poly k k_pos)

-- -- We call the special extension field elements Z_k
@[simp]
def Z (k : ℕ) : BTField k := (list k).1.headI

-- @[simp]
-- theorem Z_eq_adjointRoot_root (k : ℕ) (k_pos : k > 0) [HEq (AdjoinRoot (poly k)) (BTField k)] :
--     Z k = AdjoinRoot.root (poly k) := by
--   simp [Z, field_eq_adjoinRoot_poly k k_pos]

-- @[simp]
-- theorem list_nonempty (k : ℕ) : (BinaryTower k).2.1 ≠ [] :=
--   List.ne_nil_of_length_eq_add_one (list_length k)

instance polyIrreducible (n : ℕ) : Irreducible (poly n) := (BinaryTower n).2.instIrreduciblePoly

instance polyIrreducibleFact (n : ℕ) : Fact (Irreducible (poly n)) := ⟨polyIrreducible n⟩

-- Possible direction: define alternate definition of BTF as Quotient of MvPolynomial (Fin n) GF(2)
-- by the ideal generated by special field elements
-- What would this definition give us?

end BinaryTower

end

/- Concrete implementation of BTF uses BitVec -/

def ConcreteBinaryTower (k : ℕ) :=
  match k with
  | 0 => BitVec 1
  | k + 1 => BitVec (2 ^ (2 ^ (k - 1)))


-- Define all arithmetic operations



-- Define a field isomorphism
