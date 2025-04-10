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

-- Define Fintype instance for GaloisField 2 1 explicitly
instance GF_2_fintype: Fintype (GF(2)) := Fintype.ofFinite (GF(2))

-- Theorem 1: x ^ |F| = x using FiniteField.pow_card
theorem GF_2_pow_card (x : GF(2)) : x ^ Fintype.card (GF(2)) = x := by
  rw [FiniteField.pow_card]  -- Requires Fintype and Field instances, already provided

-- Theorem 2: |GF(2)| = 2
theorem GF_2_card : Fintype.card (GF(2)) = 2^(2^0) := by
  let φ : GF(2) ≃ₐ[ZMod 2] ZMod 2 := GaloisField.equivZmodP 2
  -- Apply card_congr to the underlying Equiv
  have h := Fintype.card_congr φ.toEquiv
  -- ZMod 2 has 2 elements
  rw [ZMod.card 2] at h
  exact h

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
  let φ: GF(2) ≃ₐ[ZMod 2] ZMod 2 := GaloisField.equivZmodP 2

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
    exact map_one φ
  have h_zero : φ 0 = 0 := by
    exact map_zero φ
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

@[to_additive]
lemma prod_univ_twos {M : Type*} [CommMonoid M] {n : ℕ} (hn : n = 2) (f : Fin n → M) :
    (∏ i, f i) = f (Fin.cast hn.symm 0) * f (Fin.cast hn.symm 1) := by
  simp [← Fin.prod_congr' f hn.symm]

-- if linear combination of two representations with the same PowerBasis are equal
-- then the representations are exactly the same
theorem unique_repr {R : Type*} [CommRing R] {S : Type*} [CommRing S] [Algebra R S]
    (pb : PowerBasis R S) (repr1 repr2 : Fin pb.dim →₀ R)
    (h : ∑ i : Fin pb.dim, repr1 i • pb.basis i = ∑ i : Fin pb.dim, repr2 i • pb.basis i) :
    repr1 = repr2 := by
  -- Use the fact that PowerBasis.basis is a basis
  -- Aproach: maybe we should utilize the uniqueness of (pb.basis.repr s)
  set val := ∑ i : Fin pb.dim, repr1 i • pb.basis i
  -- theorem repr_linearCombination (v) : b.repr (Finsupp.linearCombination _ b v) = v := by
  have rerp_eq_rerp1: pb.basis.repr (Finsupp.linearCombination _ pb.basis repr1) = repr1 := by
    apply pb.basis.repr_linearCombination
  have rerpr_eq_rerp2: pb.basis.repr (Finsupp.linearCombination _ pb.basis repr2) = repr2 := by
    apply pb.basis.repr_linearCombination

  have val_eq_linearComb_of_repr1: val = (Finsupp.linearCombination _ pb.basis repr1) := by
    rw [Finsupp.linearCombination_apply (v := pb.basis) (l := repr1)]
    -- ⊢ val = repr1.sum fun i a ↦ a • pb.basis i
    rw [Finsupp.sum_fintype (f := repr1)] -- ⊢ ∀ (i : Fin pb.dim), 0 • pb.basis i = 0
    intros i; exact zero_smul R (pb.basis i)

  have val_eq_linearComb_of_repr2: val = (Finsupp.linearCombination _ pb.basis repr2) := by
    have val_eq: val = ∑ i : Fin pb.dim, repr2 i • pb.basis i := by
      unfold val
      exact h
    rw [Finsupp.linearCombination_apply (v := pb.basis) (l := repr2)]
    -- ⊢ val = repr2.sum fun i a ↦ a • pb.basis i
    rw [Finsupp.sum_fintype]
    exact val_eq
    intros i; exact zero_smul R (pb.basis i)

  rw [←val_eq_linearComb_of_repr1] at rerp_eq_rerp1
  rw [←val_eq_linearComb_of_repr2] at rerpr_eq_rerp2
  rw [rerp_eq_rerp1] at rerpr_eq_rerp2
  exact rerpr_eq_rerp2

theorem linear_sum_repr(R : Type*) [CommRing R] (S : Type*) [CommRing S] [Algebra R S]
    (pb : PowerBasis R S) (h_dim : pb.dim = (2: ℕ)) (s : S) :
    ∃ a b : R, s = a • pb.gen + algebraMap R S b := by
  let tmp: Basis (Fin pb.dim) R S := pb.basis
  let repr : (Fin pb.dim) →₀ R := pb.basis.repr s
  have s_repr : s = ∑ i : Fin pb.dim, repr i • pb.basis i := (pb.basis.sum_repr s).symm

  -- Step 1: introduce shorthands for indices and coefficients of the basis
  set i0 := Fin.cast h_dim.symm 0 with i0_def
  set i1 := Fin.cast h_dim.symm 1 with i1_def
  set a := repr i1 with a_def
  set b := repr i0 with b_def

  -- Step 2: state that a and b satisfy the existential quantifier
  use a, b
  rw [s_repr]
  let f: Fin pb.dim → S := fun i => repr i • pb.basis i

  -- Step 3: convert to size-2 linear-sum form
  have sum_repr_eq: ∑ i : Fin pb.dim, repr i • pb.basis i = f i0 + f i1 := by
    exact sum_univ_twos (hn := h_dim) (f := f)
  rw [sum_repr_eq]
  -- ⊢ f i0 + f i1 = a • pb.gen + (algebraMap R S) b

  -- Step 4: prove equality for each operand
  have left_operand: f i1 = a • pb.gen := by
    unfold f
    have oright: pb.basis i1 = pb.gen := by
      rw [pb.basis_eq_pow]
      rw [i1_def] -- ⊢ pb.gen ^ ↑(Fin.cast ⋯ 1) = pb.gen
      norm_num
    rw [a_def, oright]
  rw [left_operand]
  have right_operand : f i0 = algebraMap R S b := by
    unfold f
    have oright : pb.basis i0 = 1 := by
      rw [pb.basis_eq_pow]
      rw [i0_def] -- ⊢ pb.gen ^ ↑(Fin.cast ⋯ 0) = 1
      norm_num
    rw [b_def, oright]
    have b_mul_one: b • 1 = ((algebraMap R S) b) * 1 := Algebra.smul_def (r := b) (x := (1: S))
    rw [b_mul_one] -- ⊢ (algebraMap R S) b * 1 = (algebraMap R S) b
    rw [mul_one]
  rw [right_operand]
  -- ⊢ (algebraMap R S) b + a • pb.gen = a • pb.gen + (algebraMap R S) b
  exact add_comm (algebraMap R S b) (a • pb.gen)

theorem unique_linear_sum_repr (R : Type*) [CommRing R] (S : Type*) [CommRing S] [Algebra R S]
    (pb : PowerBasis R S) (h_dim : pb.dim = 2) (s : S) :
    ∃! p : R × R, s = p.fst • pb.gen + algebraMap R S p.snd := by
  -- Get the coordinate representation of s in terms of the basis
  let repr := pb.basis.repr s
  have s_repr : s = ∑ i : Fin pb.dim, repr i • pb.basis i := (pb.basis.sum_repr s).symm

  -- Define indices and coefficients using the dimension assumption
  have h_dim' : Fintype.card (Fin pb.dim) = 2 := by rw [h_dim]; simp
  set i0 := Fin.cast h_dim.symm 0 with i0_def
  set i1 := Fin.cast h_dim.symm 1 with i1_def
  have i1_ne_i0 : i1 ≠ i0 := by
    rw [i1_def, i0_def]
    norm_num
  set a := repr i1 with a_def
  set b := repr i0 with b_def
  have basis_i1_eq_gen : pb.basis i1 = pb.gen := by
    rw [pb.basis_eq_pow, i1_def]
    simp
  have basis_i0_eq_one : pb.basis i0 = 1 := by
    rw [pb.basis_eq_pow, i0_def]
    simp

  use ⟨a, b⟩

  constructor
  · -- ⊢ (fun p ↦ s = p.1 • pb.gen + (algebraMap R S) p.2) (a, b), p ∈ R × R
    let p: R × R := (a, b)
    have s_eq_linear_comb_of_a_b: s = a • pb.gen + algebraMap R S b := by
      rw [sum_univ_twos (hn := h_dim) (f := fun i => repr i • pb.basis i)] at s_repr
      rw [basis_i0_eq_one, basis_i1_eq_gen, Algebra.smul_def, mul_one] at s_repr
      rw [←a_def, ←b_def] at s_repr
      rw [add_comm] at s_repr
      exact s_repr
    rw [s_eq_linear_comb_of_a_b]
  · intro y hy -- hy : s = y.1 • pb.gen + (algebraMap R S) y.2
    rw [←basis_i1_eq_gen, Algebra.smul_def] at hy
    rw [←mul_one (a := ((algebraMap R S) y.2))] at hy
    rw [←basis_i0_eq_one] at hy
    let repr2: Fin pb.dim →₀ R := Finsupp.single i1 y.1 + Finsupp.single i0 y.2
    have repr2_i0: repr2 i0 = y.2 := by
        unfold repr2
        rw [Finsupp.add_apply]
        rw [Finsupp.single_apply, Finsupp.single_apply]
        rw [if_pos rfl] -- i0 = i0
        rw [if_neg i1_ne_i0]
        rw [zero_add]
    have repr2_i1: repr2 i1 = y.1 := by
      unfold repr2
      rw [Finsupp.add_apply]
      rw [Finsupp.single_apply, Finsupp.single_apply]
      rw [if_pos rfl] -- ⊢ (y.1 + if i0 = i1 then y.2 else 0) = y.1
      rw [if_neg (fun h => i1_ne_i0 h.symm)]
      rw [add_zero]
    have sum_repr_eq: ∑ i : Fin pb.dim, repr2 i • pb.basis i = s := by
      rw [sum_univ_twos (hn := h_dim) (f := fun i => repr2 i • pb.basis i)]
      rw [repr2_i0, repr2_i1]
      rw [hy]
      rw [Algebra.smul_def]
      rw [Algebra.smul_def]
      rw [i0_def, i1_def, add_comm]

    have repr_eq_repr2: repr = repr2 := by
      have eq_linear_comb: ∑ i : Fin pb.dim, repr i • pb.basis i
        = ∑ i : Fin pb.dim, repr2 i • pb.basis i := by
        rw [sum_repr_eq]
        exact s_repr.symm
      exact unique_repr pb repr repr2 eq_linear_comb

    -- => y = (a, b)
    have repr_i0_eq_repr2_i0: repr i0 = repr2 i0 := by
      rw [repr_eq_repr2]
    have repr_i1_eq_repr2_i1: repr i1 = repr2 i1 := by
      rw [repr_eq_repr2]
    have y1_eq_a: y.1 = a := by
      calc
        y.1 = repr2 i1 := by rw [repr2_i1.symm]
        _ = repr i1 := by rw [repr_i1_eq_repr2_i1]
        _ = a := by rw [a_def]
    have y2_eq_b: y.2 = b := by
      calc
        y.2 = repr2 i0 := by rw [repr2_i0.symm]
        _ = repr i0 := by rw [repr_i0_eq_repr2_i0]
        _ = b := by rw [b_def]
    exact Prod.ext y1_eq_a y2_eq_b

theorem linear_form_of_elements_in_adjoined_commring
    {R : Type*} [CommRing R] (f : R[X]) (hf_deg : f.natDegree = 2)
    (hf_monic : Monic f) (c1 : AdjoinRoot f) :
    ∃ a b : R, c1 = (AdjoinRoot.of f) a * root f + (AdjoinRoot.of f) b := by
  let pb: PowerBasis R (AdjoinRoot f) := powerBasis' hf_monic
  have h_dim : pb.dim = 2 := by rw [powerBasis'_dim, hf_deg]
  let repr : Fin pb.dim →₀ R := pb.basis.repr c1
  have c1_repr : c1 = ∑ i : Fin pb.dim, repr i • pb.basis i := (pb.basis.sum_repr c1).symm
  have c1_linear_sum_repr := linear_sum_repr (R := R) (S := AdjoinRoot f) pb h_dim c1
  have gen_eq_root : pb.gen = root f := by rw [powerBasis'_gen]
  rw [gen_eq_root] at c1_linear_sum_repr
  obtain ⟨a, b, c1_linear_comb_over_a_b⟩ := c1_linear_sum_repr
  use a, b
  -- c1_linear_comb_over_a_b : c1 = a • root f + (algebraMap R (AdjoinRoot f)) b
  have oleft: (a: R) • root (f: R[X]) = (AdjoinRoot.of f) a * root f := by
    simp [Algebra.smul_def] -- Definition of algebra scalar multiplication
  have oright: (algebraMap R (AdjoinRoot f)) b = (of f) b := by
    simp [Algebra.smul_def]
  rw [oleft, oright] at c1_linear_comb_over_a_b
  exact c1_linear_comb_over_a_b

theorem unique_linear_form_of_elements_in_adjoined_commring
    {R : Type*} [CommRing R] (f : R[X]) (hf_deg : f.natDegree = 2)
    (hf_monic : Monic f) (c1 : AdjoinRoot f) :
    ∃! p : R × R, c1 = (AdjoinRoot.of f) p.1 * root f + (AdjoinRoot.of f) p.2 := by
  -- Define the PowerBasis
  let pb : PowerBasis R (AdjoinRoot f) := powerBasis' hf_monic
  have h_dim : pb.dim = 2 := by rw [powerBasis'_dim, hf_deg]
  let repr : Fin pb.dim →₀ R := pb.basis.repr c1
  have c1_repr : c1 = ∑ i : Fin pb.dim, repr i • pb.basis i := (pb.basis.sum_repr c1).symm

  -- Apply unique_linear_sum_repr
  have h_unique : ∃! p : R × R, c1 = p.fst • pb.gen + algebraMap R (AdjoinRoot f) p.snd :=
    unique_linear_sum_repr R (AdjoinRoot f) pb h_dim c1

  convert h_unique using 1
  · ext p
    rw [Algebra.smul_def] -- p.fst • pb.gen = (algebraMap R (AdjoinRoot f) p.fst) * pb.gen
    rfl

theorem two_eq_zero_in_char2_field {F : Type*} [Field F] (sumZeroIffEq : ∀ (x y : F), x + y = 0 ↔ x = y): (2 : F) = 0 := by
  have char_two : (1:F) + (1:F) = 0 := by
    exact (sumZeroIffEq 1 1).mpr rfl
  have : (2:F) = (1:F) + (1:F) := by norm_num
  rw [this]
  exact char_two

theorem sum_of_pow_exp_of_2 {F : Type*} [Field F] (sumZeroIffEq : ∀ (x y : F), x + y = 0 ↔ x = y) (i : ℕ) : ∀ (a b c : F) (h_sum_a_b_eq_c: a + b = c), a^(2^i) + b^(2^i) = c^(2^i) := by
  induction i with
  | zero =>
    simp [pow_zero] -- a^1 + b^1 = a + b = c = c^1
  | succ i ih => -- ih : ∀ (a b c : F), a + b = c → a ^ 2 ^ i + b ^ 2 ^ i = c ^ 2 ^ i
    -- Goal: a^(2^(i+1)) + b^(2^(i+1)) = c^(2^(i+1))
    have h : 2 ^ (i + 1) = 2 * 2 ^ i := by
      rw [Nat.pow_succ'] -- 2^(i+1) = 2 * 2^i
    rw [Nat.pow_succ'] -- Rewrite 2^(i+1) in the exponents
    intros a b c h_sum
    rw [pow_mul, pow_mul, pow_mul] -- a^(2 * 2^i) = (a^(2^i))^2, etc.
    set x := a ^ (2 ^ i)
    set y := b ^ (2 ^ i)
    set z := c ^ (2 ^ i)
    have x_plus_y_eq_z : x + y = z := by exact ih a b c h_sum
    -- ⊢ (a ^ 2) ^ 2 ^ i + (b ^ 2) ^ 2 ^ i = (c ^ 2) ^ 2 ^ i
    have goal_eq : ∀ (u: F), (u ^ 2) ^ 2 ^ i = (u ^ (2^i))^2 := by
      intro u
      rw [←pow_mul, ←pow_mul]
      rw [mul_comm]
    rw [goal_eq a, goal_eq b, goal_eq c]
    have expand_square : ∀ (s t : F), (s + t)^2 = s^2 + t^2 := by
      intros s t
      -- Expand (s + t)^2
      rw [pow_two, add_mul, mul_add, ←pow_two, pow_two, pow_two]
      rw [mul_add, ←pow_two, pow_two, ←add_assoc]
      -- Now we have: ⊢ s * s + s * t + t * s + t * t = s * s + t * t
      have cross_term : s * t + t * s = (2 : F) * s * t := by
        rw [mul_comm t s, ←two_mul, ←mul_assoc]
      have s_mul_t_eq: s * t = t * s := by
        rw [mul_comm]
      rw [add_assoc (a := s * s) (b := s * t)]
      -- -- ⊢ s * s + s * t + (t * s + t * t) = s * s + t * t
      rw [cross_term]
      rw [(sumZeroIffEq (s * t) (t * s)).mpr s_mul_t_eq] at cross_term
      rw [←cross_term]
      rw [add_zero]
    -- ⊢ (a ^ 2 ^ i) ^ 2 + (b ^ 2 ^ i) ^ 2 = (c ^ 2 ^ i) ^ 2
    rw [←expand_square x y]
    rw [x_plus_y_eq_z]

theorem sum_square_char2 {F : Type*} [Field F] (sumZeroIffEq : ∀ (x y : F), x + y = 0 ↔ x = y) (s : Finset ℕ) (f : ℕ → F) : (∑ j ∈ s, f j)^2 = ∑ j ∈ s, (f j)^2 := by
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty, zero_pow (by norm_num), Finset.sum_empty]
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    -- Current goal: (f a + ∑ j ∈ s, f j) ^ 2 = f a ^ 2 + ∑ j ∈ s, f j ^ 2
    have expand_square : ∀ (x y : F), (x + y)^2 = x^2 + y^2 := by
      intros x y
      have sum_eq: x + y = (x + y) := by rfl
      have sum_pow_2_pow_1:= sum_of_pow_exp_of_2 (sumZeroIffEq := sumZeroIffEq) (a:=x) (b:=y) (c:=x+y) (i:=1) (sum_eq) -- x^(2^1) + y^(2^1) = (x+y)^(2^1)
      rw [pow_one] at sum_pow_2_pow_1
      exact sum_pow_2_pow_1.symm
    rw [expand_square]
    congr

theorem singleton_subset_Icc (n : ℕ) : {1} ⊆ Finset.Icc 1 (n + 1) := by
  rw [Finset.singleton_subset_iff]
  simp only [Finset.mem_Icc]
  have one_le_n_plus_1 := Nat.le_add_right 1 n
  rw [add_comm] at one_le_n_plus_1
  exact ⟨Nat.le_refl 1, one_le_n_plus_1⟩

theorem two_le_two_pow_n_plus_1 (n : ℕ) : 2 ≤ 2 ^ (n + 1) := by
  calc
    2 = 2 ^ 1               := by rw [Nat.pow_one]
    _ ≤ 2 ^ (n + 1)         := Nat.pow_le_pow_right (by decide) (by exact Nat.zero_lt_succ n)

theorem one_le_two_pow_n (n : ℕ) : 1 ≤ 2 ^ n := by
  calc
    1 = 2^0               := by rw [Nat.pow_zero]
    _ ≤ 2 ^ n         := Nat.pow_le_pow_right (by decide) (by exact Nat.zero_le n)

theorem two_pow_ne_zero (n : ℕ) : 2 ^ n ≠ 0 := by
  by_contra hn
  have h_1_le_0: 1 ≤ 0 := by
    calc 1 ≤ 2^n := by exact one_le_two_pow_n n
    _ = 0 := by rw [hn]
  exact Nat.not_le_of_gt (by decide) h_1_le_0

/-- For any field element (x:F) where x^2 = x*z + 1, this theorem gives a closed form for x^(2^i) -/
theorem pow_exp_of_2_repr_given_x_square_repr {F : Type*} [instField: Field F] (sumZeroIffEq: ∀ (x y : F), x + y = 0 ↔ x = y) (x z: F) (h_z_non_zero: z ≠ 0) (h_x_square: x^2 = x*z + 1): ∀ i : ℕ,
  x^(2^i) = x * z^(2^i - 1) + ∑ j ∈ Finset.Icc 1 i, z^(2^i - 2^j) := by
  intro i
  induction i with
  | zero =>
    -- # Base case (i = 0): When `i = 0`, the expression simplifies to: x^(2^0) = x (trivial)
    -- ⊢ x ^ 2 ^ 0 = x * z ^ (2 ^ 0 - 1) + ∑ j ∈ Finset.Icc 1 0, z ^ (2 ^ 0 - 2 ^ j)
    rw [pow_zero, pow_one, Nat.sub_self, pow_zero, mul_one]
    -- ⊢ x = x + ∑ j ∈ Finset.Icc 1 0, z ^ (1 - 2 ^ j)
    have range_is_empty:¬1 ≤ 0 := by linarith
    rw [Finset.Icc_eq_empty range_is_empty, Finset.sum_empty, add_zero]
  | succ n x_pow_2_pow_n =>
    -- # Inductive step: assume the result holds for `i = n`. We want to show that the result holds for `i = n+1` that x^(2^(n+1)) = x * z^(2^(n+1) - 1) + ∑(j ∈ Finset.Icc 1 (n+1)) z^(2^(n+1) - 2^j), or LHS = RHS for short (*)
    -- ## Step 0. Using the induction hypothesis, we know that:
      -- x_pow_2_pow_n: x^(2^n) = x * z^(2^n - 1) + ∑(j ∈ Finset.Icc 1 n) z^(2^n - 2^j)
    -- ## Step 1. Next, we consider the term `x^(2^(n+1))`. We can write: x^(2^(n+1)) = (x^(2^n))^2
      -- By the induction hypothesis, we already have the expression for `x^(2^n)`. Substituting that into the equation for `x^(2^(n+1))`, we get:
        -- x_pow_2_pow_n_plus_1: x^(2^(n+1)) = (x^(2^n))^2 = [x * z^(2^n - 1) + ∑(j ∈ Finset.Icc 1 n) z^(2^n - 2^j)]^2 = [L + R]^2
        -- = L^2 + R^2 = (x * z^(2^n - 1))^2 + (∑(j ∈ Finset.Icc 1 n) z^(2^n - 2^j))^2 (via Frobenius automorphism property)
    -- ## Step 2. At this point, we need to simplify these terms:
      -- + first term (L^2): `[(x * z^(2^n - 1))^2]`, can be rewritten as `L_pow_2 = x^2 * z^(2^n - 1))^2 = x^2 * z^((2^n - 1) * 2) = x^2 * z^(2^(n+1) - 2) = x^2 * z^(2^(n+1) - 1) * z^(-1) = x * z^(2^(n+1) - 1) * (x * z^(-1)) = [x * z^(2^(n+1) - 1)] + x * z^(2^(n+1) - 1) * (x * z^(-1) + 1)`
      -- + second term (R^2): `R_pow_2 = [(∑(j ∈ Finset.Icc 1 n) z^(2^n - 2^j))^2]`, can be rewritten as `∑(j ∈ Finset.Icc 1 n) (z^(2^n - 2^j))^2 = ∑(j ∈ Finset.Icc 1 n) z^(2^(n+1) - 2^(j+1))
      -- = ∑(j ∈ Finset.Icc 2 (n+1)) z^(2^(n+1) - 2^j)
      -- = [∑(j ∈ Finset.Icc 1 (n+1)), z^(2^(n+1) - 2^j)] - z^(2^(n+1) - 2^1)`
    -- ## Step 3: Rewrite the goals
    -- (*) ↔ LHS = x^(2^(n+1)) = L_pow_2 + R_pow_2
      -- = [x * z^(2^(n+1) - 1)] + x * z^(2^(n+1) - 1) * (x * z^(-1) + 1) -- This is L_pow_2
      -- + [∑(j ∈ Finset.Icc 1 (n+1)) z^(2^(n+1) - 2^j)] - z^(2^(n+1) - 2^1) -- This is R_pow_2
      -- = [x * z^(2^(n+1) - 1) + ∑(j ∈ Finset.Icc 1 (n+1)) z^(2^(n+1) - 2^j)] + [x * z^(2^(n+1) - 1) * (x * z^(-1) + 1) - z^(2^(n+1) - 2^1) -- range terms
      -- = RHS + [x * z^(2^(n+1) - 1) * (x * z^(-1) + 1) - z^(2^(n+1) - 2^1] = RHS
    -- ↔ [x * z^(2^(n+1) - 1) * (x * z^(-1) + 1) - z^(2^(n+1) - 2^1] = 0 (**) or LHS2 = RHS2

    -- ## Step 1

    have x_pow_2_pow_n_plus_1 : x^(2^(n + 1)) = (x^(2^n))^2 := by
      rw [pow_add, pow_mul, pow_one]
    rw [x_pow_2_pow_n] at x_pow_2_pow_n_plus_1
    let L := x * z^(2^n - 1)
    let R := ∑ j ∈ Finset.Icc 1 n, z ^ (2 ^ n - 2 ^ j)
    have x_pow_2_pow_n_plus_1 : x^(2^(n + 1)) = L^2 + R^2 := by
      calc x^(2^(n + 1)) = (L + R)^2 := by rw [x_pow_2_pow_n_plus_1]
        -- sum_of_pow_exp_of_2 (sumZeroIffEq := sumZeroIffEq) (a:=x) (b:=y) (c:=x+y) (i:=1) (sum_eq)
        _ = L^(2^1) + R^(2^1) := by exact (sum_of_pow_exp_of_2 (sumZeroIffEq := sumZeroIffEq) (i:=1) (a:=L) (b:=R) (c:=L+R) (h_sum_a_b_eq_c:=by rfl)).symm
        _ = L^2 + R^2 := by rw [pow_one]

    -- ## Step 2
    let instSemiring := instField.toDivisionSemiring
    let instGroupWithZero := instSemiring.toGroupWithZero

    have L_pow_2 : L^2 = x * z^(2^(n+1) - 1) + x * z^(2^(n+1) - 1) * (x * (z^1)⁻¹ + 1) := by
      calc L^2 = (x * z^(2^n - 1))^2 := by rfl
        _ = x^2 * (z^(2^n - 1))^2 := by rw [mul_pow]
        _ = x^2 * z ^ ((2 ^ n - 1) * 2) := by rw [←pow_mul]
        _ = x^2 * z ^ (2^n * 2 - 2) := by rw [Nat.mul_sub_right_distrib] -- use Nat version
        _ = x^2 * z ^ (2^(n+1) - 2) := by rw [←Nat.pow_succ]
        _ = x^2 * z ^ ((2^(n+1) - 1) - 1) := by rw [Nat.sub_sub]
        _ = x^2 * (z ^ (2^(n+1) - 1) * (z^1)⁻¹) := by
          have left_exp_le_1 : 1 ≤ 2 ^ (n + 1) - 1 := by
            apply Nat.le_sub_of_add_le -- ⊢ 1 + 1 ≤ 2 ^ (n + 1)
            rw [Nat.add_eq_two_iff.mpr] -- ⊢ 2 ≤ 2 ^ (n + 1)
            exact two_le_two_pow_n_plus_1 n
            norm_num -- solve: 1 = 1 ∧ 1 = 1
          rw [←pow_sub₀ (a:=z) (ha:=h_z_non_zero) (h:=left_exp_le_1)]
        _ = (x * z ^ (2^(n+1) - 1)) * (x * (z^1)⁻¹) := by rw [mul_comm, mul_assoc]; ring_nf
        _ = (x * z ^ (2^(n+1) - 1)) * (x * (z^1)⁻¹ + 1 + 1) := by
          have one_plus_one_is_0 := (sumZeroIffEq 1 1).mpr (by rfl)
          rw [add_assoc, one_plus_one_is_0, add_zero]
        _ = (x * z ^ (2^(n+1) - 1)) * (1 + (x * (z^1)⁻¹ + 1)) := by
          rw [←add_assoc]; ring_nf
        _ = (x * z ^ (2^(n+1) - 1)) + (x * z ^ (2^(n+1) - 1)) * (x * (z^1)⁻¹ + 1) := by
          rw [mul_add, mul_one]

    have R_pow_2 : R^2 = (∑(j ∈ Finset.Icc 1 (n+1)), z^(2^(n+1) - 2^j)) - z^(2^(n+1) - 2^1) := by
      calc R^2 = (∑ j ∈ Finset.Icc 1 n, z ^ (2 ^ n - 2 ^ j))^2 := by rfl
        _ = ∑ j ∈ Finset.Icc 1 n, (z^(2 ^ n - 2 ^ j))^2 := by
          exact sum_square_char2 (sumZeroIffEq := sumZeroIffEq) (Finset.Icc 1 n) (fun j => z^(2^n - 2^j))
        _ = ∑ j ∈ Finset.Icc 1 n, z^(2^n*2 - 2^j*2) := by
          apply Finset.sum_congr rfl (fun j _ => by
            rw [←pow_mul (a:=z) (m:=2^n - 2^j) (n:=2), Nat.mul_sub_right_distrib])
        _ = ∑ j ∈ Finset.Icc 1 n, z^(2^(n+1) - 2^(j+1)) := by
          apply Finset.sum_congr rfl (fun j _ => by
            rw [←Nat.pow_succ, ←Nat.pow_succ])
        _ = ∑(j ∈ Finset.Icc 2 (n+1)), z^(2^(n+1) - 2^j) := by
          -- TODO: shorten this sum range shift
          apply Finset.sum_bij' (fun i _ => i + 1) (fun i _ => i - 1)
          · -- left inverse
            intro i hi
            simp only [Finset.mem_Icc] at hi ⊢
            -- ⊢ i + 1 - 1 = i
            rfl
          · -- right inverse
            intro i hi
            -- ⊢ i - 1 + 1 = i
            have ⟨left_bound, _⟩ := Finset.mem_Icc.mp hi -- hi : i ∈ Finset.Icc 2 (n + 1)
            have one_le_left_bound : 1 ≤ i := by
              calc
                1 ≤ 2 := by norm_num
                _ ≤ i := by exact left_bound
            exact Nat.sub_add_cancel one_le_left_bound
          · -- function value match
            intro i hi
            simp only [Nat.add_sub_cancel]
          · -- left membership preservation
            intro i hi
            -- ⊢ i + 1 ∈ Finset.Icc 2 (n + 1)
            rw [Finset.mem_Icc]
            have ⟨left_bound, right_bound⟩ := Finset.mem_Icc.mp hi
            -- ⊢ 2 ≤ i + 1 ∧ i + 1 ≤ n + 1
            apply And.intro
            · exact Nat.succ_le_succ left_bound
            · exact Nat.succ_le_succ right_bound
          -- ⊢ ∀ a ∈ Finset.Icc 2 (n + 1), a - 1 ∈ Finset.Icc 1 n
          · -- right membership preservation
            intro a ha
            simp only [Finset.mem_Icc] at ha
            rw [Finset.mem_Icc]
            have ⟨left_bound, right_bound⟩ := ha
            apply And.intro
            · exact Nat.pred_le_pred left_bound
            · exact Nat.pred_le_pred right_bound
        _ = ∑(j ∈ Finset.Icc 1 (n+1)), z^(2^(n+1) - 2^j) - z^(2^(n+1) - 2^1) := by
          calc
            ∑ j ∈ Finset.Icc 2 (n + 1), z ^ (2 ^ (n + 1) - 2 ^ j) =
              (z ^ (2 ^ (n + 1) - 2^1)) + (∑ j ∈ Finset.Icc 2 (n + 1), z ^ (2 ^ (n + 1) - 2 ^ j)) - (z ^ (2 ^ (n + 1) - 2^1)) := by
              norm_num
            _ = ∑(j ∈ Finset.Icc 1 (n+1)), z^(2^(n+1) - 2^j) - z^(2^(n+1) - 2^1) := by
              have h : Finset.Icc 2 (n + 1) = Finset.Icc 1 (n + 1) \ {1} := by
                ext j
                -- ⊢ j ∈ Finset.Icc 2 (n + 1) ↔ j ∈ Finset.Icc 1 (n + 1) \ {1}
                simp only [Finset.mem_sdiff, Finset.mem_Icc, Finset.mem_singleton]
                -- ⊢ 2 ≤ j ∧ j ≤ n + 1 ↔ (1 ≤ j ∧ j ≤ n + 1) ∧ ¬j = 1
                constructor
                · intro h
                  -- h : 2 ≤ j ∧ j ≤ n + 1
                  -- ⊢ (1 ≤ j ∧ j ≤ n + 1) ∧ ¬j = 1
                  have one_le_j : 1 ≤ j := by
                    calc 1 ≤ 2 := by norm_num
                    _ ≤ j := by exact h.left
                  have j_ne_one : j ≠ 1 := by
                    intro hj1
                    rw [hj1] at h
                    norm_num at h
                  exact ⟨⟨one_le_j, h.2⟩, j_ne_one⟩
                · intro ⟨⟨h1, h2⟩, hj⟩
                  push_neg at hj
                  -- ⊢ 2 ≤ j ∧ j ≤ n + 1, h1 : 1 ≤ j, h2 : j ≤ n + 1, hj : j ≠ 1
                  constructor
                  · apply Nat.succ_le_of_lt
                    apply Nat.lt_of_le_of_ne
                    · exact h1
                    · push_neg
                      exact hj.symm
                  · exact h2
              rw [h]
              rw [Finset.sum_sdiff_eq_sub]
              simp [Finset.singleton_subset_iff]
              -- ⊢ {1} ⊆ Finset.Icc 1 (n + 1)
              exact singleton_subset_Icc n

    -- ## Step 3: Rewrite the goals
    have sum_L_sq_R_sq: L^2 + R^2 = x * z^(2^(n+1) - 1) + x * z^(2^(n+1) - 1) * (x * (z^1)⁻¹ + 1) + (∑(j ∈ Finset.Icc 1 (n+1)), z^(2^(n+1) - 2^j)) - z^(2^(n+1) - 2^1) := by
      rw [L_pow_2, R_pow_2, add_sub_assoc]
    rw [x_pow_2_pow_n_plus_1]
    rw [sum_L_sq_R_sq]

    -- x * z ^ (2 ^ (n + 1) - 1) * (x * (z ^ 1)⁻¹ + 1) +
      -- ∑ j ∈ Finset.Icc 1 (n + 1), z ^ (2 ^ (n + 1) - 2 ^ j)

    set t1 := x * z ^ (2 ^ (n + 1) - 1)
    set t2 := x * z ^ (2 ^ (n + 1) - 1) * (x * (z ^ 1)⁻¹ + 1)
    set t3 := ∑ j ∈ Finset.Icc 1 (n + 1), z ^ (2 ^ (n + 1) - 2 ^ j)
    set t4 := z ^ (2 ^ (n + 1) - 2 ^ 1)
    -- ⊢ t1 + t2 + t3 - t4 = t1 + t3
    rw [add_assoc t1 t2 t3, add_comm t2 t3, ← add_assoc t1 t3 t2]
    rw [sub_eq_add_neg]
    -- ⊢ t1 + t3 + t2 + (-t4) = t1 + t3
    -- ## Step 4: Reduce to h_x_square hypothesis: x^2 = xz + 1
    have t2_minus_t4: t2 + (-t4) = 0 := by
      set E := 2^(n+1)
      have one_plus_one_is_0: (1:F) + 1 = 0 := (sumZeroIffEq 1 1).mpr (by rfl)
      have xz_plus_xz_is_0: (x*z:F) + x*z = 0 := (sumZeroIffEq (x*z) (x*z)).mpr (by rfl)
      calc t2 + (-t4) = x * z^(E - 1) * (x * (z^1)⁻¹ + 1) + (-z^(E - 2^1)) := by rfl
        _ = x * z^(E - 1) * x * (z^1)⁻¹ + x * z^(E - 1) * 1 + (-z^(E - 2)) := by ring_nf
        _ = x^2 * z^(E - 1) * (z^1)⁻¹ + x * z^(E - 1) + (-z^(E - 2)) := by ring_nf
        _ = x^2 * (z^(E - 1) * (z^1)⁻¹) + x * z^(E - 1) + (-z^(E - 2)) := by ring_nf
        _ = x^2 * z^(E - 2) + x * z^(E - 1) + (-z^(E - 2)) := by
          have one_le_E_minus_one: 1 ≤ E - 1 := by
            apply Nat.le_sub_of_add_le -- ⊢ 1 + 1 ≤ 2 ^ (n + 1)
            rw [Nat.add_eq_two_iff.mpr] -- ⊢ 2 ≤ 2 ^ (n + 1)
            exact two_le_two_pow_n_plus_1 n
            norm_num -- solve: 1 = 1 ∧ 1 = 1
          rw [←pow_sub₀ z h_z_non_zero one_le_E_minus_one]
          rfl
        _ = x^2 * z^(E - 2) + x * z^(E - 2) * z + (-z^(E - 2)) := by
          have z_pow_eq: z^(E - 1) = z^(E - 2) * z := by
            rw [←pow_succ] -- ⊢ z ^ (E - 1) = z ^ (E - 2 + 1)
            congr 1 -- focus on the exponent: ⊢ E - 2 + 1 = E - 1
            norm_num -- ⊢ E = E - 2 + 2
            rw [Nat.sub_add_cancel (h:=two_le_two_pow_n_plus_1 n)]
          rw [z_pow_eq]
          ring_nf
        _ = z^(E - 2) * (x^2 + x*z + (-1)) := by ring_nf
        _ = z^(E - 2) * (x^2 + x*z + 1) := by
          have neg_one_eq_one : (-1 : F) = 1 := by
            rw [← add_eq_zero_iff_eq_neg.mp one_plus_one_is_0]
          rw [neg_one_eq_one]
        _ = z^(E - 2) * (x*z + 1 + x*z + 1) := by rw [h_x_square]
        _ = z^(E - 2) * (x*z + x*z + 1 + 1) := by ring_nf
        _ = z^(E - 2) * ((x*z + x*z) + (1 + 1)) := by ring_nf
        _ = z^(E - 2) * (0 + 0) := by rw [one_plus_one_is_0, xz_plus_xz_is_0]
        _ = 0 := by ring_nf

    rw [add_assoc (t1 + t3), t2_minus_t4, add_zero]

structure PolyInstanceResult (F : Type _) [Field F] (specialElement : F) where
  poly : Polynomial F
  monic : Monic poly
  not_unit : ¬IsUnit poly
  deg_poly_is_2: poly.degree = 2
  nat_deg_poly_is_2 : poly.natDegree = 2
  coeffOfX_0 : poly.coeff 0 = 1
  coeffOfX_1 : poly.coeff 1 = specialElement
  poly_form: poly = X^2 + (C specialElement * X + 1)

def PolyInstances (F : Type _) [Field F] (specialElement : F) :
    PolyInstanceResult F specialElement :=

  let t1 := C specialElement
  have deg_t1_le_0 : t1.degree ≤ 0 := by exact degree_C_le
  let newPoly : F[X] := X^2 + (t1 * X + 1)
  let poly_form: newPoly = X^2 + (t1 * X + 1) := rfl

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
    coeffOfX_1 := coeffOfX_1,
    poly_form := poly_form
  }
  result

theorem inverse_is_root_of_prevPoly
    {prevBTField : Type*} [Field prevBTField]
    {curBTField : Type*} [Field curBTField]
    (of_prev : prevBTField →+* curBTField)
    (u : curBTField) (t1 : prevBTField)
    (specialElementNeZero : u ≠ 0)
    (eval_prevPoly_at_root : u^2 + of_prev t1 * u + 1 = 0)
    (h_eval : ∀ (x: curBTField), eval₂ of_prev x (X^2 + (C t1 * X + 1)) = x^2 + of_prev t1 * x + 1) :
    eval₂ of_prev u⁻¹ (X^2 + (C t1 * X + 1)) = 0 := by
    let u1 := u⁻¹
    rw [h_eval u1]
    have u1_eq_u_pow_minus_1 : u1 = 1/u := by
      unfold u1
      ring_nf
    rw [u1_eq_u_pow_minus_1]
    -- theorem mul_left_cancel_iff : a * b = a * c ↔ b = c :=
    -- ⊢ (1 / u) ^ 2 + of_prev t1 * (1 / u) + 1 = 0
    -- convert to (u^2) * (1/u)^2 + u^2 * t1 * (1/u) + u^2 = u^2 * 0 = 0
    have h_clear_denom : (1/u)^2 + of_prev t1 * (1/u) + 1 = 0 ↔
      u^2 * ((1/u)^2 + of_prev t1 * (1/u) + 1) = 0 := by
      constructor
      · intro h; rw [h]; simp
      · intro h;
        rw [←mul_zero (u^2)] at h
        exact mul_left_cancel₀ (pow_ne_zero 2 specialElementNeZero) h
    rw [h_clear_denom]
    -- Expand and simplify
    -- ⊢ u ^ 2 * ((1 / u) ^ 2 + of_prev t1 * (1 / u) + 1) = 0
    ring_nf
    calc
      u^2 + u^2 * u⁻¹ * of_prev t1 + u^2 * u⁻¹^2 = u^2 + u * u * u⁻¹ * of_prev t1 + u * u * u⁻¹ * u⁻¹ := by ring_nf
      _ = u^2 + u * of_prev t1 + 1 := by
        rw [mul_assoc (u)]
        have u_mul_u1_eq_1 : u * u⁻¹ = 1 := by
          exact mul_inv_cancel₀ specialElementNeZero
        rw [u_mul_u1_eq_1, mul_one, u_mul_u1_eq_1]
      -- , mul_inv_cancel, mul_one, mul_inv_cancel]
      _ = u^2 + of_prev t1 * u + 1 := by ring_nf
      _ = 0 := by exact eval_prevPoly_at_root

theorem sum_of_root_and_inverse_is_t1
    {prevBTField : Type*} [Field prevBTField]
    {curBTField : Type*} [Field curBTField]
    (of_prev : prevBTField →+* curBTField)
    (u : curBTField) (t1 : prevBTField)
    (specialElementNeZero : u ≠ 0)
    (eval_prevPoly_at_root : u^2 + of_prev t1 * u + 1 = 0)
    (sumZeroIffEq : ∀ (x y : curBTField), x + y = 0 ↔ x = y) :
    u + u⁻¹ = of_prev t1 := by
  -- ⊢ u + u⁻¹ = of_prev t1
  have h_clear_denom : u + u⁻¹ = of_prev t1 ↔
    u^1 * (u + u⁻¹) = u^1 * of_prev t1 := by
    constructor
    · intro h; rw [h]
    · intro h;
      exact mul_left_cancel₀ (pow_ne_zero 1 specialElementNeZero) h
  rw [h_clear_denom]
  -- ⊢ u * (u + u⁻¹) = u ^ 1 * of_prev t1
  have u_pow_2_plus_u_pow_2_is_0: u^2 + u^2 = 0 := (sumZeroIffEq (u^2) (u^2)).mpr (by rfl)
  have one_plus_one_is_0 := (sumZeroIffEq 1 1).mpr (by rfl)
  have eq: u^1 * (u + u⁻¹) = u^1 * of_prev t1 := by
    calc
      u^1 * (u + u⁻¹) = u^1 * u + u^1 * u⁻¹ := by ring_nf
      _ = u^2 + 1 := by rw [pow_one, mul_inv_cancel₀ (h := specialElementNeZero)]; ring_nf
      _ = u^2 + 1 + 0 := by ring_nf
      _ = u^2 + 1 + (u^2 + of_prev t1 * u + 1) := by rw [←eval_prevPoly_at_root]
      _ = (u^2 + u^2) + of_prev t1 * u + (1 + 1) := by ring_nf
      _ = of_prev t1 * u := by rw [u_pow_2_plus_u_pow_2_is_0, one_plus_one_is_0, zero_add, add_zero]
      _ = u^1 * of_prev t1 := by rw [←pow_one u]; ring_nf
  exact eq

theorem self_sum_eq_zero
    {prevBTField : Type*} [CommRing prevBTField]
    (sumZeroIffEqPrev : ∀ (x y : prevBTField), x + y = 0 ↔ x = y)
    (prevPoly : Polynomial prevBTField)
    (hf_deg : prevPoly.natDegree = 2)
    (hf_monic : Monic prevPoly) :
    ∀ (x : AdjoinRoot prevPoly), x + x = 0 := by
  set u := AdjoinRoot.root prevPoly
  intro x
  -- First construct the unique linear form using the degree and monic properties
  have unique_linear_form := unique_linear_form_of_elements_in_adjoined_commring (hf_deg := hf_deg) (hf_monic := hf_monic)
  have x_linear_form : ∃! (p : prevBTField × prevBTField), x = (of prevPoly) p.1 * u + (of prevPoly) p.2 := by
    exact unique_linear_form x
  have ⟨⟨x1, x2⟩, x_eq⟩ := x_linear_form
  have x1_plus_x1_eq_0: x1 + x1 = 0 := (sumZeroIffEqPrev x1 x1).mpr rfl
  have x2_plus_x2_eq_0: x2 + x2 = 0 := (sumZeroIffEqPrev x2 x2).mpr rfl
  rw [x_eq.1]
  calc
    (of prevPoly) x1 * u + (of prevPoly) x2 + ((of prevPoly) x1 * u + (of prevPoly) x2) = (of prevPoly) x1 * u + (of prevPoly) x2 + ((of prevPoly) x1 * u + (of prevPoly) x2) := by rfl
    _ = (of prevPoly) x1 * u + (of prevPoly) x1 * u + ((of prevPoly) x2 + (of prevPoly) x2) := by ring
    _ = ((of prevPoly) x1 + (of prevPoly) x1) * u + ((of prevPoly) x2 + (of prevPoly) x2) := by ring_nf
    _ = (of prevPoly) (x1 + x1) * u + (of prevPoly) (x2 + x2) := by
      rw [map_add, map_add]
    _ = (of prevPoly) 0 * u + (of prevPoly) 0 := by rw [x1_plus_x1_eq_0, x2_plus_x2_eq_0]
    _ = 0 * u + 0 := by rw [map_zero]
    _ = 0 := by ring

    -- have selfSumEqZero: ∀ (x : curBTField), x + x = 0 := self_sum_eq_zero (sumZeroIffEqPrev := sumZeroIffEqPrevBTField) (prevPoly:=prevPoly) (hf_deg:=prevPolyNatDegIs2) (hf_monic:=prevPolyIsMonic)

theorem sum_zero_iff_eq_of_self_sum_zero {F : Type*} [AddGroup F] (h_self_sum_eq_zero: ∀ (x : F), x + x = 0) :
    ∀ (x y : F), x + y = 0 ↔ x = y := by
  intro x y
  have y_sum_y_eq_0: y + y = 0 := h_self_sum_eq_zero y
  constructor
  · -- (→) If x + y = 0, then x = y
    intro h_sum_zero
    -- Add y to both sides: (x + y) + y = 0 + y
    rw [←add_left_inj y] at h_sum_zero
    rw [zero_add, add_assoc] at h_sum_zero
    rw [y_sum_y_eq_0, add_zero] at h_sum_zero
    exact h_sum_zero
  · -- (←) If x = y, then x + y = 0
    intro h_eq
    rw [h_eq]
    exact y_sum_y_eq_0

/-- A variant of `Finset.mul_prod_erase` with the multiplication swapped. -/
@[to_additive "A variant of `Finset.add_sum_erase` with the addition swapped."]
theorem prod_mul_erase {α β : Type*} [CommMonoid β] [DecidableEq α] (s : Finset α) (f : α → β) {a : α} (h : a ∈ s) :
    f a * (∏ x ∈ s.erase a, f x) = ∏ x ∈ s, f x := by rw [mul_comm]; exact Finset.prod_erase_mul s f h

theorem eval₂_quadratic_prevField_coeff
  {prevBTField : Type*} [CommRing prevBTField]
  {curBTField : Type*} [CommRing curBTField]
  (of_prev : prevBTField →+* curBTField)
  (t1 : prevBTField)
  (x : curBTField) :
  eval₂ of_prev x (X^2 + (C t1 * X + 1)) = x^2 + of_prev t1 * x + 1 := by
  calc
    eval₂ of_prev x (X^2 + (C t1 * X + 1)) = eval₂ of_prev x (X^2) + eval₂ of_prev x (C t1 * X) + eval₂ of_prev x 1 := by rw [eval₂_add, add_assoc, eval₂_add]
    _ = x^2 + of_prev t1 * x + 1 := by rw [eval₂_pow, eval₂_mul, eval₂_C, eval₂_X, eval₂_one]

-- theorem pow_exp_of_2_repr_given_x_square_repr {F : Type*} [instField: Field F] (sumZeroIffEq: ∀ (x y : F), x + y = 0 ↔ x = y) (x z: F) (h_z_non_zero: z ≠ 0) (h_x_square: x^2 = x*z + 1): ∀ i : ℕ,
--   x^(2^i) = x * z^(2^i - 1) + ∑ j ∈ Finset.Icc 1 i, z^(2^i - 2^j) :=

lemma galois_eval_in_BTField
    {curBTField : Type*} [Field curBTField]
    (u : curBTField) (t1 : curBTField) -- here t1 is already lifted to curBTField
    (k : ℕ)
    (sumZeroIffEq: ∀ (x y : curBTField), x + y = 0 ↔ x = y)
    (prevSpecialElementNeZero : t1 ≠ 0)
    (u_plus_inv_eq_t1 : u + u⁻¹ = t1)
    (h_u_square: u^2 = u*t1 + 1)
    (h_t1_pow: t1^(2^(2^k)-1) = 1 ∧ (t1⁻¹)^(2^(2^k)-1) = 1)
    (h_t1_pow_2_pow_2_pow_k:  t1^(2^(2^k)) = t1)
    (h_t1_inv_pow_2_pow_2_pow_k:  (t1⁻¹)^(2^(2^k)) = t1⁻¹)
    (trace_map_at_inv: ∑ i ∈ Finset.range (2 ^ k), t1⁻¹ ^ (2 ^ i) = 1) :
    u^(2^(2^k)) = u⁻¹ := by

  have u_pow_2_pow_k: u ^ 2 ^ 2 ^ k = u * t1 ^ (2 ^ 2 ^ k - 1) + ∑ j ∈ Finset.Icc 1 (2 ^ k), t1 ^ (2 ^ 2 ^ k - 2 ^ j) := pow_exp_of_2_repr_given_x_square_repr (sumZeroIffEq := sumZeroIffEq) (x:=u) (z:=t1) (h_z_non_zero:=prevSpecialElementNeZero) (h_x_square:=h_u_square) (i:=2^k)
  rw [u_pow_2_pow_k]
  rw [h_t1_pow.left, mul_one]
  have sum_eq_t1: ∑ i ∈ Finset.Icc 1 (2 ^ k), t1 ^ (2 ^ 2 ^ k - 2 ^ i) = t1 := by
    calc
      ∑ i ∈ Finset.Icc 1 (2 ^ k), t1 ^ (2 ^ 2 ^ k - 2 ^ i) = ∑ i ∈ Finset.Icc 1 (2 ^ k), ((t1 ^ (2 ^ 2 ^ k)) * (t1^(2 ^ i))⁻¹) := by
        apply Finset.sum_congr rfl (fun i hi => by
          have h_gte_0_pow: 2 ^ i ≤ 2 ^ 2 ^ k := by
            rw [Finset.mem_Icc] at hi -- hi : 1 ≤ i ∧ i ≤ 2 ^ k
            apply pow_le_pow_right₀ (by decide) (hi.2)
          rw [pow_sub₀ (a:=t1) (ha:=prevSpecialElementNeZero) (h:=h_gte_0_pow)]
        )
      _ = ∑ i ∈ Finset.Icc 1 (2 ^ k), (t1 * (t1^(2 ^ i))⁻¹) := by
        apply Finset.sum_congr rfl (fun i hi => by
          rw [h_t1_pow_2_pow_2_pow_k]
        )
      _ = ∑ i ∈ Finset.Icc 1 (2 ^ k), (t1 * (t1⁻¹)^(2 ^ i)) := by
        apply Finset.sum_congr rfl (fun i hi => by
          rw [inv_pow (a:=t1)]
        )
      _ = t1 * (∑ i ∈ Finset.Icc 1 (2 ^ k), (t1⁻¹)^(2 ^ i)) := by
        rw [Finset.mul_sum]
      _ = t1 * (∑ i ∈ Finset.Icc 1 (2 ^ k - 1), (t1⁻¹)^(2 ^ i) + (t1⁻¹)^(2^2^k)) := by
        congr 1 -- Match t1 * a = t1 * b by proving a = b
        rw [←Finset.sum_erase_add _ _ (by rw [Finset.mem_Icc]; exact ⟨one_le_two_pow_n k, le_refl _⟩)]
        congr 2
        -- ⊢ (Finset.Icc 1 (2 ^ k)).erase (2 ^ k) = Finset.Icc 1 (2 ^ k - 1)
        ext x -- consider an element
        -- ⊢ x ∈ (Finset.Icc 1 (2 ^ k)).erase (2 ^ k) ↔ x ∈ Finset.Icc 1 (2 ^ k - 1)
        simp only [Finset.mem_erase, Finset.mem_Icc]
        -- ⊢ x ≠ 2 ^ k ∧ 1 ≤ x ∧ x ≤ 2 ^ k ↔ 1 ≤ x ∧ x ≤ 2 ^ k - 1
        constructor
        · intro h -- h : x ≠ 2 ^ k ∧ 1 ≤ x ∧ x ≤ 2 ^ k
          have hx : x ≤ 2 ^ k - 1 := Nat.le_pred_of_lt (lt_of_le_of_ne h.2.2 h.1)
          exact ⟨h.2.1, hx⟩
        · intro h -- ⊢ x ≠ 2 ^ k ∧ 1 ≤ x ∧ x ≤ 2 ^ k
          -- ⊢ x ≠ 2 ^ k ∧ 1 ≤ x ∧ x ≤ 2 ^ k
          refine ⟨?_, h.1, Nat.le_trans h.2 (Nat.sub_le (2 ^ k) 1)⟩
          intro hx_eq
          have hx_le:= h.2
          rw [hx_eq] at hx_le
          -- hx_le: 2^k < 2^k - 1
          have lt_succ: 2^k - 1 < 2^k := by
            calc 2^k - 1 < 2^k - 1 + 1 := Nat.lt_succ_self (2^k - 1)
              _ = 2^k := by rw [Nat.sub_add_cancel (h:=one_le_two_pow_n k)]
          exact Nat.lt_irrefl _ (Nat.lt_of_le_of_lt hx_le lt_succ)
      _ = t1 * (∑ i ∈ Finset.Icc 1 (2 ^ k - 1), (t1⁻¹)^(2 ^ i) + t1⁻¹) := by rw [h_t1_inv_pow_2_pow_2_pow_k]
      _ = t1 * (∑ i ∈ Finset.Icc 1 (2 ^ k - 1), (t1⁻¹)^(2 ^ i) + (t1⁻¹)^1) := by
        congr
        · rw [pow_one]
      _ = t1 * ((t1⁻¹)^(2^0) + ∑ i ∈ Finset.Icc 1 (2 ^ k - 1), (t1⁻¹)^(2 ^ i)) := by
        rw [add_comm, pow_zero]
      _ = t1 * (∑ i ∈ Finset.Icc 0 (2 ^ k - 1), (t1⁻¹)^(2 ^ i)) := by
        congr 1 -- NOTE: we can also use Finset.add_sum_erase in this case
      _ = t1 * (∑ i ∈ Finset.range (2 ^ k), (t1⁻¹)^(2 ^ i)) := by
        congr 1
        have range_eq_ico: Finset.Icc 0 (2 ^ k - 1) = Finset.range (2 ^ k) := by
          rw [←Nat.range_succ_eq_Icc_zero (2^k - 1)]
          congr
          rw [Nat.sub_add_cancel]
          exact one_le_two_pow_n k
        congr -- auto use range_eq_ico
      _ = t1 := by
        rw [trace_map_at_inv, mul_one]
  rw [sum_eq_t1]
  rw [←add_right_inj u, ←add_assoc]
  have u_plus_u_eq_0: u + u = 0 := by exact (sumZeroIffEq u u).mpr (by rfl)
  rw [u_plus_u_eq_0, zero_add] -- ⊢ t1 = u + u⁻¹
  exact u_plus_inv_eq_t1.symm

-- curBTField ≃ 𝔽_(2^(2^(k+1)))
theorem galois_automorphism_power
    {curBTField : Type*} [Field curBTField]
    (u : curBTField) (t1 : curBTField) -- here t1 is already lifted to curBTField
    (k : ℕ)
    (sumZeroIffEq: ∀ (x y : curBTField), x + y = 0 ↔ x = y)
    (specialElementNeZero : u ≠ 0)
    (prevSpecialElementNeZero : t1 ≠ 0)
    (u_plus_inv_eq_t1 : u + u⁻¹ = t1)
    (h_u_square: u^2 = u*t1 + 1)
    (h_t1_pow: t1^(2^(2^k)-1) = 1 ∧ (t1⁻¹)^(2^(2^k)-1) = 1)
    (trace_map_roots : ∑ i ∈ Finset.range (2 ^ k), t1 ^ (2 ^ i) = 1 ∧
                      ∑ i ∈ Finset.range (2 ^ k), t1⁻¹ ^ (2 ^ i) = 1) :
    u^(2^(2^k)) = u⁻¹ ∧ (u⁻¹)^(2^(2^k)) = u := by

  have h_t1_pow_2_pow_2_pow_k:  t1^(2^(2^k)) = t1 := by
    calc t1^(2^(2^k)) = t1^(2^(2^k) - 1 + 1) := by rw [Nat.sub_add_cancel (h:=one_le_two_pow_n (2^k))]
      _ = t1 := by rw [pow_succ, h_t1_pow.left, one_mul]
  have h_t1_inv_pow_2_pow_2_pow_k:  (t1⁻¹)^(2^(2^k)) = t1⁻¹ := by
    calc (t1⁻¹)^(2^(2^k)) = (t1⁻¹)^(2^(2^k) - 1 + 1) := by rw [Nat.sub_add_cancel (h:=one_le_two_pow_n (2^k))]
      _ = t1⁻¹ := by rw [pow_succ, h_t1_pow.right, one_mul]
  have h_u_square2: u * t1 + u * u = 1 := by
    rw [←pow_two, add_comm]
    rw [←add_left_inj (a:=u*t1), add_assoc]
    have s: u*t1 + u*t1 = 0 := (sumZeroIffEq (x:=u*t1) (y:=u*t1)).mpr (by rfl)
    rw [s, add_zero, add_comm]
    exact h_u_square
  -------------------------------------------------------------------------------
  constructor
  · -- u^(2^(2^k)) = u⁻¹
    exact galois_eval_in_BTField u t1 k sumZeroIffEq prevSpecialElementNeZero u_plus_inv_eq_t1 h_u_square h_t1_pow h_t1_pow_2_pow_2_pow_k h_t1_inv_pow_2_pow_2_pow_k (trace_map_at_inv:=trace_map_roots.2)
  · -- (u⁻¹)^(2^(2^k)) = u
    have u_is_inv_of_u1: u = u⁻¹⁻¹ := (inv_inv u).symm
    have u1_plus_u_eq_t1: u⁻¹ + u⁻¹⁻¹ = t1 := by rw [←u_plus_inv_eq_t1, add_comm]; rw [← u_is_inv_of_u1]
    have u_square_ne_zero : u^2 ≠ 0 := by
      exact pow_ne_zero 2 specialElementNeZero
    have h_u1_square: u⁻¹^2 = u⁻¹*t1 + 1 := by
      have h_clear_denom: u⁻¹^2 = u⁻¹*t1 + 1 ↔
        u^2 * (u⁻¹^2) = u^2 * (u⁻¹*t1 + 1) := by
        constructor
        · intro h; rw [h];
        · intro h;
          simp [mul_inv_cancel] at h -- h : (u ^ 2)⁻¹ = u⁻¹ * t1 + 1 ∨ u = 0
          have h1 : (u ^ 2)⁻¹ = u⁻¹ * t1 + 1 := by
            cases h with
            | inl h_left => exact h_left  -- (u ^ 2)⁻¹ = u⁻¹ * t1 + 1
            | inr h_right => contradiction  -- u = 0 contradicts u ≠ 0
          rw [←h1]
          rw [inv_pow]
      rw [h_clear_denom]
      -- ⊢ u ^ 2 * u⁻¹ ^ 2 = u ^ 2 * (u⁻¹ * t1 + 1)
      rw [inv_pow, mul_inv_cancel₀ (a:=u^2) (u_square_ne_zero)]
      rw [left_distrib, ←mul_assoc, mul_one, ←pow_sub_one_mul (a:=u) (by norm_num)]
      norm_num
      exact h_u_square2.symm
    have res:= galois_eval_in_BTField (u:=u⁻¹) (t1:=t1) (k:=k) (sumZeroIffEq:=sumZeroIffEq) (prevSpecialElementNeZero:=prevSpecialElementNeZero) (u_plus_inv_eq_t1:=u1_plus_u_eq_t1) (h_u_square:=h_u1_square) (h_t1_pow:=h_t1_pow) (h_t1_pow_2_pow_2_pow_k:=h_t1_pow_2_pow_2_pow_k) (h_t1_inv_pow_2_pow_2_pow_k:=h_t1_inv_pow_2_pow_2_pow_k) (trace_map_at_inv:=trace_map_roots.2)
    rw [←u_is_inv_of_u1] at res
    exact res

structure BinaryTowerResult (F : Type _) (k : ℕ) where
  vec       : (List.Vector F (k + 1))
  instMul   : (Mul F)
  instField : (Field F)
  instNontrivial:(Nontrivial F)
  newPoly   : (Polynomial F)
  specialElement: F
  specialElementNeZero: specialElement ≠ 0
  newPolyForm: newPoly = X^2 + (C specialElement * X + 1)
  degNewPolyIs2: (newPoly.degree = 2)
  newPolyIsMonic: (Monic newPoly)
  instInh   : (Inhabited F)
  instDomain: (IsDomain F)
  isNotUnitPoly: (¬IsUnit newPoly)
  instNoZeroDiv : (NoZeroDivisors F)
  instIrreduciblePoly : (Irreducible (p := (newPoly : Polynomial F)))
  sumZeroIffEq: ∀ (x y : F), x + y = 0 ↔ x = y
  instFintype   : Fintype F  -- New: F is finite
  fieldFintypeCard     : Fintype.card F = 2^(2^k)  -- New: Size is 2^(2^(k+1))
  traceMapEvalAtRootsIs1 : (∑ i in Finset.range (2^k), specialElement^(2^i)) = 1 ∧ (∑ i in Finset.range (2^k), (specialElement⁻¹)^(2^i)) = 1

theorem sum_Icc_split {α : Type*} [AddCommMonoid α] (f : ℕ → α) (a b c : ℕ)
    (h₁ : a ≤ b) (h₂ : b ≤ c):
    ∑ i in Finset.Icc a c, f i = ∑ i in Finset.Icc a b, f i + ∑ i in Finset.Icc (b+1) c, f i := by
  have h_disjoint: Disjoint (Finset.Icc a b) (Finset.Icc (b+1) c) := by
    apply Finset.disjoint_iff_inter_eq_empty.mpr -- main theorem for converting disjoint condition into intersection = ∅ condition
    ext i
    simp only [Finset.mem_inter, Finset.mem_Icc]
    constructor
    · intro h
      -- Alternatively, we can use a single line: linarith [h.1.2, h.2.1]
      have h_le_b : i ≤ b := h.1.2
      have h_ge_b_plus_1 : b + 1 ≤ i := h.2.1
      have h_contradiction : b + 1 ≤ b := le_trans h_ge_b_plus_1 h_le_b
      have h_false : b < b := Nat.lt_of_succ_le h_contradiction
      exact absurd h_false (lt_irrefl b)
    · intro h -- h : i ∈ ∅
      exact absurd h (Finset.not_mem_empty i)

  rw [←Finset.sum_union h_disjoint]
  · congr
    ext j
    simp only [Finset.mem_Icc, Finset.mem_union]
    constructor
    · intro h
      -- h : a ≤ j ∧ j ≤ c
      cases Nat.lt_or_ge j (b+1) with
      | inl h_lt => -- j < (b+1)
        left -- pick the left branch, for OR statement
        exact ⟨h.1, Nat.le_of_lt_succ h_lt⟩
      | inr h_ge => -- b + 1 ≤ j
        right
        exact ⟨h_ge, h.2⟩
    · intro h
      -- h : a ≤ j ∧ j ≤ b ∨ b + 1 ≤ j ∧ j ≤ c
      cases h with
      | inl h_left =>
        -- h_left : a ≤ j ∧ j ≤ b
        exact ⟨h_left.1, Nat.le_trans h_left.2 h₂⟩
      | inr h_right =>
        -- h_right : b + 1 ≤ j ∧ j ≤ c
        exact ⟨Nat.le_trans h₁ (Nat.le_of_succ_le h_right.1), h_right.2⟩

lemma lifted_trace_map_eval_at_roots_prev_BTField
  {curBTField : Type*} [Field curBTField]
  (u : curBTField) (t1 : curBTField) -- here t1 is already lifted to curBTField
  (k : ℕ)
  (sumZeroIffEq: ∀ (x y : curBTField), x + y = 0 ↔ x = y)
  -- (instFintype: Fintype curBTField)
  -- (fintypeCard: Fintype.card curBTField = 2^(2^(k+1)))
  -- (prevSpecialElementNeZero : t1 ≠ 0)
  (u_plus_inv_eq_t1 : u + u⁻¹ = t1)
  (galois_automorphism: u^(2^(2^k)) = u⁻¹ ∧ (u⁻¹)^(2^(2^k)) = u)
  -- (h_u_square: u^2 = u*t1 + 1)
  -- (h_t1_pow: t1^(2^(2^k)-1) = 1 ∧ (t1⁻¹)^(2^(2^k)-1) = 1)
  -- (h_t1_pow_2_pow_2_pow_k:  t1^(2^(2^k)) = t1)
  -- (h_t1_inv_pow_2_pow_2_pow_k:  (t1⁻¹)^(2^(2^k)) = t1⁻¹)
  (trace_map_at_prev_root: ∑ i ∈ Finset.range (2 ^ k), t1 ^ (2 ^ i) = 1) :
  ∑ i ∈ Finset.range (2 ^ (k+1)), u ^ (2 ^ i) = 1 := by

  calc
    ∑ i ∈ Finset.range (2 ^ (k+1)), u ^ (2 ^ i) = ∑ i ∈ Finset.Icc 0 (2^(k+1) - 1), u ^ (2 ^ i) := by
      rw [←Nat.range_succ_eq_Icc_zero (2^(k+1) - 1)]
      congr
      rw [Nat.sub_one_add_one (two_pow_ne_zero (k+1))]
    _ = ∑ i ∈ Finset.Icc 0 (2^k - 1), u ^ (2 ^ i) + ∑ i ∈ Finset.Icc (2^k) (2^(k+1) - 1), u ^ (2 ^ i) := by
      have zero_ne_2_pow_k: 0 ≤ 2^k-1 := by
        rw [←Nat.add_le_add_iff_right (n:=1), Nat.sub_add_cancel (h:=one_le_two_pow_n k), zero_add]
        exact one_le_two_pow_n k
      have h_lt: 2 ^ k ≤ 2 ^ (k + 1) - 1 := by
        rw [pow_add 2 k 1, pow_one, mul_two]
        conv =>
          lhs
          rw [←Nat.add_zero (n:=2^k)]
        rw [Nat.add_sub_assoc (n:=2^k) (m:=2^k) (k:=1) (h:=one_le_two_pow_n k)]
        -- ⊢ 2 ^ k + 0 < 2 ^ k + (2 ^ k - 1)
        rw [Nat.add_le_add_iff_left (n:=2^k)]
        rw [←Nat.add_le_add_iff_right (n:=1) , Nat.sub_add_cancel (h:=one_le_two_pow_n k), zero_add]
        exact one_le_two_pow_n k
      have h_lt_lt: 2^k - 1 ≤ 2^(k+1) - 1 := by
        calc 2^k - 1 ≤ 2^k := Nat.sub_le (2^k) 1
          _ ≤ 2^(k+1) - 1 := h_lt
      have res := sum_Icc_split (f:=fun i => u^(2^i)) (a:=0) (b:=2^k-1) (c:=2^(k+1) - 1) (h₁:=zero_ne_2_pow_k) (h₂:=h_lt_lt)
      rw [Nat.sub_add_cancel (h:=one_le_two_pow_n k)] at res
      rw [res]
    _ = ∑ i ∈ Finset.Icc 0 (2^k - 1), u ^ (2 ^ i)  + ∑ i ∈ Finset.Icc 0 (2^k - 1), u ^ (2 ^ (2^k + i)) := by
      congr 1
      -- ⊢ ∑ i ∈ Finset.Icc (2 ^ k) (2 ^ (k + 1) - 1), u ^ 2 ^ i = ∑ i ∈ Finset.Icc 0 (2 ^ k - 1), u ^ 2 ^ (2 ^ k + i)
      apply Finset.sum_bij' (fun i _ => i - 2^k) (fun i _ => i + 2^k)
      · -- left inverse: g_inv(g(i)) = i
        intro ileft h_left -- h_left : ileft ∈ Finset.Icc (2 ^ k) (2 ^ (k + 1) - 1) ⊢ ileft - 2 ^ k + 2 ^ k = ileft
        simp [Finset.mem_Icc] at h_left
        rw [Nat.sub_add_cancel h_left.1]
      · -- right inverse: g(g_inv(i)) = i
        intro iright h_right
        simp [Finset.mem_Icc] at h_right
        rw [Nat.add_sub_cancel]
      · -- function value match: fLeft(i) = fRight(g(i))
        intro i hi
        simp [Finset.mem_Icc] at hi
        congr
        rw [←Nat.add_sub_assoc (n:=2^k) (m:=i) (k:=2^k) (hi.left), ←add_comm, Nat.add_sub_cancel]
      · -- left membership preservation
        intro i hi
        simp [Finset.mem_Icc] at hi
        simp [Finset.mem_Icc]
        -- conv =>
          -- rhs
        rw [←Nat.sub_add_comm (one_le_two_pow_n k)]
        rw [←Nat.mul_two, ←Nat.pow_succ]
        exact hi.right
      · -- right membership preservation
        intro i hi
        simp [Finset.mem_Icc] at hi
        simp [Finset.mem_Icc]
        rw [Nat.pow_succ, Nat.mul_two, add_comm]
        conv =>
          rhs
          rw [Nat.add_sub_assoc (h:=one_le_two_pow_n k) (n:=2^k)]
        rw [Nat.add_le_add_iff_left (n:=2^k)]
        exact hi
    _ = ∑ i ∈ Finset.Icc 0 (2^k - 1), u ^ (2 ^ i)  + ∑ i ∈ Finset.Icc 0 (2^k - 1), (u ^ (2 ^ (2^k) * 2^i)) := by
      congr -- ⊢ (fun i ↦ u ^ 2 ^ (2 ^ k + i)) = fun i ↦ u ^ (2 ^ 2 ^ k * 2 ^ i)
      ext i
      rw [pow_add]
    _ = ∑ i ∈ Finset.Icc 0 (2^k - 1), u ^ (2 ^ i)  + ∑ i ∈ Finset.Icc 0 (2^k - 1), (u ^ (2 ^ (2^k)))^(2^i) := by
      congr
      ext i
      rw [pow_mul]
    _ = ∑ i ∈ Finset.Icc 0 (2^k - 1), u ^ (2 ^ i)  + ∑ i ∈ Finset.Icc 0 (2^k - 1), (u⁻¹)^(2^i) := by
      rw [galois_automorphism.1]
    _ = ∑ i ∈ Finset.Icc 0 (2^k - 1), (u^2^i + u⁻¹^2^i) := by rw [Finset.sum_add_distrib]
    _ = ∑ i ∈ Finset.Icc 0 (2^k - 1), t1^2^i := by
      apply Finset.sum_congr rfl (fun i hi => by
        have sum_pow_2_pow_i:= sum_of_pow_exp_of_2 (sumZeroIffEq := sumZeroIffEq) (a:=u) (b:=u⁻¹) (c:=t1) (i:=i) (u_plus_inv_eq_t1) -- x^(2^1) + y^(2^1) = (x+y)^(2^1)
        rw [sum_pow_2_pow_i]
      )
    _ = ∑ i ∈ Finset.range (2 ^ k), t1^2^i := by
      rw [←Nat.range_succ_eq_Icc_zero (2^k - 1)]
      rw [Nat.sub_one_add_one (two_pow_ne_zero k)]
    _ = 1 := by rw [trace_map_at_prev_root]

theorem rsum_eq_t1_square_aux
  {curBTField : Type*} [Field curBTField]
  (c1 : curBTField) (u : curBTField) -- here u is already lifted to curBTField
  (k : ℕ)
  (sumZeroIffEq: ∀ (x y : curBTField), x + y = 0 ↔ x = y)
  (x_pow_card: ∀ (x : curBTField), x^(2^(2^(k+1))) = x)
  -- (instFintype: Fintype curBTField)
  -- (fintypeCard: Fintype.card curBTField = 2^(2^(k+1)))
  -- (prevSpecialElementNeZero : u ≠ 0)
  -- (h_u_square: c1^2 = c1*u + 1)
  (u_ne_zero : u ≠ 0)
  -- (h_t1_pow_2_pow_2_pow_k:  u^(2^(2^k)) = u)
  -- (h_t1_inv_pow_2_pow_2_pow_k:  (u⁻¹)^(2^(2^k)) = u⁻¹)
  (trace_map_at_prev_root: ∑ i ∈ Finset.range (2^(k+1)), u ^ (2 ^ i) = 1 ∧ ∑ i ∈ Finset.range (2^(k+1)), u⁻¹ ^ (2 ^ i) = 1):
   ∑ j ∈ Finset.Icc 1 (2 ^ (k + 1)), u ^ (2 ^ 2 ^ (k + 1) - 2 ^ j) = u := by

  have trace_map_icc_t1: ∑ j ∈ Finset.Icc 0 (2^(k+1)-1), u ^ (2^j) = 1 := by
    rw [←Nat.range_succ_eq_Icc_zero (2^(k+1)-1), Nat.sub_add_cancel (h:=one_le_two_pow_n (k+1))]
    exact trace_map_at_prev_root.left
  have trace_map_icc_t1_inv: ∑ j ∈ Finset.Icc 0 (2^(k+1)-1), u⁻¹ ^ (2^j) = 1 := by
    rw [←Nat.range_succ_eq_Icc_zero (2^(k+1)-1), Nat.sub_add_cancel (h:=one_le_two_pow_n (k+1))]
    exact trace_map_at_prev_root.right

  calc
    ∑ j ∈ Finset.Icc 1 (2 ^ (k + 1)), u ^ (2 ^ 2 ^ (k + 1) - 2 ^ j) = ∑ j ∈ Finset.Icc 1 (2 ^ (k + 1)), (u ^ (2 ^ 2 ^ (k + 1)) * ((u) ^ 2 ^ j)⁻¹) := by
      apply Finset.sum_congr rfl (fun j hj => by
        simp [Finset.mem_Icc] at hj -- hj : 1 ≤ j ∧ j ≤ 2 ^ (k + 1)
        have h_gte_0_pow: 2 ^ j ≤ 2 ^ 2 ^ (k + 1) := by
          apply pow_le_pow_right₀ (by decide) (hj.2)
        rw [pow_sub₀ (a := u) (ha := u_ne_zero) (h := h_gte_0_pow)]
      )
    _ = ∑ j ∈ Finset.Icc 1 (2 ^ (k + 1)), ((u) * ((u) ^ 2 ^ j)⁻¹) := by
      rw [x_pow_card (u)]
    _ = u * ∑ j ∈ Finset.Icc 1 (2 ^ (k + 1)), ((u) ^ 2 ^ j)⁻¹ := by rw [Finset.mul_sum]
    _ = u * ∑ j ∈ Finset.Icc 1 (2 ^ (k + 1)), (((u)⁻¹) ^ 2 ^ j) := by
      congr
      ext j
      rw [←inv_pow (a := u) (n := 2 ^ j)]
    _ = u * ∑ j ∈ Finset.Icc 0 (2 ^ (k + 1) - 1), ((u⁻¹) ^ 2 ^ j) := by
      rw [mul_right_inj' (a := u) (ha := u_ne_zero)]
      apply Finset.sum_bij' (fun i _ => if i = 2^(k+1) then 0 else i) (fun i _ => if i = 0 then 2^(k+1) else i)
        -- hi: Maps to Icc 0 (2^(k+1))
      · intro i hi
        simp [Finset.mem_Icc] at hi ⊢
        by_cases h : i = 2^(k+1)
        · simp [h];
        · simp [h];
          have tmp := Nat.lt_iff_le_and_ne.mpr ⟨hi.2, h⟩
          sorry -- exact Nat.le_iff_lt_or_eq.mpr ⟨, False⟩ )
          -- ⊢ ∑ j ∈ Finset.Icc 1 (2 ^ (k + 1)), u⁻¹ ^ 2 ^ j = ∑ j ∈ Finset.Icc 0 (2 ^ (k + 1) - 1), u⁻¹ ^ 2 ^ j
      -- hj: Maps back
      · intro i hi
        simp [Finset.mem_Icc] at hi ⊢
        by_cases h : i = 0
        · simp [h];
        · simp [h];
          intro i_eq
          sorry -- TODO: use False.elim
      -- hij: j (i a) = a
      · intro i hi
        simp [Finset.mem_Icc] at hi
        by_cases h : i = 2^(k+1)
        · simp [h]; sorry
        · simp [h]
      -- hji: i (j b) = b
      · intro i hi
        simp [Finset.mem_Icc] at hi
        by_cases h : i = 0
        · simp [h]
        · simp [h]; sorry
      -- h_sum: Values match
      · intro i hi
        simp [Finset.mem_Icc] at hi
        rw [Finset.mem_Icc]
        sorry
    _ = u := by rw [trace_map_icc_t1_inv, mul_one]

set_option maxHeartbeats 1000000
def binary_tower_inductive_step
  (k : Nat)
  (prevBTField : Type*) [Field prevBTField]
  (prevBTResult: Σ' prevBTField, BinaryTowerResult prevBTField k)
  : Σ' (F : Type _), BinaryTowerResult F (k + 1) := by
  let prevBTField := prevBTResult.fst
  let prevInstField := prevBTResult.2.instField
  let elts := prevBTResult.2.vec
  let prevPoly := prevBTResult.2.newPoly -- poly over prevBTField
  let prevPolyDegIs2 := prevBTResult.2.degNewPolyIs2
  let prevPolyIsMonic: (Monic prevPoly) := prevBTResult.2.newPolyIsMonic
  have prevPolyNatDegIs2 : prevPoly.natDegree = 2 := by
    have h_pos : 0 < 2 := by norm_num
    exact (degree_eq_iff_natDegree_eq_of_pos h_pos).mp prevPolyDegIs2
  have degPrevPolyNe0 : prevPoly.degree ≠ 0 := by
    intro h_deg_eq_0
    rw [prevPolyDegIs2] at h_deg_eq_0
    contradiction
  let instPrevPolyIrreducible := prevBTResult.2.instIrreduciblePoly
  let prevSpecialElement: prevBTField := prevBTResult.2.specialElement
  let prevPolyForm: prevPoly = X^2 + (C prevSpecialElement * X + 1) := prevBTResult.2.newPolyForm
  let t1: prevBTField := prevSpecialElement
  have t1_ne_zero_in_prevBTField: t1 ≠ 0 := prevBTResult.2.specialElementNeZero
  have h_inj_of_prevPoly : Function.Injective (AdjoinRoot.of prevPoly) := AdjoinRoot.of.injective_of_degree_ne_zero degPrevPolyNe0
  have prevSpecialElementNeZero: of prevPoly t1 ≠ 0 := by
    by_contra h -- h: of prevPoly t1 = 0
    rw [map_eq_zero_iff (AdjoinRoot.of prevPoly) h_inj_of_prevPoly] at h
    contradiction -- with t1_ne_zero_in_prevBTField
  have t1_ne_zero: (AdjoinRoot.of prevPoly) t1 ≠ 0 := by
    by_contra h_t1_eq_zero_in_curBTField
    -- def Injective (f : α → β) : Prop :=
      -- ∀ ⦃a₁ a₂⦄, f a₁ = f a₂ → a₁ = a₂
    have h_t1_eq_zero_in_prevBTField: t1 = 0 := by
      exact h_inj_of_prevPoly (by rw [h_t1_eq_zero_in_curBTField, map_zero])
    contradiction
  let instPrevBTFieldIsFinType: Fintype prevBTField := prevBTResult.2.instFintype
  let prevBTFieldCard: Fintype.card prevBTField = 2^(2^k) := prevBTResult.2.fieldFintypeCard
  let instFactIrrPoly : Fact (Irreducible prevPoly) := ⟨instPrevPolyIrreducible⟩
  let sumZeroIffEqPrevBTField : ∀ (x y : prevBTField), x + y = (0: prevBTField) ↔ x = y := by exact prevBTResult.2.sumZeroIffEq

  let curBTField := AdjoinRoot prevPoly
  let instFieldAdjoinRootOfPoly : Field curBTField := by
    exact AdjoinRoot.instField (f := prevPoly)
  -- Lift to new BTField level
  let u: curBTField := AdjoinRoot.root prevPoly -- generator of curBTField & adjoined root of the prevPoly which generates curBTField
  let adjoinRootOfPoly : AdjoinRoot prevPoly = curBTField := by
    simp [curBTField]
  have u_is_inv_of_u1: u = u⁻¹⁻¹ := (inv_inv u).symm
  let polyInstances := PolyInstances curBTField u
  let coeffOfX_0: polyInstances.poly.coeff 0 = 1 := polyInstances.coeffOfX_0
  let coeffOfX_1: polyInstances.poly.coeff 1 = u := polyInstances.coeffOfX_1
  let newPoly: curBTField[X] := polyInstances.poly -- = X^2 + (t1 * X + 1)
  let newPolyIsMonic := polyInstances.monic
  let instNotUnitPoly: ¬IsUnit newPoly := polyInstances.not_unit
  let instNoZeroDiv : NoZeroDivisors curBTField := inferInstance
  let newElts := elts.map (fun x => (AdjoinRoot.of prevPoly).toFun x)
  let polyRingIsMulZero: MulZeroClass (Polynomial prevBTField) := inferInstance
  let instFieldcurBTField : Field curBTField := by exact AdjoinRoot.instField (f := prevPoly)
  let instMul: Mul curBTField := inferInstance
  let instMulZeroClass : MulZeroClass curBTField := inferInstance
  let instInh: Inhabited curBTField := inferInstance

  let instDomain: IsDomain curBTField := inferInstance
  -- have linear_form_of_elements_in_curBTField: ∀ (c1 : AdjoinRoot prevPoly), ∃ a b, c1 = (of prevPoly) a * root prevPoly + (of prevPoly) b := linear_form_of_elements_in_adjoined_commring (hf_deg := prevPolyNatDegIs2) (hf_monic := prevPolyIsMonic)
  have unique_linear_form_of_elements_in_curBTField: ∀ (c1 : AdjoinRoot prevPoly), ∃! (p : prevBTField × prevBTField), c1 = (of prevPoly) p.1 * root prevPoly + (of prevPoly) p.2 := unique_linear_form_of_elements_in_adjoined_commring (hf_deg := prevPolyNatDegIs2) (hf_monic := prevPolyIsMonic)

  have selfSumEqZero: ∀ (x : curBTField), x + x = 0 := self_sum_eq_zero (sumZeroIffEqPrev := sumZeroIffEqPrevBTField) (prevPoly:=prevPoly) (hf_deg:=prevPolyNatDegIs2) (hf_monic:=prevPolyIsMonic)

  have sumZeroIffEq: ∀ (x y : curBTField), x + y = 0 ↔ x = y := sum_zero_iff_eq_of_self_sum_zero (h_self_sum_eq_zero := selfSumEqZero)

  have u_is_root: u = AdjoinRoot.root prevPoly := rfl
  have h_eval : ∀ (x: curBTField), eval₂ (of prevPoly) x (X^2 + (C t1 * X + 1)) =
                    x^2 + (of prevPoly) t1 * x + 1 := eval₂_quadratic_prevField_coeff (of_prev := of prevPoly) t1

  have eval_prevPoly_at_root : u^2 + (of prevPoly) t1 * u + 1 = 0 := by -- u^2 + t1 * u + 1 = 0
      have h_root : eval₂ (of prevPoly) u prevPoly = 0 := by
        rw [u_is_root]
        exact eval₂_root prevPoly
      have h_expand : eval₂ (of prevPoly) u (X^2 + (C t1 * X + 1)) = 0 := by
        rw [←prevPolyForm]
        exact h_root
      rw [h_eval u] at h_expand
      exact h_expand
  have h_u_square: u^2 = u*t1 + 1 := by
    have h1 := eval_prevPoly_at_root
    rw [←add_right_inj (u^2), ←add_assoc, ←add_assoc] at h1
    rw [selfSumEqZero (u^2), zero_add, add_zero, mul_comm] at h1
    exact h1.symm
  have one_ne_zero: (1: curBTField) ≠ (0: curBTField) := by exact NeZero.out
  have specialElementNeZero: u ≠ 0 := by
    by_contra h_eq
    rw [h_eq] at eval_prevPoly_at_root
    have two_pos : 2 ≠ 0 := by norm_num
    rw [zero_pow two_pos, mul_zero, zero_add, zero_add] at eval_prevPoly_at_root
    exact one_ne_zero eval_prevPoly_at_root

    -- Step 2: transform the equations in curBTField and create new value equalitiy bounds
    -- (1) c1 + c2 = (a + c) * u + (b + d) = u
    -- <=> u * (1 - a - c) = b + d
  let u1 := u⁻¹

  have u1_is_root := inverse_is_root_of_prevPoly (of_prev:= of prevPoly) (u:=u) (t1:=t1) (specialElementNeZero:=specialElementNeZero) (eval_prevPoly_at_root:=eval_prevPoly_at_root) (h_eval:=h_eval)

  have u_plus_u1_eq_t1: u + u⁻¹ = t1 := sum_of_root_and_inverse_is_t1 (of_prev := of prevPoly) (u:=u) (t1:=t1) (specialElementNeZero:=specialElementNeZero) (eval_prevPoly_at_root:=eval_prevPoly_at_root) (sumZeroIffEq:=sumZeroIffEq)

  have linear_comb_of_prevBTField_is_in_curBTField: ∀ (a b : prevBTField), (of prevPoly) a * root prevPoly + (of prevPoly) b = (of prevPoly) a * u + (of prevPoly) b := by
    intro a b
    rw [u_is_root]

  let f : curBTField → prevBTField × prevBTField := fun c1 =>
    let h := unique_linear_form_of_elements_in_curBTField c1  -- Get the unique existential proof
    Classical.choose h

  have inj_f : Function.Injective f := by
    intros c1 c2 h_eq
    unfold f at h_eq
    -- h_eq is now (a1, b1) = (a2, b2), where a1, b1, a2, b2 are defined with Classical.choose
    let h1 := unique_linear_form_of_elements_in_curBTField c1
    let h2 := unique_linear_form_of_elements_in_curBTField c2
    let a1 := (Classical.choose h1).1
    let b1 := (Classical.choose h1).2
    let a2 := (Classical.choose h2).1
    let b2 := (Classical.choose h2).2
    -- Assert that h_eq matches the pair equality
    have pair_eq : (a1, b1) = (a2, b2) := h_eq
    have ha : a1 = a2 := (Prod.ext_iff.mp pair_eq).1
    have hb : b1 = b2 := (Prod.ext_iff.mp pair_eq).2
    have h1_eq : c1 = (of prevPoly) a1 * root prevPoly + (of prevPoly) b1 :=
      (Classical.choose_spec h1).1
    have h2_eq : c2 = (of prevPoly) a2 * root prevPoly + (of prevPoly) b2 :=
      (Classical.choose_spec h2).1
    rw [h1_eq, h2_eq, ha, hb]

  have surj_f : Function.Surjective f := by
    intro (p : prevBTField × prevBTField)
    let c1 := (of prevPoly) p.1 * root prevPoly + (of prevPoly) p.2
    use c1
    have h_ex : c1 = (of prevPoly) p.1 * root prevPoly + (of prevPoly) p.2 := rfl
    have h_uniq := unique_linear_form_of_elements_in_curBTField c1
    have p_spec : c1 = (of prevPoly) p.1 * root prevPoly + (of prevPoly) p.2 := h_ex
    -- Show that f c1 = p by using the uniqueness property
    have h_unique := (Classical.choose_spec h_uniq).2 p p_spec
    -- The function f chooses the unique representation, so f c1 must equal p
    exact h_unique.symm

  have bij_f: Function.Bijective f := by
    constructor
    · exact inj_f  -- Injectivity from instFintype
    · exact surj_f

  have equivRelation: curBTField ≃ prevBTField × prevBTField := by
    exact Equiv.ofBijective (f := f) (hf := bij_f)

  let instFintype : Fintype curBTField := by
    exact Fintype.ofEquiv (prevBTField × prevBTField) equivRelation.symm

  let fieldFintypeCard: Fintype.card curBTField = 2^(2^(k + 1)) := by
    let e : curBTField ≃ prevBTField × prevBTField := Equiv.ofBijective f bij_f
    -- ⊢ Fintype.card curBTField = 2 ^ 2 ^ (k + 1)
    have equivCard := Fintype.ofEquiv_card equivRelation.symm
    rw [Fintype.card_prod] at equivCard
    rw [prevBTFieldCard] at equivCard -- equivCard : Fintype.card curBTField = 2 ^ 2 ^ k * 2 ^ 2 ^ k
    have card_simp : 2 ^ 2 ^ k * 2 ^ 2 ^ k = 2 ^ (2 ^ k + 2 ^ k) := by rw [Nat.pow_add]
    have exp_simp : 2 ^ k + 2 ^ k = 2 ^ (k + 1) := by
      rw [←Nat.mul_two, Nat.pow_succ]
    rw [card_simp, exp_simp] at equivCard
    exact equivCard
  have mul_eq_implies_eq_of_nonzero {F : Type*} [Field F]
    (x y a b : F) (hx : x * a = b) (hy : y * a = b) (ha : a ≠ 0) : x = y := by
    -- Since x * a = b and y * a = b, we have x * a = y * a
    have h : x * a = y * a := by rw [hx, hy]

    -- Subtract y * a from both sides: x * a - y * a = 0
    have h_diff : x * a - y * a = 0 := by rw [h]; simp

    -- Factorize: (x - y) * a = 0
    have h_factor : (x - y) * a = 0 := by rw [sub_mul]; exact h_diff

    -- In a field, if (x - y) * a = 0 and a ≠ 0, then x - y = 0 (no zero divisors)
    have h_xy : x - y = 0 := by apply (mul_eq_zero.mp h_factor).resolve_right ha

    -- Rearranging gives x = y
    exact sub_eq_zero.mp h_xy

  have prevTraceMapEvalAtRootsIs1: ∑ i ∈ Finset.range (2 ^ k), t1 ^ 2 ^ i = 1 ∧ ∑ i ∈ Finset.range (2 ^ k), t1⁻¹ ^ 2 ^ i = 1 := by
    exact prevBTResult.2.traceMapEvalAtRootsIs1

  have liftedPrevTraceMapEvalAtRootsIs1: ∑ i ∈ Finset.range (2 ^ k), (of prevPoly) t1 ^ 2 ^ i = 1 ∧ ∑ i ∈ Finset.range (2 ^ k), (of prevPoly t1)⁻¹ ^ 2 ^ i = 1 := by
    constructor
    · -- First part: sum of t1^(2^i)
      have h_coe: (of prevPoly) (∑ i ∈ Finset.range (2 ^ k), t1 ^ 2 ^ i) = 1 := by
        rw [prevTraceMapEvalAtRootsIs1.1, map_one]
      have h_map := map_sum (of prevPoly) (fun i => t1 ^ 2 ^ i) (Finset.range (2 ^ k))
      rw [h_map] at h_coe
      rw [Finset.sum_congr rfl (fun i hi => by
        rw [map_pow (f := of prevPoly) (a := t1) (n := 2 ^ i)]
      )] at h_coe
      exact h_coe
    · -- Second part: sum of (t1⁻¹)^(2^i)
      have h_coe: (of prevPoly) (∑ i ∈ Finset.range (2 ^ k), t1⁻¹ ^ 2 ^ i) = 1 := by
        rw [prevTraceMapEvalAtRootsIs1.2, map_one]
      have h_map := map_sum (of prevPoly) (fun i => t1⁻¹ ^ 2 ^ i) (Finset.range (2 ^ k))
      rw [h_map] at h_coe
      rw [Finset.sum_congr rfl (fun i hi => by
        rw [map_pow (f := of prevPoly) (a := t1⁻¹) (n := 2 ^ i)]
      )] at h_coe
      rw [Finset.sum_congr rfl (fun i hi => by -- map_inv₀ here
        rw [map_inv₀ (f := of prevPoly) (a := t1)]
      )] at h_coe
      exact h_coe

  have h_prev_pow_card_sub_one: ∀ (x: prevBTField) (hx: x ≠ 0), x^(2^(2^k)-1) = 1 := by
    intro x hx
    calc
      x^(2^(2^k)-1) = x^(Fintype.card prevBTField - 1) := by rw [prevBTResult.2.fieldFintypeCard]
      _ = 1 := by exact FiniteField.pow_card_sub_one_eq_one (a:=x) (ha:=hx)
  have h_lifted_prev_pow_card_sub_one: ∀ (x: prevBTField) (hx: x ≠ 0), (of prevPoly) x^(2^(2^k)-1) = 1 := by
    intro x hx
    have h1: x^(2^(2^k)-1) = 1 := h_prev_pow_card_sub_one x hx
    have h_coe: (of prevPoly) (x^(2^(2^k)-1)) = 1 := by rw [h1]; rfl
    rw [map_pow (f := of prevPoly) (a := x) (n := 2^(2^k)-1)] at h_coe
    exact h_coe

  have h_t1_pow: (of prevPoly) t1^(2^(2^k)-1) = 1 ∧ (of prevPoly t1)⁻¹^(2^(2^k)-1) = 1 := by
    constructor
    · rw [h_lifted_prev_pow_card_sub_one t1 t1_ne_zero_in_prevBTField]
    · have t1_inv_ne_zero: t1⁻¹ ≠ 0 := by
        intro h
        rw [inv_eq_zero] at h
        contradiction
      rw [←h_lifted_prev_pow_card_sub_one t1⁻¹ t1_inv_ne_zero]
      rw [map_inv₀ (f := of prevPoly) (a := t1)]

  have galoisAutomorphism: u^(2^(2^k)) = u⁻¹ ∧ (u⁻¹)^(2^(2^k)) = u := by
    exact galois_automorphism_power (u:=u) (t1:=t1) (k:=k) (sumZeroIffEq:=sumZeroIffEq) (specialElementNeZero:=specialElementNeZero) (prevSpecialElementNeZero:=prevSpecialElementNeZero) (u_plus_inv_eq_t1:=u_plus_u1_eq_t1) (h_u_square:=h_u_square) (h_t1_pow:=h_t1_pow) (trace_map_roots:=liftedPrevTraceMapEvalAtRootsIs1)

  have traceMapEvalAtRootsIs1 : (∑ i  ∈ Finset.range (2^(k+1)), u^(2^i)) = 1 ∧ (∑ i  ∈ Finset.range (2^(k+1)), (u⁻¹)^(2^i)) = 1 := by
    constructor
    ·
      have res := lifted_trace_map_eval_at_roots_prev_BTField (u:=u) (t1:=t1) (k:=k) (sumZeroIffEq:=sumZeroIffEq) (u_plus_inv_eq_t1:=u_plus_u1_eq_t1) (galois_automorphism:=galoisAutomorphism) (trace_map_at_prev_root:=liftedPrevTraceMapEvalAtRootsIs1.1)
      exact res
    ·
      have u1_plus_u11_eq_t1: u⁻¹ + u⁻¹⁻¹ = (of prevPoly) t1 := by
        rw [←u_plus_u1_eq_t1]
        rw [←u_is_inv_of_u1]
        rw [add_comm]
      have galoisAutomorphismRev: (u⁻¹)^(2^(2^k)) = u⁻¹⁻¹ ∧ (u⁻¹⁻¹)^(2^(2^k)) = u⁻¹ := by
        rw [←u_is_inv_of_u1]
        exact ⟨galoisAutomorphism.2, galoisAutomorphism.1⟩
      have res := lifted_trace_map_eval_at_roots_prev_BTField (u:=u⁻¹) (t1:=t1) (k:=k) (sumZeroIffEq:=sumZeroIffEq) (u_plus_inv_eq_t1:=u1_plus_u11_eq_t1) (galois_automorphism:=galoisAutomorphismRev) (trace_map_at_prev_root:=liftedPrevTraceMapEvalAtRootsIs1.1)
      exact res

  let instIrreduciblePoly : Irreducible newPoly := by
    by_contra h_not_irreducible
    -- ¬Irreducible p ↔ ∃ c₁ c₂, p.coeff 0 = c₁ * c₂ ∧ p.coeff 1 = c₁ + c₂
    -- Step 1: set up 4 equations
      -- c1 = au + b, c2 = cu + d (Lemma)
      -- c1 + c2 = u
      -- u^2 + t1 * u + 1 = 0
      -- c1 * c2 = 1

    obtain ⟨c1, c2, h_mul, h_add⟩ :=
      (Monic.not_irreducible_iff_exists_add_mul_eq_coeff
        newPolyIsMonic polyInstances.nat_deg_poly_is_2).mp h_not_irreducible
    rw [polyInstances.coeffOfX_0] at h_mul
    rw [polyInstances.coeffOfX_1] at h_add
    rw [←coeffOfX_1, coeffOfX_1] at h_add -- u = c1 + c2
    rw [←coeffOfX_0, coeffOfX_0] at h_mul -- (1: curBTField) = c1 * c2

    have c1_linear_form : ∃! p : prevBTField × prevBTField, c1 = (of prevPoly) p.1 * u + (of prevPoly) p.2 := by
      exact unique_linear_form_of_elements_in_curBTField c1
    have ⟨⟨a, b⟩, c1_eq⟩ := c1_linear_form -- (c1: curBTField) = (of prevPoly) a * u + (of prevPoly) b
    have c2_linear_form : ∃! p : prevBTField × prevBTField, c2 = (of prevPoly) p.1 * u + (of prevPoly) p.2 := by
      exact unique_linear_form_of_elements_in_curBTField c2
    have ⟨⟨c, d⟩, c2_eq⟩ := c2_linear_form -- (c2: curBTField) = (of prevPoly) c * u + (of prevPoly) d
    set ofa: curBTField := (of prevPoly) a
    set ofb: curBTField := (of prevPoly) b
    set ofc: curBTField := (of prevPoly) c
    set ofd: curBTField := (of prevPoly) d

    have eq1 : c1 + c2 = u := h_add.symm -- c1 + c2 = u
    have eq1_with_coeffs := eq1
    rw [c1_eq.1, c2_eq.1] at eq1_with_coeffs
    have h_c1_square: c1^2 = c1 * u + 1 := by sorry

    -- Substitute linear forms into equation (1)
    have eq1_expanded : (of prevPoly) (a + c) * u + (of prevPoly) (b + d) = u := by
      calc
        (of prevPoly) (a + c) * u + (of prevPoly) (b + d) = (ofa + ofc) * u + (of prevPoly) (b + d) := by rw [map_add]
        _ = ofa * u + ofc * u + ofb + ofd := by rw [add_mul, map_add, ←add_assoc]
        _ = (ofa * u + ofc * u + ofb) + ofd := by rw [add_assoc]
        _ = (ofa * u + (ofc * u + ofb)) + ofd := by rw [←add_assoc]
        _ = (ofa * u + (ofb + ofc * u)) + ofd := by rw [add_comm (a := ofb) (b := ofc * u)]
        _ = (ofa * u + ofb) + (ofc * u + ofd) := by rw [add_assoc, add_assoc, add_assoc]
        _ = u := by exact eq1_with_coeffs

    have x_pow_card: ∀ (x: curBTField), x^(2^2^(k + 1)) = x := by
      intro x
      calc
        x^(2^2^(k + 1)) = x^(Fintype.card curBTField) := by rw [fieldFintypeCard]
        _ = x := by exact FiniteField.pow_card x

    have x_pow_exp_of_2_repr := pow_exp_of_2_repr_given_x_square_repr (sumZeroIffEq := sumZeroIffEq)

    have c1_pow_card_eq_c1:= x_pow_card c1 -- Fermat's little theorem
    have two_to_k_plus_1_ne_zero: 2^(k + 1) ≠ 0 := by norm_num
    have c1_pow_card_eq := x_pow_exp_of_2_repr (x:=c1) (z:=u) (h_z_non_zero:=specialElementNeZero) (h_x_square:=h_c1_square) (i:=2^(k+1))
    rw [c1_pow_card_eq_c1] at c1_pow_card_eq

    have h_1_le_fin_card: 1 ≤ Fintype.card curBTField := by
      rw [fieldFintypeCard] -- ⊢ 1 ≤ 2 ^ 2 ^ (k + 1)
      apply Nat.one_le_pow
      apply Nat.zero_lt_two
    let instDivisionRing: DivisionRing curBTField := inferInstance
    let instDivisionSemiring: DivisionSemiring curBTField := instDivisionRing.toDivisionSemiring
    let instGroupWithZero: GroupWithZero curBTField := instDivisionSemiring.toGroupWithZero

    have u_pow_card_sub_one: u^(2^2^(k+1) - 1) = 1 := by
      rw [←FiniteField.pow_card_sub_one_eq_one (a:=u) (ha:=specialElementNeZero)]
      rw [fieldFintypeCard]

    -- have t1_pow_prevBTField_card_sub_1_eq_1 : (of prevPoly) t1^(2^2^(k+1) - 1) = 1 := by
    --   calc
    --     (of prevPoly) t1^(2^2^(k+1) - 1) = (of prevPoly) t1^(2^2^(k+1)) * ((of prevPoly) t1)⁻¹ := by
    --       have two_ne_zero: 2 ≠ 0 := by norm_num
    --       have one_lt_two: 1 < 2 := by norm_num
    --       have one_lt_two_pow_k_plus_1: 1 < 2 ^ 2 ^ (k + 1) := Nat.one_lt_pow (hn := two_to_k_plus_1_ne_zero) (ha := one_lt_two) (n := 2^(k + 1))
    --       have one_le_two_pow_k_plus_1: 1 ≤ 2 ^ 2 ^ (k + 1) := Nat.le_of_lt one_lt_two_pow_k_plus_1
    --       -- lemma pow_sub₀ (a : G₀) (ha : a ≠ 0) (h : n ≤ m) : a ^ (m - n) = a ^ m * (a ^ n)⁻¹ := by
    --       rw [pow_sub₀ (a := (of prevPoly) t1) (ha := t1_ne_zero) (h := one_le_two_pow_k_plus_1)]
    --       rw [pow_one]
    --     _ = t1 * ((of prevPoly) t1)⁻¹ := by rw [x_pow_card ((of prevPoly) t1)]
    --     _ = 1 := by
    --       exact mul_inv_cancel₀ (h := t1_ne_zero)
    rw [u_pow_card_sub_one, mul_one] at c1_pow_card_eq -- u_pow_card_eq : u = u * 1 + ∑ j ∈ Finset.range (2 ^ (k + 1)), (of prevPoly) t1 ^ (2 ^ 2 ^ (k + 1) - 2 ^ (j + 1))
    set rsum := ∑ j ∈ Finset.Icc 1 (2 ^ (k + 1)), u ^ (2 ^ 2 ^ (k + 1) - 2 ^ j) with rsum_def
    have rsum_eq_zero: rsum = 0 := by
      have sum_eq_2: -c1 + c1 = -c1 + (c1 + rsum) := (add_right_inj (a := -c1)).mpr c1_pow_card_eq
      have sum_eq_3: 0 = -c1 + (c1 + rsum) := by
        rw [neg_add_cancel] at sum_eq_2
        exact sum_eq_2
      rw [←add_assoc, neg_add_cancel, zero_add] at sum_eq_3
      exact sum_eq_3.symm

    have c1_plus_inv_eq_t1: c1 + u⁻¹ = u := by sorry
    have rsum_eq_u: rsum = u := rsum_eq_t1_square_aux (c1:=c1) (u:=u) (k:=k) (sumZeroIffEq:=sumZeroIffEq) (x_pow_card:=x_pow_card) (u_ne_zero:=specialElementNeZero) (trace_map_at_prev_root:=traceMapEvalAtRootsIs1)

    have rsum_ne_zero: rsum ≠ 0 := by
      rw [rsum_eq_u]
      exact specialElementNeZero

    rw [rsum_eq_zero] at rsum_ne_zero
    contradiction

  let result: BinaryTowerResult curBTField (k + 1) := {
    vec := u ::ᵥ newElts,
    instMul := instMul,
    instField := instFieldAdjoinRootOfPoly,
    instNontrivial := inferInstance,
    newPoly := newPoly,
    instInh := instInh,
    instDomain := instDomain,
    isNotUnitPoly := instNotUnitPoly,
    instNoZeroDiv := instNoZeroDiv,
    instIrreduciblePoly := instIrreduciblePoly,
    sumZeroIffEq := sumZeroIffEq,
    specialElement := u,
    specialElementNeZero := specialElementNeZero,
    newPolyForm := polyInstances.poly_form,
    degNewPolyIs2 := polyInstances.deg_poly_is_2,
    newPolyIsMonic := newPolyIsMonic,
    instFintype := instFintype,
    fieldFintypeCard := fieldFintypeCard,
    traceMapEvalAtRootsIs1 := traceMapEvalAtRootsIs1
  }

  exact ⟨curBTField, result⟩

-- def BinaryTower (k : ℕ) : Σ' (F : Type _), BinaryTowerResult F k :=
def BinaryTowerAux (k : ℕ) (rec : ∀ m : ℕ, m < k → Σ' (F : Type _), BinaryTowerResult F m) :
    Σ' (F : Type _), BinaryTowerResult F k :=
  match k with
  | 0 =>
    let curBTField := GF(2)
    let newList : List.Vector (GF(2)) 1 := List.Vector.cons (1 : GF(2)) List.Vector.nil
    let specialElement : GF(2) := newList.1.headI
    let specialElementIs1: specialElement = 1 := by
      unfold specialElement
      rfl
    let specialElementNeZero: specialElement ≠ 0 := by
      rw [specialElementIs1]
      norm_num
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

    let sumZeroIffEq: ∀ (x y : GF(2)), x + y = 0 ↔ x = y := by
      intro x y
      constructor
      · -- (→) If x + y = 0, then x = y
        intro h_sum_zero
        -- Case analysis on x
        rcases GF_2_value_eq_zero_or_one x with x_zero | x_one
        · -- Case x = 0
          rcases GF_2_value_eq_zero_or_one y with y_zero | y_one
          · -- Case y = 0
            rw [x_zero, y_zero]
          · -- Case y = 1
            rw [x_zero, y_one] at h_sum_zero
            -- 0 + 1 = 0
            simp at h_sum_zero
        · -- Case x = 1
          rcases GF_2_value_eq_zero_or_one y with y_zero | y_one
          · -- Case y = 0
            rw [x_one, y_zero] at h_sum_zero
            -- 1 + 0 = 0
            simp at h_sum_zero
          · -- Case y = 1
            rw [x_one, y_one]
      · -- (←) If x = y, then x + y = 0
        intro h_eq
        rw [h_eq]
        -- In GF(2), x + x = 0 for any x
        rcases GF_2_value_eq_zero_or_one y with y_zero | y_one
        · rw [y_zero]
          simp
        · rw [y_one]
          exact GF_2_one_add_one_eq_zero
    let instFintype: Fintype (GF(2)) := GF_2_fintype
    let fieldFintypeCard: Fintype.card (GF(2)) = 2^(2^0) := by exact GF_2_card
    have traceMapEvalAtRootsIs1 : (∑ i in Finset.range (2^0), specialElement^(2^i)) = 1 ∧ (∑ i in Finset.range (2^0), (specialElement⁻¹)^(2^i)) = 1 := by
      constructor
      · -- Prove first part: (∑ i in Finset.range (2^0), specialElement^(2^i)) = 1
        rw [Nat.pow_zero] -- 2^0 = 1
        rw [Finset.range_one] -- range 1 = {0}
        rw [specialElementIs1] -- specialElement = 1
        norm_num
      · -- Prove second part: (∑ i in Finset.range (2^0), (specialElement⁻¹)^(2^i)) = 1
        rw [Nat.pow_zero] -- 2^0 = 1
        simp [Finset.range_one] -- range 1 = {0}
        exact specialElementIs1

    let result: BinaryTowerResult curBTField 0 :={
      vec := newList,
      instMul := inferInstance,
      instField := inferInstance,
      instNontrivial := instNontrivial,
      newPoly := newPoly,
      specialElement := specialElement,
      specialElementNeZero := specialElementNeZero,
      newPolyForm := polyInstances.poly_form,
      degNewPolyIs2 := polyInstances.deg_poly_is_2,
      newPolyIsMonic := newPolyIsMonic,
      instInh := inferInstance,
      instDomain := inferInstance,
      isNotUnitPoly := instNotUnitPoly,
      instNoZeroDiv := instNoZeroDiv,
      instIrreduciblePoly := instIrreduciblePoly,
      sumZeroIffEq := sumZeroIffEq,
      instFintype := instFintype,
      fieldFintypeCard := fieldFintypeCard,
      traceMapEvalAtRootsIs1 := traceMapEvalAtRootsIs1
    }

    ⟨ curBTField, result ⟩
  | k + 1 =>
    let prevBTResult := rec k (Nat.lt_succ_self k)
    let instPrevBTield := prevBTResult.2.instField
    binary_tower_inductive_step (k:=k) (prevBTField:=prevBTResult.fst) (prevBTResult:=prevBTResult)

namespace BinaryTower

-- @[simp]
-- def BTField (k : ℕ) := (BinaryTower k).1

-- @[simp]
-- instance BTFieldIsField (k : ℕ) : Field (BTField k) := (BinaryTower k).2.instField

-- @[simp]
-- instance CommRing (k : ℕ) : CommRing (BTField k) := Field.toCommRing

-- @[simp]
-- instance Inhabited (k : ℕ) : Inhabited (BTField k) := (BinaryTower k).2.instInh

-- @[simp]
-- def list (k : ℕ) : List.Vector (BTField k) (k + 1) := (BinaryTower k).2.vec

-- @[simp]
-- def poly (k : ℕ) : Polynomial (BTField k) := (BinaryTower k).2.newPoly

-- @[coe]
-- theorem field_eq_adjoinRoot_poly (k : ℕ) (k_pos : k > 0) : AdjoinRoot (poly (k - 1)) = BTField k := by
--   induction k with
--   | zero => absurd k_pos ; simp
--   | succ k _ => sorry

-- instance coe_field_adjoinRoot (k : ℕ) (k_pos : k > 0) : Coe (AdjoinRoot (poly (k - 1))) (BTField k) where
--   coe := Eq.mp (field_eq_adjoinRoot_poly k k_pos)

-- -- -- We call the special extension field elements Z_k
-- @[simp]
-- def Z (k : ℕ) : BTField k := (list k).1.headI

-- -- @[simp]
-- -- theorem Z_eq_adjointRoot_root (k : ℕ) (k_pos : k > 0) [HEq (AdjoinRoot (poly k)) (BTField k)] :
-- --     Z k = AdjoinRoot.root (poly k) := by
-- --   simp [Z, field_eq_adjoinRoot_poly k k_pos]

-- -- @[simp]
-- -- theorem list_nonempty (k : ℕ) : (BinaryTower k).2.1 ≠ [] :=
-- --   List.ne_nil_of_length_eq_add_one (list_length k)

-- instance polyIrreducible (n : ℕ) : Irreducible (poly n) := (BinaryTower n).2.instIrreduciblePoly

-- instance polyIrreducibleFact (n : ℕ) : Fact (Irreducible (poly n)) := ⟨polyIrreducible n⟩

-- -- Possible direction: define alternate definition of BTF as Quotient of MvPolynomial (Fin n) GF(2)
-- -- by the ideal generated by special field elements
-- -- What would this definition give us?

end BinaryTower

end

/- Concrete implementation of BTF uses BitVec -/

def ConcreteBinaryTower (k : ℕ) :=
  match k with
  | 0 => BitVec 1
  | k + 1 => BitVec (2 ^ (2 ^ (k - 1)))


-- Define all arithmetic operations



-- Define a field isomorphism
