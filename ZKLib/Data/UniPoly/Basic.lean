/-
Copyright (c) 2024 ZKLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import Mathlib.Algebra.Tropical.Basic
import Mathlib.RingTheory.Polynomial.Basic
import ZKLib.Data.Math.Operations

/-!
  # Computable Univariate Polynomials

  This file contains a computable datatype for univariate polynomial, `UniPoly R`. This is
  internally represented as an array of coefficients.
-/

open Polynomial

/-- A type analogous to `Polynomial` that supports computable operations. This defined to be a
  wrapper around `Array`.

For example the Array `#[1,2,3]` represents the polynomial `1 + 2x + 3x^2`. Two arrays may represent
the same polynomial via zero-padding, for example `#[1,2,3] = #[1,2,3,0,0,0,...]`.
 -/
@[reducible, inline, specialize]
def UniPoly (R : Type*) := Array R

namespace UniPoly

@[reducible]
def mk {R : Type*} (coeffs : Array R) : UniPoly R := coeffs

@[reducible]
def coeffs {R : Type*} (p : UniPoly R) : Array R := p

variable {R : Type*} [Ring R] [BEq R]
variable {Q : Type*} [Ring Q]

/-- The constant polynomial `C r`. -/
def C (r : R) : UniPoly R := #[r]

/-- The variable `X`. -/
def X : UniPoly R := #[0, 1]

/-- Return the index of the last non-zero coefficient of a `UniPoly` -/
def last_nonzero (p: UniPoly R) : Option (Fin p.size) :=
  p.findIdxRev? (· != 0)

/-- Remove leading zeroes from a `UniPoly`. Requires `BEq` to check if the coefficients are zero. -/
def trim (p : UniPoly R) : UniPoly R :=
  match p.last_nonzero with
  | none => #[]
  | some i => p.extract 0 (i.val + 1)

/-- Return the degree of a `UniPoly`. -/
def degree (p : UniPoly R) : Nat :=
  match p.last_nonzero with
  | none => 0
  | some i => i.val + 1

/-- Return the leading coefficient of a `UniPoly` as the last coefficient of the trimmed array,
or `0` if the trimmed array is empty. -/
def leadingCoeff (p : UniPoly R) : R := p.trim.getLastD 0

namespace Trim

-- characterize .last_nonzero
theorem last_nonzero_none [LawfulBEq R] {p : UniPoly R} :
  (∀ i, (hi : i < p.size) → p[i] = 0) → p.last_nonzero = none
:= by
  intro h
  apply Array.findIdxRev?_eq_none
  intros
  rw [bne_iff_ne, ne_eq, not_not]
  apply_assumption

theorem last_nonzero_some [LawfulBEq R] {p : UniPoly R} {i} (hi: i < p.size) (h: p[i] ≠ 0) :
  ∃ k, p.last_nonzero = some k
:= Array.findIdxRev?_eq_some ⟨i, hi, bne_iff_ne.mpr h⟩

theorem last_nonzero_spec [LawfulBEq R] {p : UniPoly R} {k} :
  p.last_nonzero = some k
  → p[k] ≠ 0 ∧ (∀ j, (hj : j < p.size) → j > k → p[j] = 0)
:= by
  intro (h : p.last_nonzero = some k)
  constructor
  · by_contra
    have h : p[k] != 0 := Array.findIdxRev?_def h
    rwa [‹p[k] = 0›, bne_self_eq_false, Bool.false_eq_true] at h
  · intro j hj j_gt_k
    have h : ¬(p[j] != 0) := Array.findIdxRev?_maximal h ⟨ j, hj ⟩ j_gt_k
    rwa [bne_iff_ne, ne_eq, not_not] at h

-- the property of `last_nonzero_spec` uniquely identifies an element,
-- and that allows us to prove the reverse as well
def last_nonzero_prop {p : UniPoly R} (k: Fin p.size) : Prop :=
  p[k] ≠ 0 ∧ (∀ j, (hj : j < p.size) → j > k → p[j] = 0)

lemma last_nonzero_unique {p : UniPoly Q} {k k' : Fin p.size} :
  last_nonzero_prop k → last_nonzero_prop k' → k = k'
:= by
  suffices weaker : ∀ k k', last_nonzero_prop k → last_nonzero_prop k' → k ≤ k' by
    intro h h'
    exact Fin.le_antisymm (weaker k k' h h') (weaker k' k h' h)
  intro k k' ⟨ h_nonzero, h ⟩ ⟨ h_nonzero', h' ⟩
  by_contra k_not_le
  have : p[k] = 0 := h' k k.is_lt (Nat.lt_of_not_ge k_not_le)
  contradiction

theorem last_nonzero_some_iff [LawfulBEq R]  {p : UniPoly R} {k} :
  p.last_nonzero = some k ↔ (p[k] ≠ 0 ∧ (∀ j, (hj : j < p.size) → j > k → p[j] = 0))
:= by
  constructor
  · apply last_nonzero_spec
  intro h_prop
  have ⟨ k', h_some'⟩ := last_nonzero_some k.is_lt h_prop.left
  have k_is_k' := last_nonzero_unique (last_nonzero_spec h_some') h_prop
  rwa [← k_is_k']

/-- eliminator for `p.last_nonzero`, e.g. use with the induction tactic as follows:
  ```
  induction p using last_none_zero_elim with
  | case1 p h_none h_all_zero => ...
  | case2 p k h_some h_nonzero h_max => ...
  ```
-/
theorem last_nonzero_induct [LawfulBEq R] {motive : UniPoly R → Prop}
  (case1 : ∀ p, p.last_nonzero = none → (∀ i, (hi : i < p.size) → p[i] = 0) → motive p)
  (case2 : ∀ p : UniPoly R, ∀ k : Fin p.size, p.last_nonzero = some k → p[k] ≠ 0 →
    (∀ j : ℕ, (hj : j < p.size) → j > k → p[j] = 0) → motive p)
  (p : UniPoly R) : motive p
:= by
  by_cases h : ∀ i, (hi : i < p.size) → p[i] = 0
  · exact case1 p (last_nonzero_none h) h
  · push_neg at h; rcases h with ⟨ i, hi, h ⟩
    obtain ⟨ k, h_some ⟩ := last_nonzero_some hi h
    have ⟨ h_nonzero, h_max ⟩ := last_nonzero_spec h_some
    exact case2 p k h_some h_nonzero h_max

/-- eliminator for `p.trim`; use with the induction tactic as follows:
  ```
  induction p using Trim.elim with
  | case1 p h_empty h_all_zero => ...
  | case2 p k h_extract h_nonzero h_max => ...
  ```
-/
theorem induct [LawfulBEq R] {motive : UniPoly R → Prop}
  (case1 : ∀ p, p.trim = #[] → (∀ i, (hi : i < p.size) → p[i] = 0) → motive p)
  (case2 : ∀ p : UniPoly R, ∀ k : Fin p.size, p.trim = p.extract 0 (k + 1)
    → p[k] ≠ 0 → (∀ j : ℕ, (hj : j < p.size) → j > k → p[j] = 0) → motive p)
  (p : UniPoly R) : motive p
:= by induction p using last_nonzero_induct with
  | case1 p h_none h_all_zero =>
    have h_empty : p.trim = #[] := by unfold trim; rw [h_none]
    exact case1 p h_empty h_all_zero
  | case2 p k h_some h_nonzero h_max =>
    have h_extract : p.trim = p.extract 0 (k + 1) := by unfold trim; rw [h_some]
    exact case2 p k h_extract h_nonzero h_max

/-- eliminator for `p.trim`; e.g. use for case distinction as follows:
  ```
  rcases (Trim.elim p) with ⟨ h_empty, h_all_zero ⟩ | ⟨ k, h_extract, h_nonzero, h_max ⟩
  ```
-/
theorem elim [LawfulBEq R] (p : UniPoly R) :
    (p.trim = #[] ∧  (∀ i, (hi : i < p.size) → p[i] = 0))
  ∨ (∃ k : Fin p.size,
        p.trim = p.extract 0 (k + 1)
      ∧ p[k] ≠ 0
      ∧ (∀ j : ℕ, (hj : j < p.size) → j > k → p[j] = 0))
:= by induction p using induct with
  | case1 p h_empty h_all_zero => left; exact ⟨h_empty, h_all_zero⟩
  | case2 p k h_extract h_nonzero h_max => right; exact ⟨k, h_extract, h_nonzero, h_max⟩

theorem size_eq_degree (p : UniPoly R) : p.trim.size = p.degree := by
  unfold trim degree
  match h : p.last_nonzero with
  | none => simp
  | some i => simp [Fin.is_lt, Nat.succ_le_of_lt]

theorem size_le_size (p : UniPoly R) : p.trim.size ≤ p.size := by
  unfold trim
  match h : p.last_nonzero with
  | none => simp
  | some i => simp [Array.size_extract]

theorem getD_eq_getElem_of_lt [LawfulBEq R] {p : UniPoly R} {i} (hi: i < p.size) :
  p.trim.getD i 0 = p[i] := by
  induction p using induct with
  | case1 p h_empty h_all_zero =>
    specialize h_all_zero i hi
    simp [h_empty, h_all_zero]
  | case2 p k h_extract h_nonzero h_max =>
    simp [h_extract]
    -- split between i > k and i <= k
    have h_size : k + 1 = (p.extract 0 (k + 1)).size := by
      simp [Array.size_extract]
      exact Nat.succ_le_of_lt k.is_lt
    rcases (Nat.lt_or_ge k i) with hik | hik
    · have hik' : i ≥ (p.extract 0 (k + 1)).size := by linarith
      rw [Array.getElem?_eq_none hik', Option.getD_none]
      exact h_max i hi hik |> Eq.symm
    · have hik' : i < (p.extract 0 (k + 1)).size := by linarith
      rw [Array.getElem?_eq_getElem hik', Option.getD_some, Array.getElem_extract]
      simp only [zero_add]

theorem getD_eq_getD [LawfulBEq R] (p : UniPoly R) (i : ℕ) :
  p.trim.getD i 0 = p.getD i 0 := by
  rcases (Nat.lt_or_ge i p.size) with hi | hi
  · rw [getD_eq_getElem_of_lt hi]
    simp [hi]
  · have hi' : i ≥ p.trim.size := by linarith [size_le_size p]
    simp [hi, hi']

lemma getD_eq_coeff_getElem {p : UniPoly Q} {i} (hp : i < p.size) :
  p.getD i 0 = p[i] := by
  simp [hp]

/-- Two polynomials are equivalent if they are the same after removing leading zeroes. -/
def equiv (p q : UniPoly R) : Prop :=
  ∀ i, p.getD i 0 = q.getD i 0

lemma getD_eq_zero {p : UniPoly Q} :
    (∀ i, (hi : i < p.size) → p[i] = 0) ↔ ∀ i, p.getD i 0 = 0
:= by
  constructor <;> intro h i
  · cases Nat.lt_or_ge i p.size <;> simp [h, *]
  · intro hi; specialize h i; simp [hi] at h; assumption

lemma eq_degree_of_equiv [LawfulBEq R] {p q : UniPoly R} : equiv p q → p.degree = q.degree := by
  unfold equiv degree
  intro h_equiv
  induction p using last_nonzero_induct with
  | case1 p h_none_p h_all_zero =>
    have h_zero_p : ∀ i, p.getD i 0 = 0 := getD_eq_zero.mp h_all_zero
    have h_zero_q : ∀ i, q.getD i 0 = 0 := by intro i; rw [← h_equiv, h_zero_p]
    have h_none_q : q.last_nonzero = none := last_nonzero_none (getD_eq_zero.mpr h_zero_q)
    rw [h_none_p, h_none_q]
  | case2 p k h_some_p h_nonzero_p h_max_p =>
    have h_equiv_k := h_equiv k
    have k_lt_q : k < q.size := by
      by_contra h_not_lt
      have h_ge := Nat.le_of_not_lt h_not_lt
      simp [h_ge] at h_equiv_k
      contradiction
    simp [k_lt_q] at h_equiv_k
    have h_nonzero_q : q[k.val] ≠ 0 := by rwa [← h_equiv_k]
    have h_max_q : ∀ j, (hj : j < q.size) → j > k → q[j] = 0 := by
      intro j hj j_gt_k
      have h_eq := h_equiv j
      simp [hj] at h_eq
      rw [← h_eq]
      rcases Nat.lt_or_ge j p.size with hj | hj
      · simp [hj, h_max_p j hj j_gt_k]
      · simp [hj]
    have h_some_q : q.last_nonzero = some ⟨ k, k_lt_q ⟩ :=
      last_nonzero_some_iff.mpr ⟨ h_nonzero_q, h_max_q ⟩
    rw [h_some_p, h_some_q]

theorem eq_of_equiv [LawfulBEq R] {p q : UniPoly R} : equiv p q → p.trim = q.trim := by
  unfold equiv
  intro h
  ext
  · rw [size_eq_degree, size_eq_degree]
    apply eq_degree_of_equiv h
  rw [← getD_eq_coeff_getElem, ← getD_eq_coeff_getElem]
  rw [getD_eq_getD, getD_eq_getD, h _]

theorem trim_equiv [LawfulBEq R] (p : UniPoly R) : equiv p.trim p := by
  apply getD_eq_getD

theorem trim_twice [LawfulBEq R] (p : UniPoly R) : p.trim.trim = p.trim := by
  apply eq_of_equiv
  apply trim_equiv

theorem canonical_empty : (UniPoly.mk #[]).trim = UniPoly.mk (R:=R) #[] := by
  have : (UniPoly.mk (R:=R) #[]).last_nonzero = none := by
    simp [last_nonzero];
    apply Array.findIdxRev?_emtpy_none
    rfl
  rw [trim, this]

theorem canonical_of_size_zero {p : UniPoly R} : p.size = 0 → p.trim = p := by
  intro h
  suffices h_empty : p = #[] by rw [h_empty]; exact canonical_empty
  exact Array.eq_empty_of_size_eq_zero h

theorem canonical_nonempty_iff [LawfulBEq R] {p : UniPoly R} (hp: p.size > 0) :
  p.trim = p ↔ p.last_nonzero = some ⟨ p.size - 1, Nat.pred_lt_self hp ⟩
:= by
  unfold trim
  induction p using last_nonzero_induct with
  | case1 p h_none h_all_zero =>
    simp [h_none]
    by_contra h_empty
    subst h_empty
    contradiction
  | case2 p k h_some h_nonzero h_max =>
    simp [h_some]
    constructor
    · intro h
      ext
      conv => rhs; congr; congr; rw [← h]
      have : k + 1 ≤ p.size := Nat.succ_le_of_lt k.is_lt
      simp [Array.size_extract, this]
    · intro h
      have : k + 1 = p.size := by rw [h]; exact Nat.succ_pred_eq_of_pos hp
      rw [this]
      exact Array.extract_all p

theorem last_nonzero_last_iff [LawfulBEq R] {p : UniPoly R} (hp: p.size > 0) :
  p.last_nonzero = some ⟨ p.size - 1, Nat.pred_lt_self hp ⟩ ↔ p.getLast hp ≠ 0
:= by
  induction p using last_nonzero_induct with
  | case1 => simp [Array.getLast, *]
  | case2 p k h_some h_nonzero h_max =>
    simp only [h_some, Option.some_inj, Array.getLast]
    constructor
    · intro h
      have : k = p.size - 1 := by rw [h]
      conv => lhs; congr; case i => rw [← this]
      assumption
    · intro h
      rcases Nat.lt_trichotomy k (p.size - 1) with h_lt | h_eq | h_gt
      · specialize h_max (p.size - 1) (Nat.pred_lt_self hp) h_lt
        contradiction
      · ext; assumption
      · have : k < p.size := k.is_lt
        have : k ≥ p.size := Nat.le_of_pred_lt h_gt
        linarith

theorem canonical_iff [LawfulBEq R] {p : UniPoly R} :
   p.trim = p ↔ ∀ hp : p.size > 0, p.getLast hp ≠ 0
:= by
  constructor
  · intro h hp
    rwa [← last_nonzero_last_iff hp, ← canonical_nonempty_iff hp]
  · rintro h
    rcases Nat.eq_zero_or_pos p.size with h_zero | hp
    · exact canonical_of_size_zero h_zero
    · rw [canonical_nonempty_iff hp, last_nonzero_last_iff hp]
      exact h hp

theorem non_zero_map [LawfulBEq R] (f : R → R) (hf : ∀ r, f r = 0 → r = 0) (p : UniPoly R) :
  let fp := UniPoly.mk (p.map f);
  p.trim = p → fp.trim = fp
:= by
  intro fp p_canon
  by_cases hp : p.size > 0
  -- positive case
  apply canonical_iff.mpr
  intro hfp
  have h_nonzero := canonical_iff.mp p_canon hp
  have : fp.getLast hfp = f (p.getLast hp) := by simp [Array.getLast, fp]
  rw [this]
  by_contra h_zero
  specialize hf (p.getLast hp) h_zero
  contradiction
  -- zero case
  have : p.size = 0 := by linarith
  have : fp.size = 0 := by simp [this, fp]
  apply canonical_of_size_zero this
end Trim

/-- canonical version of UniPoly -/
def UniPolyC (R : Type*) [BEq R] [Ring R] := { p : UniPoly R // p.trim = p }

@[ext] theorem UniPolyC.ext {p q : UniPolyC R} (h : p.val = q.val) : p = q := Subtype.eq h

instance : Inhabited (UniPolyC R) := ⟨#[], Trim.canonical_empty⟩

section Operations

variable {S : Type*}

-- p(x) = a_0 + a_1 x + a_2 x^2 + ... + a_n x^n

-- eval₂ f x p = f(a_0) + f(a_1) x + f(a_2) x^2 + ... + f(a_n) x^n

/-- Evaluates a `UniPoly` at a given value, using a ring homomorphism `f: R →+* S`. -/
def eval₂ [Semiring S] (f : R →+* S) (x : S) (p : UniPoly R) : S :=
  p.zipWithIndex.foldl (fun acc ⟨a, i⟩ => acc + f a * x ^ i) 0

/-- Evaluates a `UniPoly` at a given value. -/
def eval (x : R) (p : UniPoly R) : R :=
  p.eval₂ (RingHom.id R) x

/-- Addition of two `UniPoly`s. Defined as the pointwise sum of the underlying coefficient arrays
  (properly padded with zeroes). -/
def add_raw (p q : UniPoly R) : UniPoly R :=
  let ⟨p', q'⟩ := Array.matchSize p q 0
  .mk (Array.zipWith p' q' (· + ·) )

/-- Addition of two `UniPoly`s. -/
def add (p q : UniPoly R) : UniPoly R :=
  add_raw p q |> trim

/-- Scalar multiplication of `UniPoly` by an element of `R`. -/
def smul (r : R) (p : UniPoly R) : UniPoly R :=
  .mk (Array.map (fun a => r * a) p)

def nsmul_raw (n : ℕ) (p : UniPoly R) : UniPoly R :=
  .mk (Array.map (fun a => n * a) p)

/-- Scalar multiplication of `UniPoly` by a natural number. -/
def nsmul (n : ℕ) (p : UniPoly R) : UniPoly R :=
  nsmul_raw n p |> trim

/-- Negation of a `UniPoly`. -/
def neg (p : UniPoly R) : UniPoly R := p.map (fun a => -a)

/-- Subtraction of two `UniPoly`s. -/
def sub (p q : UniPoly R) : UniPoly R := p.add q.neg

/-- Multiplication of a `UniPoly` by `X ^ i`, i.e. pre-pending `i` zeroes to the
underlying array of coefficients. -/
def mulPowX (i : Nat) (p : UniPoly R) : UniPoly R := .mk (Array.replicate i 0 ++ p)

/-- Multiplication of a `UniPoly` by `X`, reduces to `mulPowX 1`. -/
@[reducible] def mulX (p : UniPoly R) : UniPoly R := p.mulPowX 1

/-- Multiplication of two `UniPoly`s, using the naive `O(n^2)` algorithm. -/
def mul (p q : UniPoly R) : UniPoly R :=
  p.zipWithIndex.foldl (fun acc ⟨a, i⟩ => acc.add <| (smul a q).mulPowX i) (C 0)

/-- Exponentiation of a `UniPoly` by a natural number `n` via repeated multiplication. -/
def pow (p : UniPoly R) (n : Nat) : UniPoly R := (mul p)^[n] (C 1)

-- TODO: define repeated squaring version of `pow`

instance : Zero (UniPoly R) := ⟨#[]⟩
instance : One (UniPoly R) := ⟨UniPoly.C 1⟩
instance : Add (UniPoly R) := ⟨UniPoly.add⟩
instance : SMul R (UniPoly R) := ⟨UniPoly.smul⟩
instance : SMul ℕ (UniPoly R) := ⟨nsmul⟩
instance : Neg (UniPoly R) := ⟨UniPoly.neg⟩
instance : Sub (UniPoly R) := ⟨UniPoly.sub⟩
instance : Mul (UniPoly R) := ⟨UniPoly.mul⟩
instance : Pow (UniPoly R) Nat := ⟨UniPoly.pow⟩
instance : NatCast (UniPoly R) := ⟨fun n => UniPoly.C (n : R)⟩
instance : IntCast (UniPoly R) := ⟨fun n => UniPoly.C (n : R)⟩

/-- Convert a `UniPoly` to a `Polynomial`. -/
noncomputable def toPoly (p : UniPoly R) : Polynomial R :=
  p.eval₂ Polynomial.C Polynomial.X

/-- Return a bound on the degree of a `UniPoly` as the size of the underlying array
(and `⊥` if the array is empty). -/
def degreeBound (p : UniPoly R) : WithBot Nat :=
  match p.size with
  | 0 => ⊥
  | .succ n => n

/-- Convert `degreeBound` to a natural number by sending `⊥` to `0`. -/
def natDegreeBound (p : UniPoly R) : Nat :=
  (degreeBound p).getD 0


/-- Check if a `UniPoly` is monic, i.e. its leading coefficient is 1. -/
def monic (p : UniPoly R) : Bool := p.leadingCoeff == 1

/-- Division and modulus of `p : UniPoly R` by a monic `q : UniPoly R`. -/
def divModByMonicAux [Field R] (p : UniPoly R) (q : UniPoly R) :
    UniPoly R × UniPoly R :=
  go (p.size - q.size) p q
where
  go : Nat → UniPoly R → UniPoly R → UniPoly R × UniPoly R
  | 0, p, _ => ⟨0, p⟩
  | n+1, p, q =>
      let k := p.size - q.size -- k should equal n, this is technically unneeded
      let q' := C p.leadingCoeff * (q * X.pow k)
      let p' := (p - q').trim
      let (e, f) := go n p' q
      -- p' = q * e + f
      -- Thus p = p' + q' = q * e + f + p.leadingCoeff * q * X^n
      -- = q * (e + p.leadingCoeff * X^n) + f
      ⟨e + C p.leadingCoeff * X^k, f⟩

/-- Division of `p : UniPoly R` by a monic `q : UniPoly R`. -/
def divByMonic [Field R] (p : UniPoly R) (q : UniPoly R) :
    UniPoly R :=
  (divModByMonicAux p q).1

/-- Modulus of `p : UniPoly R` by a monic `q : UniPoly R`. -/
def modByMonic [Field R] (p : UniPoly R) (q : UniPoly R) :
    UniPoly R :=
  (divModByMonicAux p q).2

/-- Division of two `UniPoly`s. -/
def div [Field R] (p q : UniPoly R) : UniPoly R :=
  (C (q.leadingCoeff)⁻¹ • p).divByMonic (C (q.leadingCoeff)⁻¹ * q)

/-- Modulus of two `UniPoly`s. -/
def mod [Field R] (p q : UniPoly R) : UniPoly R :=
  (C (q.leadingCoeff)⁻¹ • p).modByMonic (C (q.leadingCoeff)⁻¹ * q)

instance [Field R] : Div (UniPoly R) := ⟨UniPoly.div⟩
instance [Field R] : Mod (UniPoly R) := ⟨UniPoly.mod⟩

/-- Pseudo-division of a `UniPoly` by `X`, which shifts all non-constant coefficients
to the left by one. -/
def divX (p : UniPoly R) : UniPoly R := p.extract 1 p.size

variable (p q r : UniPoly R)

-- some helper lemmas to characterize p + q

lemma matchSize_size_eq {p q : UniPoly Q} :
  let (p', q') := Array.matchSize p q 0
  p'.size = q'.size := by
  show (List.rightpad _ _ _).length = (List.rightpad _ _ _).length
  rw [List.rightpad_length, List.rightpad_length]
  omega

lemma matchSize_size {p q : UniPoly Q} :
  let (p', _) := Array.matchSize p q 0
  p'.size = max p.size q.size := by
  show (List.rightpad _ _ _).length = max (List.length _) (List.length _)
  rw [List.rightpad_length]
  omega

lemma zipWith_size {R} {f : R → R → R} {a b : Array R} :
  a.size = b.size → (Array.zipWith a b f).size = a.size := by
  simp; omega

-- TODO we could generalize the next few lemmas to matchSize + zipWith f for any f

theorem add_size {p q : UniPoly Q} : (add_raw p q).size = max p.size q.size := by
  show (Array.zipWith _ _ _ ).size = max p.size q.size
  rw [zipWith_size matchSize_size_eq, matchSize_size]

theorem add_coeff {p q : UniPoly Q} {i: ℕ} (hi: i < (add_raw p q).size) :
  (add_raw p q)[i] = p.getD i 0 + q.getD i 0
:= by
  simp [add_raw]
  unfold List.matchSize
  repeat rw [List.rightpad_getElem_eq_getD]
  simp only [List.getD_eq_getElem?_getD, Array.getElem?_eq_toList]

theorem add_coeff? (p q : UniPoly Q) (i: ℕ) :
  (add_raw p q).getD i 0 = p.getD i 0 + q.getD i 0
:= by
  rcases (Nat.lt_or_ge i (add_raw p q).size) with h_lt | h_ge
  · rw [← add_coeff h_lt]; simp [h_lt]
  have h_lt' : i ≥ max p.size q.size := by rwa [← add_size]
  have h_p : i ≥ p.size := by omega
  have h_q : i ≥ q.size := by omega
  simp [h_ge, h_p, h_q]

lemma trim_add_trim [LawfulBEq R] (p q : UniPoly R) : p.trim + q = p + q := by
  apply Trim.eq_of_equiv
  intro i
  rw [add_coeff?, add_coeff?, Trim.getD_eq_getD]

-- algebra theorems about addition

omit [Ring Q] in
@[simp] theorem zero_def : (0 : UniPoly Q) = #[] := rfl

theorem add_comm : p + q = q + p := by
  apply congrArg trim
  ext
  · simp only [add_size]; omega
  · simp only [add_coeff]
    apply _root_.add_comm

def canonical (p : UniPoly R) := p.trim = p

theorem zero_canonical : (0 : UniPoly R).trim = 0 := Trim.canonical_empty

theorem zero_add (hp : p.canonical) : 0 + p = p := by
  rw (occs := .pos [2]) [← hp]
  apply congrArg trim
  ext <;> simp [add_size, add_coeff, *]

theorem add_zero (hp : p.canonical) : p + 0 = p := by
  rw [add_comm, zero_add p hp]

theorem add_assoc [LawfulBEq R] : p + q + r = p + (q + r) := by
  show (add_raw p q).trim + r = p + (add_raw q r).trim
  rw [trim_add_trim, add_comm p, trim_add_trim, add_comm _ p]
  apply congrArg trim
  ext i
  · simp only [add_size]; omega
  · simp only [add_coeff, add_coeff?]
    apply _root_.add_assoc

theorem nsmul_zero [LawfulBEq R] (p : UniPoly R) : nsmul 0 p = 0 := by
  suffices (nsmul_raw 0 p).last_nonzero = none by simp [nsmul, trim, *]
  apply Trim.last_nonzero_none
  intros; unfold nsmul_raw
  simp only [Nat.cast_zero, zero_mul, Array.getElem_map]

theorem nsmul_raw_succ (n : ℕ) (p : UniPoly Q) :
  nsmul_raw (n + 1) p = add_raw (nsmul_raw n p) p := by
  unfold nsmul_raw
  ext
  · simp [add_size]
  next i _ hi =>
    simp [add_size] at hi
    simp [add_coeff, hi]
    rw [_root_.add_mul (R:=Q) n 1 p[i], one_mul]

theorem nsmul_succ [LawfulBEq R] (n : ℕ) {p: UniPoly R} : nsmul (n + 1) p = nsmul n p + p := by
  unfold nsmul
  rw [trim_add_trim]
  apply congrArg trim
  apply nsmul_raw_succ

theorem neg_trim [LawfulBEq R] (p : UniPoly R) : p.trim = p → (-p).trim = -p := by
  apply Trim.non_zero_map
  simp

theorem neg_add_cancel [LawfulBEq R] (p : UniPoly R) : -p + p = 0 := by
  rw [← zero_canonical]
  apply Trim.eq_of_equiv; unfold Trim.equiv; intro i
  rw [add_coeff?]
  rcases (Nat.lt_or_ge i p.size) with hi | hi <;> simp [hi, Neg.neg, neg]

end Operations

namespace OperationsC
-- additive group on UniPolyC
variable {R : Type*} [Ring R] [BEq R] [LawfulBEq R]
variable (p q r : UniPolyC R)

instance : Add (UniPolyC R) where
  add p q := ⟨p.val + q.val, by apply Trim.trim_twice⟩

theorem add_comm : p + q = q + p := by
  apply UniPolyC.ext; apply UniPoly.add_comm

theorem add_assoc : p + q + r = p + (q + r) := by
  apply UniPolyC.ext; apply UniPoly.add_assoc

instance : Zero (UniPolyC R) := ⟨0, zero_canonical⟩

theorem zero_add : 0 + p = p := by
  apply UniPolyC.ext
  apply UniPoly.zero_add p.val p.prop

theorem add_zero : p + 0 = p := by
  apply UniPolyC.ext
  apply UniPoly.add_zero p.val p.prop

def nsmul (n : ℕ) (p : UniPolyC R) : UniPolyC R :=
  ⟨UniPoly.nsmul n p.val, by apply Trim.trim_twice⟩

theorem nsmul_zero : nsmul 0 p = 0 := by
  apply UniPolyC.ext; apply UniPoly.nsmul_zero

theorem nsmul_succ (n : ℕ) (p : UniPolyC R) : nsmul (n + 1) p = nsmul n p + p := by
  apply UniPolyC.ext; apply UniPoly.nsmul_succ

instance : Neg (UniPolyC R) where
  neg p := ⟨-p.val, neg_trim p.val p.prop⟩

instance : Sub (UniPolyC R) where
  sub p q := p + -q

theorem neg_add_cancel : -p + p = 0 := by
  apply UniPolyC.ext
  apply UniPoly.neg_add_cancel

instance [LawfulBEq R] : AddCommGroup (UniPolyC R) where
  add_assoc := add_assoc
  zero_add := zero_add
  add_zero := add_zero
  add_comm := add_comm
  neg_add_cancel := neg_add_cancel
  nsmul := nsmul -- TODO do we actually need this custom implementation?
  nsmul_zero := nsmul_zero
  nsmul_succ := nsmul_succ
  zsmul := zsmulRec -- TODO do we want a custom efficient implementation?

-- TODO: define `SemiRing` structure on `UniPolyC`

end OperationsC


section Equiv

/-- An equivalence relation `equiv` on `UniPoly`s where `p ~ q` iff one is a
zero-padding of the other. -/
def equiv (p q : UniPoly R) : Prop :=
  match p.matchSize q 0 with
  | (p', q') => p' = q'

/-- Reflexivity of the equivalence relation. -/
@[simp] theorem equiv_refl (p : UniPoly Q) : equiv p p :=
  by simp [equiv, List.matchSize]

/-- Symmetry of the equivalence relation. -/
@[simp] theorem equiv_symm {p q : UniPoly Q} : equiv p q → equiv q p :=
  fun h => by simp [equiv] at *; exact Eq.symm h

open List in
/-- Transitivity of the equivalence relation. -/
@[simp] theorem equiv_trans {p q r : UniPoly Q} : equiv p q → equiv q r → equiv p r :=
  fun hpq hqr => by
    simp_all [equiv, Array.matchSize]
    have hpq' := (List.matchSize_eq_iff_forall_eq p.toList q.toList 0).mp hpq
    have hqr' := (List.matchSize_eq_iff_forall_eq q.toList r.toList 0).mp hqr
    have hpr' : ∀ (i : Nat), p.toList.getD i 0 = r.toList.getD i 0 :=
      fun i => Eq.trans (hpq' i) (hqr' i)
    exact (List.matchSize_eq_iff_forall_eq p.toList r.toList 0).mpr hpr'

/-- The `UniPoly.equiv` is indeed an equivalence relation. -/
instance instEquivalenceEquiv : Equivalence (equiv (R := R)) where
  refl := equiv_refl
  symm := equiv_symm
  trans := equiv_trans

/-- The `Setoid` instance for `UniPoly R` induced by `UniPoly.equiv`. -/
instance instSetoidUniPoly: Setoid (UniPoly R) where
  r := equiv
  iseqv := instEquivalenceEquiv

/-- The quotient of `UniPoly R` by `UniPoly.equiv`. This will be shown to be equivalent to
  `Polynomial R`. -/
def QuotientUniPoly := Quotient (@instSetoidUniPoly R _)

-- TODO: show that operations on `UniPoly` descend to `QuotientUniPoly`



end Equiv

namespace Lagrange

-- unique polynomial of degree n that has nodes at ω^i for i = 0, 1, ..., n-1
def nodal {R : Type*} [Ring R] (n : ℕ) (ω : R) : UniPoly R := sorry
  -- .mk (Array.range n |>.map (fun i => ω^i))

/--
This function produces the polynomial which is of degree n and is equal to r i at ω^i for i = 0, 1,
..., n-1.
-/
def interpolate {R : Type*} [Ring R] (n : ℕ) (ω : R) (r : Vector R n) : UniPoly R := sorry
  -- .mk (Array.finRange n |>.map (fun i => r[i])) * nodal n ω

end Lagrange

end UniPoly

section Tropical
/-- This section courtesy of Junyan Xu -/

instance : LinearOrderedAddCommMonoidWithTop (OrderDual (WithBot ℕ)) where
  __ : LinearOrderedAddCommMonoid (OrderDual (WithBot ℕ)) := inferInstance
  __ : Top (OrderDual (WithBot ℕ)) := inferInstance
  le_top _ := bot_le (α := WithBot ℕ)
  top_add' x := WithBot.bot_add x


noncomputable instance (R) [Semiring R] : Semiring (Polynomial R × Tropical (OrderDual (WithBot ℕ)))
  := inferInstance

noncomputable instance (R) [CommSemiring R] : CommSemiring
    (Polynomial R × Tropical (OrderDual (WithBot ℕ))) := inferInstance


def TropicallyBoundPoly (R) [Semiring R] : Subsemiring
    (Polynomial R × Tropical (OrderDual (WithBot ℕ))) where
  carrier := {p | p.1.degree ≤ OrderDual.ofDual p.2.untrop}
  mul_mem' {p q} hp hq := (p.1.degree_mul_le q.1).trans (add_le_add hp hq)
  one_mem' := Polynomial.degree_one_le
  add_mem' {p q} hp hq := (p.1.degree_add_le q.1).trans (max_le_max hp hq)
  zero_mem' := Polynomial.degree_zero.le


noncomputable def UniPoly.toTropicallyBoundPolynomial {R : Type} [Ring R] (p : UniPoly R) :
    Polynomial R × Tropical (OrderDual (WithBot ℕ)) :=
  (UniPoly.toPoly p, Tropical.trop (OrderDual.toDual (UniPoly.degreeBound p)))

def degBound (b: WithBot ℕ) : ℕ := match b with
  | ⊥ => 0
  | some n => n + 1

def TropicallyBoundPolynomial.toUniPoly {R : Type} [Ring R]
    (p : Polynomial R × Tropical (OrderDual (WithBot ℕ))) : UniPoly R :=
  match p with
  | (p, n) => UniPoly.mk (Array.range (degBound n.untrop) |>.map (fun i => p.coeff i))

noncomputable def Equiv.UniPoly.TropicallyBoundPolynomial {R : Type} [BEq R] [Ring R] :
    UniPoly R ≃+* Polynomial R × Tropical (OrderDual (WithBot ℕ)) where
      toFun := UniPoly.toTropicallyBoundPolynomial
      invFun := TropicallyBoundPolynomial.toUniPoly
      left_inv := by sorry
      right_inv := by sorry
      map_mul' := by sorry
      map_add' := by sorry

end Tropical
