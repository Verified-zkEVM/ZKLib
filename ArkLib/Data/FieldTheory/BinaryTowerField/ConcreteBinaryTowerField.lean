/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen
-/

import ArkLib.Data.FieldTheory.BinaryTowerField.Basic
import ArkLib.Data.Math.DepCast

/-!
# Computable concrete binary tower fields

This file implements the concrete binary tower fields

## Main Definitions

- `ConcreteBinaryTower k`: the concrete binary tower fields of level k whose elements are reprensented via bit vectors of size 2^k

## TODOs
-- Prove Field properties for level k > 0
-- Prove isomorphism with the abstract binary tower fields and derive
--   theorems about multilinear basis

## References

- [Wie88] Doug Wiedemann. "An Iterated Quadratic Extension of GF(2)" In: The Fibonacci Quarterly
  26.4 (1988), pp. 290–295.

- [FP97] John L. Fan and Christof Paar. "On efficient inversion in tower fields of characteristic
  two". In: Proceedings of IEEE International Symposium on Information Theory. 1997.
-/

namespace ConcreteDefinition
open Polynomial

section BaseDefinitions

-- https://github.com/ingonyama-zk/smallfield-super-sumcheck/blob/sb/eq-optimized/src/tower_fields/binius.rs
def ConcreteBinaryTower : ℕ → Type := fun k => BitVec (2^k)

def bitVecToString (width : ℕ) (bv : BitVec width) : String :=
  Fin.foldl width (fun (s : String) (idx : Fin width) =>
    -- idx is the MSB-oriented loop index (0 to width-1)
    -- Fin.rev idx converts it to an LSB-oriented index
    s.push (if BitVec.getLsb' bv (Fin.rev idx) then '1' else '0')
  ) ""

def ConcreteBinaryTower.toBitString {k: ℕ} (bv: ConcreteBinaryTower k): String :=
  bitVecToString (2^k) (bv)

-- Helper: Bit width for ConcreteBinaryTower
def width (k : ℕ) : ℕ := 2^k

-- Convert Nat to ConcreteBinaryTower
def fromNat {k : ℕ} (n : Nat) : ConcreteBinaryTower k :=
  BitVec.ofNat (2^k) n

@[simp] theorem fromNat_toNat_eq_self {k : ℕ} (bv : BitVec (2^k)) :
  (fromNat (BitVec.toNat bv) : ConcreteBinaryTower k) = bv := by
  simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq, fromNat, ConcreteBinaryTower]

instance ConcreteBinaryTower.instDepCast_local : DepCast ℕ ConcreteBinaryTower where
  dcast h_k_eq term_k1 := BitVec.cast (congrArg (fun n => 2^n) h_k_eq) term_k1
  dcast_id := by
    intro k_idx; funext x
    simp only [id_eq, BitVec.cast, BitVec.ofNatLT_toNat]

theorem dcast_bitvec_zero_eq {l r: ℕ} (h_width_eq: l = r): dcast (h_width_eq) 0#(l) = 0#(r) := sorry

-- Zero element
def zero {k : ℕ} : ConcreteBinaryTower k := BitVec.zero (2^k)

-- One element
def one {k : ℕ} : ConcreteBinaryTower k := 1#(2^k)

instance instZeroConcreteBinaryTower (k : ℕ) : Zero (ConcreteBinaryTower k) where
  zero := zero
instance instOneConcreteBinaryTower (k : ℕ) : One (ConcreteBinaryTower k) where
  one := one

-- Generic OfNat instance for ConcreteBinaryTower
-- instance (k : ℕ) (n : Nat): OfNat (ConcreteBinaryTower k) n where
  -- ofNat := fromNat n

-- Special element Z_k for each level k
def Z (k : ℕ) : ConcreteBinaryTower k :=
  if k = 0 then one
  else BitVec.ofNat (2^k) (1 <<< 2^(k-1))
  -- fromNat (2^(2^(k-1)))
    -- For k > 0, Z_k is defined based on the irreducible polynomial
    -- TODO: Define Z_k properly for k > 0

-- Algebraic map from level k to level k+1
def algebraMap {k : ℕ} : ConcreteBinaryTower k → ConcreteBinaryTower (k+1) :=
  fun x => fromNat (BitVec.toNat x)

-- Define the irreducible polynomial for level k
noncomputable def definingPoly {k : ℕ} [Semiring (ConcreteBinaryTower k)] : Polynomial (ConcreteBinaryTower k) :=
  -- it depends on 'Polynomial.add'', and it does not have executable code
  X^2 + (C (Z k) * X + 1)

-- Basic operations
def add {k : ℕ} (x y : ConcreteBinaryTower k) : ConcreteBinaryTower k := BitVec.xor x y
def neg {k : ℕ} (x : ConcreteBinaryTower k) : ConcreteBinaryTower k := x

-- Type class instances
instance (k : ℕ) : HAdd (ConcreteBinaryTower k) (ConcreteBinaryTower k) (ConcreteBinaryTower k) where
  hAdd := add

-- Type class instances
instance (k : ℕ) : Add (ConcreteBinaryTower k) where
  add := add

-- instance (k: ℕ) : OfNat (ConcreteBinaryTower k) 0 where
  -- ofNat := zero
-- instance (k: ℕ) : OfNat (ConcreteBinaryTower k) 1 where
  -- ofNat := one

-- Basic lemmas for addition
lemma add_self_cancel {k : ℕ} (a : ConcreteBinaryTower k) : a + a = 0 := by
  exact BitVec.xor_self (x:=a)

lemma add_eq_zero_iff_eq {k : ℕ} (a b : ConcreteBinaryTower k) : a + b = 0 ↔ a = b := by
  exact BitVec.xor_eq_zero_iff

lemma add_assoc {k: ℕ}: ∀ (a b c : ConcreteBinaryTower k), a + b + c = a + (b + c) := by
  exact BitVec.xor_assoc

-- Addition is commutative
lemma add_comm {k : ℕ} (a b : ConcreteBinaryTower k) : a + b = b + a := by
  exact BitVec.xor_comm a b

-- Zero is identity
lemma zero_add {k : ℕ} (a : ConcreteBinaryTower k) : 0 + a = a := by
  exact BitVec.zero_xor (x:=a)

lemma add_zero {k : ℕ} (a : ConcreteBinaryTower k) : a + 0 = a := by
  exact BitVec.xor_zero (x:=a)

-- Negation is additive inverse (in char 2, neg = id)
lemma neg_add_cancel {k : ℕ} (a : ConcreteBinaryTower k) : neg a + a = 0 := by
  exact BitVec.xor_self (x:=a)

lemma if_self_rfl {α : Type*} [DecidableEq α] (a b : α) :
  (if a = b then b else a) = a := by
  by_cases h : a = b
  · rw [if_pos h, h]
  · rw [if_neg h]

-- Proof that Z_{k+1} is a root of the irreducible polynomial from level k
theorem Z_is_root {k : ℕ} [Semiring (ConcreteBinaryTower k)] [Semiring (ConcreteBinaryTower (k+1))]:
  let f : ConcreteBinaryTower k →+* ConcreteBinaryTower (k+1) := {
    toFun := algebraMap,
    map_zero' := by sorry,
    map_one' := by sorry,
    map_add' := by sorry,
    map_mul' := by sorry
  }
  eval₂ f (Z (k+1)) (definingPoly (k:=k)) = 0 := by
  sorry -- TODO: Prove that Z_{k+1}^2 + Z_{k+1} * Z_k + 1 = 0

-- Isomorphism between ConcreteBinaryTower 0 and GF(2)
-- Ensure GF(2) has decidable equality
noncomputable instance : DecidableEq (GF(2)) :=
  fun x y =>
    -- Use the isomorphism between GF(2) and ZMod 2
    let φ : GF(2) ≃ₐ[ZMod 2] ZMod 2 := GaloisField.equivZmodP 2
    -- ZMod 2 has decidable equality
    if h : φ x = φ y then
      isTrue (by
        -- φ is injective, so φ x = φ y implies x = y
        exact φ.injective h)
    else
      isFalse (by
        intro h_eq
        -- If x = y, then φ x = φ y
        apply h
        exact congrArg φ h_eq)

instance (k : ℕ) : DecidableEq (ConcreteBinaryTower k) :=
  fun x y =>
    let p := BitVec.toNat x = BitVec.toNat y
    let q := x = y
    let hp : Decidable p := Nat.decEq (BitVec.toNat x) (BitVec.toNat y)
    let h_iff_pq : p ↔ q := (BitVec.toNat_eq).symm -- p is (toNat x = toNat y), q is (x = y)
    match hp with
    | isTrue (proof_p : p) =>
      -- We have a proof of p (toNat x = toNat y). We need a proof of q (x = y).
      -- h_iff_pq.mp gives p → q. So, (h_iff_pq.mp proof_p) is a proof of q.
      isTrue (h_iff_pq.mp proof_p)
    | isFalse (nproof_p : ¬p) =>
      -- We have a proof of ¬p. We need a proof of ¬q (which is q → False).
      -- So, assume proof_q : q. We need to derive False.
      -- h_iff_pq.mpr gives q → p. So, (h_iff_pq.mpr proof_q) is a proof of p.
      -- This contradicts nproof_p.
      isFalse (fun (proof_q : q) => nproof_p (h_iff_pq.mpr proof_q))

noncomputable def toConcreteBTF0 : GF(2) → ConcreteBinaryTower 0 := --   it depends on 'instFieldGaloisField'
  fun x => if decide (x = 0) then zero else one

noncomputable def fromConcreteBTF0 : ConcreteBinaryTower 0 → (GF(2)) :=
  fun x => if decide (x = zero) then 0 else 1

lemma nsmul_succ {k : ℕ} (n : ℕ) (x : ConcreteBinaryTower k) :
  (if ↑n.succ % 2 = 0 then zero else x) = (if ↑n % 2 = 0 then zero else x) + x := by
  have h : ↑n.succ % 2 = (↑n % 2 + 1) % 2 := by
    simp [Nat.cast_succ]
  have zero_is_0: (zero: ConcreteBinaryTower k) = 0 := by rfl
  have h_n_mod_le: n % 2 < 2 := Nat.mod_lt n (by norm_num)
  match h_n_mod: n % 2 with
  | Nat.zero =>
    rw [h]
    have h1 : (n + 1) % 2 = 1 := by simp [Nat.add_mod, h_n_mod, zero_add]
    simp [h1]; rw [(add_zero x).symm]; rw [←add_assoc, ←add_comm];
    rw [zero_is_0];
    rw [zero_add];
    rw [add_zero]
  | Nat.succ x' => -- h_n_mod : n % 2 = x'.succ
    match x' with
    | Nat.zero => -- h_n_mod : n % 2 = Nat.zero.succ => h_n_mod automatically updates
      rw [h]
      have h_n_mod_eq_1 : n % 2 = 1 := by rw [h_n_mod]
      rw [h_n_mod_eq_1]
      have h1 : (1 + 1 : ℤ) % 2 = 0 := by norm_num
      simp [h1]
      rw [zero_is_0, add_self_cancel]
    | Nat.succ _ => -- h_n_mod : n % 2 = n✝.succ.succ
      have h_n_mod_ge_2 : n % 2 ≥ 2 := by
        rw [h_n_mod]
        apply Nat.le_add_left
      rw [h_n_mod] at h_n_mod_le
      linarith

lemma zsmul_succ {k : ℕ} (n : ℕ) (x : ConcreteBinaryTower k) :
  (if (↑n.succ: ℤ) % 2 = 0 then zero else x) = (if (↑n: ℤ) % 2 = 0 then zero else x) + x := by
  norm_cast
  exact nsmul_succ n x

lemma neg_mod_2_eq_0_iff_mod_2_eq_0 {n : ℤ} : (-n) % 2 = 0 ↔ n % 2 = 0 := by
  constructor
  · intro h
    apply Int.dvd_iff_emod_eq_zero.mp
    apply Int.dvd_neg.mp
    exact Int.dvd_iff_emod_eq_zero.mpr h
  · intro h
    apply Int.dvd_iff_emod_eq_zero.mp
    apply Int.dvd_neg.mpr
    exact Int.dvd_iff_emod_eq_zero.mpr h

-- Int.negSucc n = -(n+1)
lemma zsmul_neg' {k : ℕ} (n : ℕ) (a : ConcreteBinaryTower k) :
  (if ((Int.negSucc n):ℤ) % (2:ℤ) = (0:ℤ) then zero else a) = neg (if (↑n.succ: ℤ) % (2:ℤ) = (0:ℤ) then zero else a) :=
by
  have negSucc_eq_minus_of_n_plus_1: Int.negSucc n = -(n + 1) := by rfl
  rw [negSucc_eq_minus_of_n_plus_1]
  have n_succ_eq_n_plus_1: (↑n.succ: ℤ) = (↑n: ℤ) + 1 := by rfl
  rw [n_succ_eq_n_plus_1]
  -- Split on two cases of the `if ... else` statement
  by_cases h : (n + 1) % 2 = 0
  { -- h: (n + 1) % 2 = 0
    have n_succ_mod_2_eq_0: ((↑n: ℤ) + 1) % 2 = 0 := by norm_cast
    rw [n_succ_mod_2_eq_0]
    -- ⊢ (if -(↑n + 1) % 2 = 0 then zero else a) = neg (if 0 = 0 then zero else a)
    have neg_n_succ_mod_2_eq_0: (-((↑n: ℤ) + 1)) % 2 = 0 := by
      exact (neg_mod_2_eq_0_iff_mod_2_eq_0 (n:=((n: ℤ) + 1))).mpr n_succ_mod_2_eq_0
    -- ⊢ (if 0 = 0 then zero else a) = neg (if 0 = 0 then zero else a)
    rw [neg_n_succ_mod_2_eq_0]
    simp
    rfl
  }
  { -- h : ¬(n + 1) % 2 = 0
    push_neg at h -- h : (n + 1) % 2 ≠ 0
    have n_succ_mod_2_ne_1: ((↑n: ℤ) + 1) % 2 = 1 := by
      have h_mod : (n + 1) % 2 = 1 := by -- prove the ℕ-version of the hypothesis & use norm_cast
        have tmp := Nat.mod_two_eq_zero_or_one (n:=n+1)
        match tmp with
        | Or.inl h_mod_eq_0 =>
          rw [h_mod_eq_0]
          contradiction
        | Or.inr h_mod_eq_1 =>
          rw [h_mod_eq_1]
      norm_cast
    rw [n_succ_mod_2_ne_1]
    have neg_n_succ_mod_2_ne_0: (-((↑n: ℤ) + 1)) % 2 ≠ 0 := by
      by_contra h_eq_0
      have neg_succ_mod_2_eq_0: ((↑n: ℤ) + 1) % 2 = 0:= (neg_mod_2_eq_0_iff_mod_2_eq_0 (n:=((n: ℤ) + 1))).mp h_eq_0
      have neg_succ_mod_2_eq_0_nat: (n + 1) % 2 = 0 := by
        have : ↑((n + 1) % 2) = ((↑n : ℤ) + 1) % 2 := by norm_cast
        rw [neg_succ_mod_2_eq_0] at this
        apply Int.ofNat_eq_zero.mp -- simp [Int.ofNat_emod]
        exact this
      rw [neg_succ_mod_2_eq_0_nat] at h
      contradiction
    -- ⊢ (if -(↑n + 1) % 2 = 0 then zero else a) = neg (if 1 = 0 then zero else a)
    rw [if_neg one_ne_zero, neg]
    rw [if_neg neg_n_succ_mod_2_ne_0]
  }

instance (k : ℕ) : AddCommGroup (ConcreteBinaryTower k) where
  toZero := inferInstance
  neg := neg
  sub := fun x y => add x y
  add_assoc := add_assoc
  add_comm := add_comm
  zero_add := zero_add
  add_zero := add_zero
  nsmul := fun n x => if n % 2 = (0:ℕ) then zero else x
  zsmul := fun (n:ℤ) x => if n % 2 = 0 then zero else x  -- Changed to n : ℤ
  neg_add_cancel := neg_add_cancel
  nsmul_succ := nsmul_succ
  zsmul_succ' := fun n a => zsmul_succ n a
  add := add
  zsmul_neg' := zsmul_neg' (k := k)

lemma zero_is_0 {k: ℕ}: (zero (k:=k)) = (0: ConcreteBinaryTower k) := by rfl
lemma one_is_1 {k: ℕ}: (one (k:=k)) = 1 := by rfl
lemma concrete_one_ne_zero {k : ℕ} : (one (k:=k)) ≠ (zero (k:=k)) := by
  intro h_eq
  have h_toNat_eq : (one (k:=k)).toNat = (zero (k:=k)).toNat := congrArg BitVec.toNat h_eq
  simp [one, zero, BitVec.toNat_ofNat] at h_toNat_eq

instance {k: ℕ}: NeZero (1 : ConcreteBinaryTower k) := by
  unfold ConcreteBinaryTower
  exact {out := concrete_one_ne_zero (k:=k) }

lemma one_le_sub_middle_of_pow2 {k: ℕ} (h_k: 1 ≤ k): 1 ≤ 2 ^ k - 2 ^ (k - 1) := by
  have l1: 2 ^ (k - 1 + 1) = 2^k := by congr 1; omega
  have res := one_le_sub_consecutive_two_pow (n:=k-1)
  rw [l1] at res
  exact res

lemma sub_middle_of_pow2_with_one_canceled {k: ℕ} (h_k: 1 ≤ k): 2 ^ k - 1 - 2 ^ (k - 1) + 1 = 2 ^ (k - 1) := by
  calc 2 ^ k - 1 - 2 ^ (k - 1) + 1 = 2 ^ k - 2 ^ (k - 1) - 1 + 1 := by omega
    _ = 2 ^ k - 2 ^ (k - 1) := by rw [Nat.sub_add_cancel]; exact one_le_sub_middle_of_pow2 (h_k:=h_k)
    _ = 2^(k-1) * 2 - 2 ^ (k - 1):= by
      congr 1
      rw [← Nat.pow_succ]
      congr
      simp only [Nat.succ_eq_add_one]
      rw [Nat.sub_add_cancel]
      omega
    _ = 2^(k-1) + 2^(k-1) - 2^(k-1) := by rw [Nat.mul_two]
    _ = 2^(k-1) := Nat.add_sub_self_left (2 ^ (k - 1)) (2 ^ (k - 1))

-- Split a field element into high and low parts
def split {k : ℕ} (h : k > 0) (x : ConcreteBinaryTower k) :
    ConcreteBinaryTower (k - 1) × ConcreteBinaryTower (k - 1) :=
  let lo_bits: BitVec (2 ^ (k - 1) - 1 - 0 + 1) :=
    BitVec.extractLsb (hi := 2 ^ (k - 1) - 1) (lo := 0) x
  let hi_bits: BitVec (2 ^ k - 1 - 2 ^ (k - 1) + 1) :=
    BitVec.extractLsb (hi := 2 ^ k - 1) (lo := 2 ^ (k - 1)) x
  have h_lo: 2 ^ (k - 1) - 1 - 0 + 1 = 2 ^ (k - 1) := by
    calc 2 ^ (k - 1) - 1 - 0 + 1 = 2 ^ (k - 1) - 1 + 1 := by norm_num
      _ = 2^(k-1) := by rw [Nat.sub_add_cancel]; exact one_le_two_pow_n (n:=k-1)
  have h_hi := sub_middle_of_pow2_with_one_canceled (k:=k) (h_k:=by omega)
  -- Use cast to avoid overuse of fromNat & toNat
  let lo: BitVec (2^(k-1)) := dcast h_lo lo_bits
  let hi: BitVec (2^(k-1)) := dcast h_hi hi_bits
  (hi, lo)

def join {k : ℕ} (h_pos : k > 0)  (hi lo : ConcreteBinaryTower (k-1)) : ConcreteBinaryTower k :=
  BitVec.ofNat (2^k) ((hi.toNat <<< 2^(k-1)) ||| lo.toNat)

-- Option 3: Disable the precheck (not recommended for production code)
-- set_option quotPrecheck false
-- notation:90 a "ₕ[" h "]" => (split h a).1  -- High part with explicit proof
-- notation:90 a "ₗ[" h "]" => (split h a).2  -- Low part with explicit proof
-- notation:80 hi "⋈[" h "]" lo => join h hi lo  -- Join with explicit proof

theorem split_eq_iff {k : ℕ} (h_pos : k > 0) (x : ConcreteBinaryTower k)
  (hi_btf lo_btf : ConcreteBinaryTower (k - 1)):
  split h_pos x = (hi_btf, lo_btf) ↔
  (hi_btf = fromNat (k:=k-1) (x.toNat >>> 2^(k-1)) ∧
  lo_btf = fromNat (k:=k-1) (x.toNat &&& ((2^(k-1) - 1)))) := by sorry

theorem join_eq_iff {k: ℕ} (h_pos : k > 0) (x: ConcreteBinaryTower k)
  (hi_btf lo_btf : ConcreteBinaryTower (k-1)):
  x = join h_pos hi_btf lo_btf ↔
  (hi_btf = fromNat (k:=k-1) (x.toNat >>> 2^(k-1)) ∧
  lo_btf = fromNat (k:=k-1) (x.toNat &&& ((2^(k-1) - 1)))) := by sorry

theorem join_of_split {k : ℕ} (h_pos : k > 0) (x : ConcreteBinaryTower k)
    (hi_btf lo_btf : ConcreteBinaryTower (k - 1))
    (h_split_eq : split h_pos x = (hi_btf, lo_btf)):
    x = join h_pos hi_btf lo_btf := by
  have h_split := (split_eq_iff (k:=k) (h_pos:=h_pos) x hi_btf lo_btf).mp h_split_eq
  obtain ⟨h_hi, h_lo⟩ := h_split
  exact (join_eq_iff h_pos x hi_btf lo_btf).mpr ⟨h_hi, h_lo⟩

theorem split_of_join {k : ℕ} (h_pos : k > 0) (x : ConcreteBinaryTower k)
    (hi_btf lo_btf : ConcreteBinaryTower (k - 1))
    (h_join: x = join h_pos hi_btf lo_btf):
    (hi_btf, lo_btf) = split h_pos x := by
  have ⟨h_hi, h_lo⟩ := (join_eq_iff h_pos x hi_btf lo_btf).mp h_join
  exact ((split_eq_iff h_pos x hi_btf lo_btf).mpr ⟨h_hi, h_lo⟩).symm

theorem split_zero {k: ℕ} (h_pos: k > 0): split h_pos zero = (zero, zero) := by
  rw [split]
  simp only [zero, BitVec.zero_eq, BitVec.extractLsb_ofNat, Nat.zero_mod, Nat.zero_shiftRight,
    Nat.sub_zero, Nat.shiftRight_zero, Prod.mk.injEq, dcast_bitvec_zero_eq, and_self]
theorem split_one {k: ℕ} (h_pos: k > 0): split h_pos one = (zero, one) := by
  rw [split]
  simp only [zero, one, BitVec.zero_eq, BitVec.extractLsb_ofNat, Nat.zero_mod, Nat.zero_shiftRight,
    Nat.sub_zero, Nat.shiftRight_zero, Prod.mk.injEq, dcast_bitvec_zero_eq, and_self]
  sorry
theorem join_zero {k: ℕ} (h_pos: k > 0): join h_pos zero zero = zero := by sorry
theorem join_one {k: ℕ} (h_pos: k > 0): join h_pos zero one = one := by sorry

def equivProd {k : ℕ} (h_k_pos : k > 0) :
  ConcreteBinaryTower k ≃ ConcreteBinaryTower (k - 1) × ConcreteBinaryTower (k - 1) where
  toFun := split h_k_pos
  invFun := λ (hi, lo) => join h_k_pos hi lo
  left_inv := λ x => Eq.symm (join_of_split h_k_pos x _ _ rfl)
  right_inv := λ ⟨hi, lo⟩ => Eq.symm (split_of_join h_k_pos _ hi lo rfl)

lemma mul_trans_inequality {k : ℕ} (x: ℕ) (h_k: k ≤ 2) (h_x: x ≤ 2^(2^k) - 1): x < 16 := by
  have x_le_1: x ≤ 2^(2^k) - 1 := by omega
  have x_le_2: x ≤ 2^(2^2) - 1 := by
    apply le_trans x_le_1 -- 2^(2^k) - 1 ≤ 2^(2^2) - 1
    rw [Nat.sub_le_sub_iff_right]
    rw [Nat.pow_le_pow_iff_right, Nat.pow_le_pow_iff_right]
    exact h_k
    norm_num
    norm_num
    norm_num
  have x_le_15: x ≤ 15 := by omega
  have x_lt_16: x < 16 := by omega
  exact x_lt_16

#eval add (fromNat (k:=9) 1) (fromNat (k:=9) 7) -- -- 000001 xor 001101 = 001100 = 6#512
#eval (fromNat (k:=9) 1) + (fromNat (k:=9) 7)

-- Helper: Convert coefficients back to BitVec
def coeffsToBitVec {n : ℕ} (coeffs : List (ZMod 2)) : BitVec n :=
  let val := List.foldr (fun c acc => acc * 2 + c.val) 0 (coeffs.take n)
  BitVec.ofNat n val

-- Karatsuba-like multiplication for binary tower fields
def concrete_mul {k : ℕ} (a b : ConcreteBinaryTower k) : ConcreteBinaryTower k :=
  if h_k_zero: k = 0 then
    if a = zero then zero
    else if b = zero then zero
    else if a = one then b
    else if b = one then a
    else zero -- This case never happens in GF(2)
  else
    have h_k_gt_0 : k > 0 := by omega
    let (a₁, a₀) := split h_k_gt_0 a -- (hi, lo)
    let (b₁, b₀) := split h_k_gt_0 b
    let a_sum := a₁ + a₀
    let b_sum := b₁ + b₀
    let sum_mul := concrete_mul a_sum b_sum
    let prevX := Z (k - 1)
    -- Karatsuba-like step
    let mult_hi := concrete_mul a₁ b₁  -- Recursive call at k-1
    let mult_lo := concrete_mul a₀ b₀  -- Recursive call at k-1
    let lo_res := mult_lo + mult_hi -- a₀b₀ + a₁b₁
    let hi_res := sum_mul + lo_res + (concrete_mul mult_hi prevX)
    have h_eq : k - 1 + 1 = k := by omega
    -- Use the proof to cast the type
    have res := join (k:=k) (by omega) hi_res lo_res
    res
termination_by (k, a.toNat, b.toNat)

-- Multiplication instance
instance (k : ℕ) : HMul (ConcreteBinaryTower k) (ConcreteBinaryTower k) (ConcreteBinaryTower k) where
  hMul := concrete_mul

#eval bitVecToString 5 (BitVec.ofNat 5 1)  -- 5 in 4 bits is 0101
#eval split (k:=5) (by omega) (fromNat (k:=5) 1) -- 1 => (0, 1)
#eval (Z 2).toBitString -- 01|00
#eval (one (k:=2)).toBitString -- 0001
#eval (zero (k:=2)).toBitString -- 0000

#eval (fromNat (k:=2) 3).toBitString
#eval (fromNat (k:=3) 3).toBitString
#eval (fromNat (k:=4) 3).toBitString

#eval Z (0)
#eval Z (1)
#eval Z (2)
#eval Z (3)
#eval Z (4)
#eval Z (5)
#eval Z (6)

#eval (fromNat (k:=1) 3) * (fromNat (k:=1) 3) -- 9#4
#eval (fromNat (k:=4) 3) * (fromNat (k:=4) 3) -- 9#4
#eval (fromNat (k:=2) 3) * (fromNat (k:=2) 3) -- 9#4
#eval (fromNat (k:=5) 7) * (fromNat (k:=5) 20) -- 9#4

-- Test function to bundle multiple evaluations
def runTests : IO Unit := do
  -- Test k = 0 (field of order 2, like GF(2))
  let k0 : ℕ := 0
  let zero0 := zero (k := k0)
  let one0 := one (k := k0)
  let five0 := fromNat (k := k0) 5  -- 5 mod 2 = 1 in k=0
  IO.println s!"--- Tests for k = {k0} (width = {width k0}) ---"
  IO.println s!"zero = {zero0.toBitString}"
  IO.println s!"one = {one0.toBitString}"
  IO.println s!"fromNat 5 = {five0.toBitString}"
  IO.println s!"zero + one = {(add zero0 one0).toBitString}"
  IO.println s!"one + one = {(add one0 one0).toBitString}"
  IO.println s!"one * one = {(concrete_mul one0 one0).toBitString}"
  IO.println s!"zero * one = {(concrete_mul zero0 one0).toBitString}"

  -- Test k = 1 (field of order 4, like GF(4))
  let k1 : ℕ := 1
  let zero1 := zero (k := k1)
  let one1 := one (k := k1)
  let two1 := fromNat (k := k1) 2
  let three1 := fromNat (k := k1) 3
  IO.println s!"--- Tests for k = {k1} (width = {width k1}) ---"
  IO.println s!"zero = {zero1.toBitString}"
  IO.println s!"one = {one1.toBitString}"
  IO.println s!"fromNat 2 = {two1.toBitString}"
  IO.println s!"fromNat 3 = {three1.toBitString}"
  IO.println s!"one + two = {(add one1 two1).toBitString}"
  IO.println s!"two + three = {(add two1 three1).toBitString}"
  IO.println s!"one * two = {(concrete_mul one1 two1).toBitString}"
  IO.println s!"two * three = {(concrete_mul two1 three1).toBitString}"

  -- Test k = 2 (field of order 16, like GF(16))
  let k2 : ℕ := 2
  let zero2 := zero (k := k2)
  let one2 := one (k := k2)
  let five2 := fromNat (k := k2) 5
  let seven2 := fromNat (k := k2) 7
  IO.println s!"--- Tests for k = {k2} (width = {width k2}) ---"
  IO.println s!"zero = {zero2.toBitString}"
  IO.println s!"one = {one2.toBitString}"
  IO.println s!"fromNat 5 = {five2.toBitString}"
  IO.println s!"fromNat 7 = {seven2.toBitString}"
  IO.println s!"five + seven = {(add five2 seven2).toBitString}"
  IO.println s!"five * one = {(concrete_mul five2 one2).toBitString}"
  IO.println s!"five * seven = {(concrete_mul five2 seven2).toBitString}"

-- Run the tests
#eval runTests

instance (k : ℕ) : LT (ConcreteBinaryTower k) where
  lt := fun x y => by
    unfold ConcreteBinaryTower at x y
    exact x < y

instance (k : ℕ) : LE (ConcreteBinaryTower k) where
  le := fun x y => by
    unfold ConcreteBinaryTower at x y
    exact x ≤ y

instance (k: ℕ) : Preorder (ConcreteBinaryTower k) where
  le_refl := fun x => BitVec.le_refl x
  le_trans := fun x y z hxy hyz => BitVec.le_trans hxy hyz
  lt := fun x y => x < y
  lt_iff_le_not_le := fun x y => by
    unfold ConcreteBinaryTower at x y
    have bitvec_statement := (BitVec.not_lt_iff_le : ¬x < y ↔ y ≤ x)
    -- We need to prove: x < y ↔ x ≤ y ∧ ¬y ≤ x
    constructor
    · -- Forward direction: x < y → x ≤ y ∧ ¬y ≤ x
      intro h_lt
      constructor
      · -- x < y → x ≤ y
        exact BitVec.le_of_lt h_lt
      · -- x < y → ¬y ≤ x
        intro h_le_yx
        have h_not_le := mt bitvec_statement.mpr
        push_neg at h_not_le
        have neg_y_le_x := h_not_le h_lt
        contradiction
    · -- Reverse direction: x ≤ y ∧ ¬y ≤ x → x < y
      intro h
      cases h with | intro h_le_xy h_not_le_yx =>
      have x_lt_y:= mt bitvec_statement.mp h_not_le_yx
      push_neg at x_lt_y
      exact x_lt_y

theorem toNatInRange {k: ℕ} (b: ConcreteBinaryTower k) : BitVec.toNat b ≤ 2 ^ (2 ^ k) - 1 := by
  unfold ConcreteBinaryTower at b
  have le_symm: 2^k ≤ 2^k := by omega
  have toNat_le_2pow:= BitVec.toNat_lt_twoPow_of_le (m:=2^k) (n:=(2^k))
  have b_le := toNat_le_2pow le_symm (x:=b)
  omega

theorem eq_zero_or_eq_one {a : ConcreteBinaryTower 0} : a = zero ∨ a = one := by
  unfold ConcreteBinaryTower at a -- Now a is a BitVec (2^0) = BitVec 1
  have h := BitVec.eq_zero_or_eq_one a
  cases h with
  | inl h_zero =>
    left
    unfold zero
    exact h_zero
  | inr h_one =>
    right
    unfold one
    exact h_one

lemma add_eq_one_iff (a b : ConcreteBinaryTower 0) : a + b = 1 ↔ (a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 0) := by
  rcases eq_zero_or_eq_one (a := a) with (ha | ha)
  · simp [ha, concrete_mul, add_self_cancel, zero_is_0]  -- a = zero
  · simp [ha, one_is_1]

theorem concreteBTF0_isomorphic_GF2 :
  Function.Bijective toConcreteBTF0 ∧
  (∀ x y, toConcreteBTF0 (x + y) = toConcreteBTF0 x + toConcreteBTF0 y) ∧
  (∀ x y, toConcreteBTF0 (x * y) = concrete_mul (toConcreteBTF0 x) (toConcreteBTF0 y)) := by
  sorry -- TODO: Prove isomorphism

def concrete_pow_nat {k: ℕ} (x : ConcreteBinaryTower k) (n : ℕ) : ConcreteBinaryTower k :=
  if n = 0 then one
  else if n % 2 = 0 then concrete_pow_nat (concrete_mul x x) (n / 2)
  else concrete_mul x (concrete_pow_nat (concrete_mul x x) (n / 2))

-- Multiplicative inverse
def concrete_inv {k : ℕ} (a : ConcreteBinaryTower k) : ConcreteBinaryTower k :=
  if a = zero then zero else
    concrete_pow_nat a (2^(2^k) - 2)
termination_by concrete_pow_nat x n => n

lemma concrete_exists_pair_ne {k:ℕ}: ∃ x y : ConcreteBinaryTower k, x ≠ y :=
  ⟨zero (k:=k), one (k:=k), (concrete_one_ne_zero (k:=k)).symm⟩

lemma concrete_zero_mul0 (b : ConcreteBinaryTower 0) :
  concrete_mul (zero (k:=0)) b = zero (k:=0) := by
  unfold concrete_mul
  simp only [↓reduceDIte, zero, Nat.pow_zero, BitVec.zero_eq, ↓reduceIte]

lemma concrete_mul_zero0 (a : ConcreteBinaryTower 0) :
  concrete_mul a (zero (k:=0)) = zero (k:=0) := by
  unfold concrete_mul
  by_cases h : a = zero
  · simp only [↓reduceDIte, h, ↓reduceIte]
  · simp only [↓reduceDIte, zero, Nat.pow_zero, BitVec.zero_eq, ↓reduceIte, ite_self]

lemma concrete_one_mul0 (a : ConcreteBinaryTower 0) :
  concrete_mul (one (k:=0)) a = a := by
  unfold concrete_mul
  by_cases h : a = zero
  · simp [h, zero]
  · norm_num; simp only [concrete_one_ne_zero, ↓reduceIte, h]

lemma concrete_mul_one0 (a : ConcreteBinaryTower 0) :
  concrete_mul a (one (k:=0)) = a := by
  unfold concrete_mul
  by_cases h : a = zero
  · simp [h]
  · norm_num; simp [h, concrete_one_ne_zero]; intro h_eq; exact h_eq.symm

lemma concrete_mul_assoc0 (a b c : ConcreteBinaryTower 0) :
  concrete_mul (concrete_mul a b) c = concrete_mul a (concrete_mul b c) := by
  rcases eq_zero_or_eq_one (a := a) with (ha | ha)
  · simp [ha, concrete_mul]  -- a = zero case
  · rcases eq_zero_or_eq_one (a := b) with (hb | hb)
    · simp [ha, hb, concrete_mul]  -- a = one, b = zero
    · rcases eq_zero_or_eq_one (a := c) with (hc | hc)
      · simp [ha, hb, hc, concrete_mul]  -- a = one, b = one, c = zero
      · simp [ha, hb, hc, concrete_mul, concrete_one_ne_zero]  -- a = one, b = one, c = one

lemma concrete_mul_comm0 (a b : ConcreteBinaryTower 0) :
  concrete_mul a b = concrete_mul b a := by
  rcases eq_zero_or_eq_one (a := a) with (ha | ha)
  · simp [ha, concrete_mul]  -- a = zero
  · rcases eq_zero_or_eq_one (a := b) with (hb | hb)
    · simp [ha, hb, concrete_mul]  -- a = one, b = zero
    · simp [ha, hb, concrete_mul]  -- a = one, b = one

-- Helper lemma: For GF(2), `if x = 0 then 0 else x` is just `x`.
lemma if_zero_then_zero_else_self (x : ConcreteBinaryTower 0) : (if x = zero then zero else x) = x := by
  rcases eq_zero_or_eq_one (a := x) with (hx_zero | hx_one)
  · simp only [hx_zero, ↓reduceIte]
  · simp only [hx_one, concrete_one_ne_zero, ↓reduceIte] -- Goal: `(if 1 = 0 then 0 else 1) = 1`, which simplifies to `1 = 1`.

lemma concrete_mul_left_distrib0 (a b c : ConcreteBinaryTower 0) :
  concrete_mul a (b + c) = concrete_mul a b + concrete_mul a c := by
  rcases eq_zero_or_eq_one (a := a) with (ha | ha)
  · simp [ha, concrete_mul, add_self_cancel, zero_is_0]  -- a = zero
  · simp [ha, concrete_mul, add_self_cancel, zero_is_0, concrete_one_ne_zero, one_is_1];
    rcases eq_zero_or_eq_one (a := b + c) with (hb_add_c | hb_add_c)
    · simp [hb_add_c, zero_is_0];
      rw [zero_is_0] at hb_add_c
      have b_eq_c: b = c := (add_eq_zero_iff_eq b c).mp hb_add_c
      simp only [b_eq_c, add_self_cancel]
    · simp [hb_add_c, concrete_one_ne_zero, one_is_1, zero_is_0];
      have c_cases := (add_eq_one_iff b c).mp hb_add_c
      rcases eq_zero_or_eq_one (a := b) with (hb | hb)
      · simp [hb, zero_is_0];
        rw [one_is_1] at hb_add_c
        rw [zero_is_0] at hb
        simp [hb] at c_cases
        have c_ne_0: c ≠ 0 := by
          simp only [c_cases, ne_eq, one_ne_zero, not_false_eq_true]
        rw [if_neg c_ne_0]
        exact c_cases.symm
      · rw [one_is_1] at hb; simp [hb, concrete_one_ne_zero];
        simp [hb] at c_cases
        exact c_cases

lemma concrete_mul_right_distrib0 (a b c : ConcreteBinaryTower 0) :
  concrete_mul (a + b) c = concrete_mul a c + concrete_mul b c := by
  rw [concrete_mul_comm0 (a:=(a+b)) (b:=c)]
  rw [concrete_mul_comm0 (a:=a) (b:=c)]
  rw [concrete_mul_comm0 (a:=b) (b:=c)]
  exact concrete_mul_left_distrib0 (a:=c) (b:=a) (c:=b)

lemma concrete_mul_inv_cancel0 (a : ConcreteBinaryTower 0) (h : a ≠ 0) :
  concrete_mul a (concrete_inv a) = one := by
  -- Since `a` is in GF(2) and `a ≠ 0`, `a` must be `one`.
  rcases eq_zero_or_eq_one (a := a) with (ha_zero | ha_one)
  · contradiction
  · simp [ha_one]
    simp [concrete_inv]
    rw [if_neg concrete_one_ne_zero]
    rw [concrete_one_mul0]
    simp only [concrete_pow_nat, ↓reduceIte]

-- Natural number casting
def natCast {k: ℕ} (n : ℕ) : ConcreteBinaryTower k := if n % 2 = 0 then zero else one
def natCast_zero {k: ℕ} : natCast (k:=k) 0 = zero := by rfl

def natCast_succ {k: ℕ} (n : ℕ) : natCast (k:=k) (n + 1) = natCast (k:=k) n + 1 := by
  by_cases h : n % 2 = 0
  · -- If n % 2 = 0, then (n+1) % 2 = 1
    have h_succ : (n + 1) % 2 = 1 := by omega
    simp only [natCast, h, h_succ]; norm_num; rw [one_is_1, zero_is_0]; norm_num
  · -- If n % 2 = 1, then (n+1) % 2 = 0
    have h_succ : (n + 1) % 2 = 0 := by omega
    simp only [natCast, h, h_succ]; norm_num; rw [one_is_1, zero_is_0, add_self_cancel]

instance {k: ℕ} : NatCast (ConcreteBinaryTower k) where
  natCast n:= natCast n

@[simp]
lemma concrete_natCast_zero_eq_zero {k:ℕ} : natCast 0 = (0: ConcreteBinaryTower k) := by
  simp only [natCast, Nat.zero_mod, ↓reduceIte, zero_is_0]

@[simp]
lemma concrete_natCast_one_eq_one {k:ℕ} : natCast 1 = (1: ConcreteBinaryTower k) := by
  simp only [natCast, Nat.mod_succ, one_ne_zero, ↓reduceIte, one_is_1]

-- help simp recognize the NatCast coercion
@[simp] lemma natCast_eq {k: ℕ} (n : ℕ) : (↑n : ConcreteBinaryTower k) = natCast n := rfl

-- Integer casting
def intCast {k: ℕ} (n : ℤ) : ConcreteBinaryTower k := if n % 2 = 0 then zero else one

instance {k:ℕ} : IntCast (ConcreteBinaryTower k) where
  intCast n:= intCast n

def intCast_ofNat {k:ℕ} (n : ℕ) : intCast (k:=k) (n : ℤ) = natCast n := by
  have h_mod_eq : (n : ℤ) % 2 = 0 ↔ n % 2 = 0 := by omega
  by_cases h : n % 2 = 0
  · -- Case: n % 2 = 0
    have h_int : (n : ℤ) % 2 = 0 := h_mod_eq.mpr h
    simp only [intCast, natCast, h, h_int]
  · -- Case: n % 2 ≠ 0
    have h' : n % 2 = 1 := by omega  -- For n : ℕ, if not 0, then 1
    have h_int : (n : ℤ) % 2 = 1 := by omega  -- Coercion preserves modulo
    simp only [intCast, natCast, h, h_int, h']
    rfl

@[simp] lemma my_neg_mod_two (m : ℤ) : (-m) % 2 = if m % 2 = 0 then 0 else 1 := by omega
@[simp] lemma mod_two_eq_zero (m: ℤ): m % 2 = (-m) % 2 := by omega

def intCast_negSucc {k:ℕ} (n : ℕ) : intCast (k:=k) (Int.negSucc n) = - (↑(n + 1) : ConcreteBinaryTower k) := by
  by_cases h_mod : (n + 1) % 2 = 0
  · -- ⊢ intCast (Int.negSucc n) = -↑(n + 1)
    have h_neg : (-(n + 1 : ℤ)) % 2 = 0 := by omega
    unfold intCast
    have int_neg_succ: Int.negSucc n = -(n+1 : ℤ) := by rfl
    rw [int_neg_succ]
    simp only [h_neg]
    have h_nat : (↑(n + 1) : ConcreteBinaryTower k) = (zero : ConcreteBinaryTower k) := by
      simp only [natCast_eq, natCast, h_mod]
      rfl
    rw [h_nat]
    rfl
  · -- ⊢ intCast (Int.negSucc n) = -↑(n + 1)
    have h_neg : (-(n + 1 : ℤ)) % 2 = 1 := by omega
    unfold intCast
    have int_neg_succ: Int.negSucc n = -(n+1 : ℤ) := by rfl
    rw [int_neg_succ]
    simp only [h_neg]
    rw [if_neg (by simp)]
    have h_nat : (↑(n + 1) : ConcreteBinaryTower k) = (one : ConcreteBinaryTower k) := by
      simp only [natCast_eq, natCast, h_mod]
      rfl
    rw [h_nat]
    rfl

end BaseDefinitions

-------------------------------------------------------------------------------------------
-- Structure to hold properties at a given level k
structure ConcreteBTFStepResult (k : ℕ) where
  mul_eq : ∀ (a b : ConcreteBinaryTower k) (h_k : k > 0)
           {a₁ a₀ b₁ b₀ : ConcreteBinaryTower (k-1)}
           (h_a : (a₁, a₀) = split h_k a)
           (h_b : (b₁, b₀) = split h_k b),
           a * b = join h_k (a₀*b₁ + b₀*a₁ + a₁*b₁ * Z (k - 1)) (a₀*b₀ + a₁*b₁)
  mul_eq_concrete_mul(a b : ConcreteBinaryTower k): a * b = concrete_mul a b := rfl -- HMul instance
  zero_mul : ∀ a : ConcreteBinaryTower k, concrete_mul zero a = zero
  zero_mul' : ∀ a : ConcreteBinaryTower k, concrete_mul 0 a = 0
  mul_zero : ∀ a : ConcreteBinaryTower k, concrete_mul a zero = zero
  mul_zero' : ∀ a : ConcreteBinaryTower k, concrete_mul a 0 = 0
  one_mul : ∀ a : ConcreteBinaryTower k, concrete_mul one a = a
  mul_one : ∀ a : ConcreteBinaryTower k, concrete_mul a one = a
  mul_assoc : ∀ a b c : ConcreteBinaryTower k, concrete_mul (concrete_mul a b) c = concrete_mul a (concrete_mul b c)
  mul_comm : ∀ a b : ConcreteBinaryTower k, concrete_mul a b = concrete_mul b a
  mul_left_distrib : ∀ a b c : ConcreteBinaryTower k, concrete_mul a (b + c) = concrete_mul a b + concrete_mul a c
  mul_right_distrib : ∀ a b c : ConcreteBinaryTower k, concrete_mul (a + b) c = concrete_mul a c + concrete_mul b c
  add_assoc : ∀ a b c : ConcreteBinaryTower k, (a + b) + c = a + (b + c)
  add_comm : ∀ a b : ConcreteBinaryTower k, a + b = b + a
  add_zero : ∀ a : ConcreteBinaryTower k, a + zero = a
  zero_add : ∀ a : ConcreteBinaryTower k, zero + a = a
  add_neg : ∀ a : ConcreteBinaryTower k, a + (neg a) = zero
  mul_inv_cancel : ∀ a : ConcreteBinaryTower k, a ≠ zero → concrete_mul a (concrete_inv a) = one

-------------------------------------------------------------------------------------------
section InductiveConcreteBTFPropertiesProofs -- for k > 0
variable {k : ℕ} (h_k: k > 0) (recArgument : (m : ℕ) → m < k → ConcreteBTFStepResult m)

theorem concrete_mul_eq (a b: ConcreteBinaryTower k) (h_k: k > 0)
  {a₁ a₀ b₁ b₀: ConcreteBinaryTower (k-1)}
  (h_a: (a₁, a₀) = split h_k a)
  (h_b: (b₁, b₀) = split h_k b):
  a * b = join h_k (a₀*b₁ + b₀*a₁ + a₁*b₁ * Z (k - 1)) (a₀*b₀ + a₁*b₁) := by
  -- unfold concrete_mul
  -- simp only [dif_neg (Nat.ne_of_gt h_k_gt_0)]
  -- let (a₁, a₀) := split h_k_gt_0 a
  -- let (b₁, b₀) := split h_k_gt_0 b
  -- simp only [split_of_join, join_of_split, h_k_gt_0, Nat.sub_add_cancel, Nat.sub_zero, Nat.pow_one]
  -- conv =>
  --   lhs
  --   rw [concrete_mul]
  -- rfl
  sorry

lemma concrete_zero_mul {recArg : (m : ℕ) → m < k → ConcreteBTFStepResult m} (a : ConcreteBinaryTower k) :
  concrete_mul (zero (k:=k)) a = zero (k:=k) := by
  unfold concrete_mul
  by_cases h_k_zero : k = 0
  · -- Base case: k = 0
    simp only [h_k_zero, ↓reduceDIte, zero, dif_pos, ite_true]
  · -- Inductive case: k > 0
    simp only [dif_neg h_k_zero]
    -- Obtain h_k_gt_0 from h_k_zero
    have h_k_gt_0_proof : k > 0 := by omega
    -- Split zero into (zero, zero)
    have h_zero_split : split h_k_gt_0_proof (zero (k:=k)) = (zero, zero) := by rw [split_zero]
    let (a₁, a₀) := (zero (k:=k-1), zero (k:=k-1))
    let (b₁, b₀) := split h_k_gt_0_proof a
    rw [h_zero_split]
    simp only
    -- Apply the inductive hypothesis to a₁*b₁, a₀*b₀, a₁*b₀, a₀*b₁
    let recArgPrevLevel := recArg (k-1) (Nat.sub_one_lt_of_lt h_k_gt_0_proof)
    simp only [zero_is_0, zero_add, recArgPrevLevel.zero_mul']
    simp only [← zero_is_0, join_zero h_k_gt_0_proof]

lemma concrete_mul_zero {recArg : (m : ℕ) → m < k → ConcreteBTFStepResult m} (a : ConcreteBinaryTower k) :
  concrete_mul a (zero (k:=k)) = zero (k:=k) := by
  unfold concrete_mul
  by_cases h_k_zero : k = 0
  · -- Base case: k = 0
    simp only [h_k_zero, ↓reduceDIte, zero, BitVec.zero_eq, ↓reduceIte, ite_self]
  · -- Inductive case: k > 0
    simp only [dif_neg h_k_zero]
    -- Obtain h_k_gt_0 from h_k_zero
    have h_k_gt_0_proof : k > 0 := by omega
    -- Split zero into (zero, zero)
    have h_zero_split : split h_k_gt_0_proof (zero (k:=k)) = (zero, zero) := by rw [split_zero]
    -- Split a into (a₁, a₀)
    let (a₁, a₀) := split h_k_gt_0_proof a
    let (b₁, b₀) := (zero (k:=k-1), zero (k:=k-1))
    -- Rewrite with the zero split
    rw [h_zero_split]
    simp only
    -- Apply the inductive hypothesis
    let recArgPrevLevel := recArg (k-1) (Nat.sub_one_lt_of_lt h_k_gt_0_proof)
    simp only [zero_is_0, zero_add, recArgPrevLevel.mul_zero']
    -- Use join_zero to complete the proof
    simp only [← zero_is_0, recArgPrevLevel.zero_mul, join_zero h_k_gt_0_proof]

lemma concrete_one_mul {recArg : (m : ℕ) → m < k → ConcreteBTFStepResult m} (a : ConcreteBinaryTower k) :
  concrete_mul (one (k:=k)) a = a := by
  unfold concrete_mul
  by_cases h_k_zero : k = 0
  · -- Base case: k = 0
    simp [h_k_zero, ↓reduceDIte, dif_pos, one_is_1, zero_is_0]; intro h; exact h.symm
  · -- Inductive case: k > 0
    have h_k_gt_0 : k > 0 := by omega
    let recArgPrevLevel := recArg (k-1) (Nat.sub_one_lt_of_lt h_k_gt_0)
    simp only [dif_neg h_k_zero]
    let (a₁, a₀) := split h_k_gt_0 a
    have h_split_a: split h_k_gt_0 a = (a₁, a₀) := by sorry
    rw [split_one]
    simp only [zero_is_0, zero_add, recArgPrevLevel.one_mul, recArgPrevLevel.zero_mul', add_zero]
    simp [add_assoc, add_self_cancel]
    have join_result : join h_k_gt_0 a₁ a₀ = a := by
      have split_join := join_of_split h_k_gt_0 a a₁ a₀
      exact (split_join h_split_a).symm
    exact join_result

lemma concrete_mul_one {recArg : (m : ℕ) → m < k → ConcreteBTFStepResult m} (a : ConcreteBinaryTower k) :
  concrete_mul a (one (k:=k)) = a := by
  unfold concrete_mul
  by_cases h_k_zero : k = 0
  · -- Base case: k = 0
    simp [h_k_zero, ↓reduceDIte, dif_pos, one_is_1, zero_is_0];
    conv =>
      lhs
      simp only [if_self_rfl]
  · -- Inductive case: k > 0
    have h_k_gt_0 : k > 0 := by omega
    let recArgPrevLevel := recArg (k-1) (Nat.sub_one_lt_of_lt h_k_gt_0)
    simp only [dif_neg h_k_zero]
    let (a₁, a₀) := split h_k_gt_0 a
    have h_split_a: split h_k_gt_0 a = (a₁, a₀) := by sorry
    rw [split_one]
    simp only [zero_is_0, zero_add, recArgPrevLevel.mul_one, recArgPrevLevel.mul_zero',
      recArgPrevLevel.zero_mul', add_zero]
    simp [add_assoc, add_self_cancel]
    have join_result : join h_k_gt_0 a₁ a₀ = a := by
      have split_join := join_of_split h_k_gt_0 a a₁ a₀
      exact (split_join h_split_a).symm
    exact join_result

lemma concrete_pow_base_one {recArg : (m : ℕ) → m < k → ConcreteBTFStepResult m} (n : ℕ) : concrete_pow_nat (k:=k) (x:=1) n = 1 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    -- ih: ∀ m, m < n → concrete_pow_nat (k:=k) (x:=1) m = 1
    unfold concrete_pow_nat
    by_cases h_n_zero : n = 0
    · -- Base case: n = 0
      rw [if_pos h_n_zero]
      exact one_is_1  -- one = 1
    · -- Inductive step: n ≠ 0
      rw [if_neg h_n_zero]
      by_cases h_mod : n % 2 = 0
      · -- Even case: n % 2 = 0
        rw [if_pos h_mod]
        have h_square : concrete_mul (1 : ConcreteBinaryTower k) 1 = 1 := by
          rw [← one_is_1]
          rw [concrete_one_mul (recArg:=recArg)]  -- Assume concrete_mul 1 1 = 1
        rw [h_square]
        have h_div_lt : n / 2 < n := by
          apply Nat.div_lt_self
          simp [Nat.ne_zero_iff_zero_lt.mp h_n_zero]
          exact Nat.le_refl 2
        apply ih (n / 2) h_div_lt  -- Use ih for n / 2 < n
      · -- Odd case: n % 2 ≠ 0
        rw [if_neg h_mod]
        have h_square : concrete_mul (1 : ConcreteBinaryTower k) 1 = 1 := by
          rw [← one_is_1]
          rw [concrete_one_mul (recArg:=recArg)]  -- Assume concrete_mul 1 1 = 1
        rw [h_square]
        have h_div_lt : n / 2 < n := by
          apply Nat.div_lt_self
          simp [Nat.ne_zero_iff_zero_lt.mp h_n_zero]
          exact Nat.le_refl 2
        rw [ih (n / 2) h_div_lt]  -- Use ih for n / 2 < n
        rw [← one_is_1]
        rw [concrete_one_mul (recArg:=recArg)]  -- Assume concrete_mul 1 1 = 1

lemma concrete_mul_assoc (a b c : ConcreteBinaryTower k) :
  concrete_mul (concrete_mul a b) c = concrete_mul a (concrete_mul b c) := by
  unfold concrete_mul
  sorry

lemma concrete_mul_comm (a b : ConcreteBinaryTower k) :
  concrete_mul a b = concrete_mul b a := by
  unfold concrete_mul
  sorry

lemma concrete_mul_left_distrib (a b c : ConcreteBinaryTower k) :
  concrete_mul a (b + c) = concrete_mul a b + concrete_mul a c := by
  unfold concrete_mul
  by_cases h_k_zero : k = 0
  · -- Base case k = 0
    simp only [h_k_zero, ↓reduceDIte, dif_pos]
    -- In GF(2), this is true: a * (b + c) = a*b + a*c.
    -- (a AND (b XOR c)) = (a AND b) XOR (a AND c)
    -- This is a property of XOR and AND.
    -- BitVec.xor is add, BitVec.and is mul.
    -- The multiplication `concrete_mul` for k=0 is not BitVec.and!
    -- It's a special case, so we need to expand it.
    -- cases BitVec.eq_zero_or_eq_one rfl a with
    -- | inl ha0 => simp [ha0]
    -- | inr ha1 => simp [ha1]
    sorry
  · -- Inductive case k > 0
    simp only [dif_neg h_k_zero]
    have h_k_gt_0' : k > 0 := by omega
    -- This is another very involved proof. It requires:
    -- 1. Splitting (b+c) into (b₁+c₁, b₀+c₀)
    -- 2. Expanding both sides using `concrete_mul_eq`
    -- 3. Applying the distributive property at level k-1 (from `recArgument (k-1)`)
    -- 4. Using associativity and commutativity of `+` and `*` at level k-1.
    -- It is very similar to the proof of associativity for Karatsuba.
    sorry

lemma concrete_mul_right_distrib (a b c : ConcreteBinaryTower k) :
  concrete_mul (a + b) c = concrete_mul a c + concrete_mul b c := by
  rw [concrete_mul_comm (a:=(a+b)) (b:=c)]
  rw [concrete_mul_comm (a:=a) (b:=c)]
  rw [concrete_mul_comm (a:=b) (b:=c)]
  exact concrete_mul_left_distrib (a:=c) (b:=a) (c:=b)

instance instInvConcreteBTF: Inv (ConcreteBinaryTower k) where
  inv := concrete_inv

lemma concrete_mul_inv_cancel {recArg : (m : ℕ) → m < k → ConcreteBTFStepResult m} (a : ConcreteBinaryTower k) (h : a ≠ 0) :
  concrete_mul a (concrete_inv a) = one := by
  unfold concrete_inv
  -- simp only [h, ↓reduceIte]
  -- unfold concrete_pow_nat
  -- This proof requires that `concrete_pow_nat x (2^k - 2)` is the inverse.
  -- This is a property of finite fields, x^(|F|-2) = x^(-1) for x != 0.
  -- This is usually proved by showing x^(|F|-1) = 1 (Fermat's Little Theorem for fields)
  -- The base case (k=0, GF(2)) is shown by direct computation.
  -- For k > 0, this needs the field structure of `ConcreteBinaryTower k`.
  -- Since `instField` is the goal, this proof is typically *after* the field instance is established, or relies on a recursive argument.
  -- Given the structure, it needs to be proven by induction as well.
  -- The base case for k=0 is provided (`concrete_mul_inv_cancel0`).
  -- For k>0, we need to show that the recursive definition of multiplication and inversion works.
  sorry

lemma concrete_inv_zero : concrete_inv (k:=k) 0 = 0 := by
  simp only [concrete_inv, zero_is_0, ↓reduceIte]

lemma concrete_inv_one {recArg : (m : ℕ) → m < k → ConcreteBTFStepResult m} : concrete_inv (k:=k) 1 = 1 := by
  simp only [concrete_inv, zero_is_0, one_ne_zero, ↓reduceIte, concrete_pow_base_one (recArg:=recArg)]

instance instHDivConcreteBTF: HDiv (ConcreteBinaryTower k) (ConcreteBinaryTower k) (ConcreteBinaryTower k) where
  hDiv a b := a * (concrete_inv b)

lemma concrete_div_eq_mul_inv (a b : ConcreteBinaryTower k) : a / b = a * (concrete_inv b) := by
  rfl

instance instHPowConcreteBTF: HPow (ConcreteBinaryTower k) ℤ (ConcreteBinaryTower k) where
  hPow a n :=
    match n with
    | Int.ofNat m => concrete_pow_nat a m
    | Int.negSucc m =>
      -- n = -(m+1)
      if a = 0 then 0
      else concrete_pow_nat (concrete_inv a) (m + 1) -- a^(-(m+1)) = (a^(-1))^(m+1)

instance : Div (ConcreteBinaryTower k) where
  div a b := a * (concrete_inv b)

-- Ring equivalence
-- instance toBTField: ConcreteBinaryTower k ≃+* BinaryTower.BTField k := sorry
-- instance fromBTField : BinaryTower.BTField k ≃+* ConcreteBinaryTower k := toBTField.symm
-- theorem toBTField_preserves_Z: toBTField (Z k) = BinaryTower.Z k := sorry

end InductiveConcreteBTFPropertiesProofs
-------------------------------------------------------------------------------------------

def InductiveConcreteBTFPropertiesAux (k : ℕ) (rec : ∀ m : ℕ, m < k → ConcreteBTFStepResult m): ConcreteBTFStepResult k :=
  match k with
  | 0 =>
    let result: ConcreteBTFStepResult 0 :={
      mul_eq := fun a b h_k _ _ _ _ _ _ => by
        have h_l_ne_lt_0 := Nat.not_lt_zero 0
        exact absurd h_k h_l_ne_lt_0,
      mul_eq_concrete_mul := by sorry,
      zero_mul := concrete_zero_mul0,
      zero_mul' := concrete_zero_mul0,
      mul_zero := concrete_mul_zero0,
      mul_zero' := concrete_mul_zero0,
      one_mul := concrete_one_mul0,
      mul_one := concrete_mul_one0,
      mul_assoc := concrete_mul_assoc0,
      mul_comm := concrete_mul_comm0,
      mul_left_distrib := concrete_mul_left_distrib0,
      mul_right_distrib := concrete_mul_right_distrib0,
      add_assoc := add_assoc,
      add_comm := add_comm,
      add_zero := add_zero,
      zero_add := zero_add,
      add_neg := neg_add_cancel,
      mul_inv_cancel := concrete_mul_inv_cancel0
    }
    result
  | k + 1 =>
    -- rec : (m : ℕ) → m < k + 1 → ConcreteBTFStepResult m
    let result: ConcreteBTFStepResult (k+1) :={
      mul_eq_concrete_mul := by sorry,
      zero_mul := concrete_zero_mul (recArg := rec),
      zero_mul' := fun a => by rw [←zero_is_0]; exact concrete_zero_mul (recArg := rec) a
      mul_zero := concrete_mul_zero (recArg := rec),
      mul_zero' := fun a => by rw [←zero_is_0]; exact concrete_mul_zero (recArg := rec) a
      one_mul := concrete_one_mul (recArg := rec),
      mul_one := concrete_mul_one (recArg := rec),
      mul_assoc := concrete_mul_assoc,
      mul_comm := concrete_mul_comm,
      mul_left_distrib := concrete_mul_left_distrib,
      mul_right_distrib := concrete_mul_right_distrib,
      add_assoc := add_assoc,
      add_comm := add_comm,
      add_zero := add_zero,
      zero_add := zero_add,
      add_neg := neg_add_cancel,
      mul_inv_cancel := concrete_mul_inv_cancel (k:=k+1) (recArg := rec),
      mul_eq := concrete_mul_eq (k:=k+1),
    }
    result

def InductiveConcreteBTFProperties (k : ℕ) : ConcreteBTFStepResult k :=
  WellFounded.fix (measure id).wf (fun k rec => InductiveConcreteBTFPropertiesAux k rec) k

instance instRingConcrete {k:ℕ}: Ring (ConcreteBinaryTower k) where
  toAddCommGroup := inferInstance
  toOne := inferInstance
  mul := concrete_mul
  mul_assoc := (InductiveConcreteBTFProperties (k:=k)).mul_assoc
  one_mul := (InductiveConcreteBTFProperties (k:=k)).one_mul
  mul_one := (InductiveConcreteBTFProperties (k:=k)).mul_one
  left_distrib := (InductiveConcreteBTFProperties (k:=k)).mul_left_distrib
  right_distrib := (InductiveConcreteBTFProperties (k:=k)).mul_right_distrib
  zero_mul := (InductiveConcreteBTFProperties (k:=k)).zero_mul
  mul_zero := (InductiveConcreteBTFProperties (k:=k)).mul_zero

  natCast n := natCast n
  natCast_zero := natCast_zero
  natCast_succ n := natCast_succ n
  intCast n := intCast n
  intCast_ofNat n := intCast_ofNat n
  intCast_negSucc n := intCast_negSucc n

instance instDivisionRingConcrete {k:ℕ}: DivisionRing (ConcreteBinaryTower k) where
  toRing := instRingConcrete (k:=k)
  inv := concrete_inv
  exists_pair_ne := concrete_exists_pair_ne (k := k)
  mul_inv_cancel := (InductiveConcreteBTFProperties (k:=k)).mul_inv_cancel
  inv_zero := concrete_inv_zero
  qsmul := (Rat.castRec · * ·)
  nnqsmul := (NNRat.castRec · * ·)

instance instFieldConcrete {k:ℕ}: Field (ConcreteBinaryTower k) where
  toDivisionRing := instDivisionRingConcrete (k:=k)
  mul_comm := (InductiveConcreteBTFProperties (k:=k)).mul_comm

#check instFieldConcrete (k:=0)
#check instFieldConcrete (k:=5)

end ConcreteDefinition
