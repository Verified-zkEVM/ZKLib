/-
Copyright (c) 2024 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import Mathlib.InformationTheory.Hamming
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Data.Set.Finite.Lattice
import Mathlib.Topology.MetricSpace.Infsep
import Mathlib.Data.ENat.Lattice

/-!
  # Basics of Coding Theory

  We define a general code `C` to be a subset of `n → R` for some finite index set `n` and some
  target type `R`.

  We can then specialize this notion to various settings. For `[CommSemiring R]`, we define a linear
  code to be a linear subspace of `n → R`. We also define the notion of generator matrix and
  (parity) check matrix.

  ## Main Definitions

  - `codeDist C`: The Hamming distance of a code `C`, defined as the infimum (in `ℕ∞`) of the
    Hamming distances between any two distinct elements of `C`. This is noncomputable.

  - `codeDist' C`: A computable version of `codeDist C`, assuming `C` is a `Fintype`.

  We define the block length, rate, and distance of `C`. We prove simple properties of linear codes
  such as the singleton bound.
-/


variable {n : Type*} [Fintype n] {R : Type*} [DecidableEq R]

section Distance

-- Notation for Hamming distance
notation "Δ₀(" u ", " v ")" => hammingDist u v

notation "‖" u "‖₀" => hammingNorm u

/-- The Hamming distance of a code `C` is the minimum Hamming distance between any two distinct
  elements of the code.
cd
We formalize this as the infimum `sInf` over all `d : ℕ` such that there exist `u v : n → R` in the
code with `u ≠ v` and `hammingDist u v ≤ d`. If none exists, then we define the distance to be `0`.
-/
noncomputable def codeDist (C : Set (n → R)) : ℕ :=
  sInf {d | ∃ u ∈ C, ∃ v ∈ C, u ≠ v ∧ Δ₀( u, v ) ≤ d}

-- TODO: rewrite this file using existing `(e)infsep` definitions

instance : EDist (n → R) where
  edist := fun u v => hammingDist u v

instance : Dist (n → R) where
  dist := fun u v => hammingDist u v

noncomputable def eCodeDistNew (C : Set (n → R)) : ENNReal := C.einfsep

noncomputable def codeDistNew (C : Set (n → R)) : ℝ := C.infsep

notation "‖" C "‖₀" => codeDist C

/-- The distance from a vector `u` to a code `C` is the minimum Hamming distance between `u`
and any element of `C`. -/
noncomputable def distFromCode (u : n → R) (C : Set (n → R)) : ℕ∞ :=
  sInf {d | ∃ v ∈ C, hammingDist u v ≤ d}

notation "Δ₀(" u ", " C ")" => distFromCode u C

@[simp]
theorem codeDist_empty : ‖ (∅ : Set (n → R) ) ‖₀ = 0 := by simp [codeDist]

@[simp]
theorem codeDist_subsingleton {C : Set (n → R)} [Subsingleton C] : ‖C‖₀ = 0 := by
  simp only [codeDist]
  have {d : ℕ} : (∃ u ∈ C, ∃ v ∈ C, u ≠ v ∧ hammingDist u v ≤ d) = False := by
    have h := @Subsingleton.allEq C _
    simp_all; intro a ha b hb hab
    have hEq : a = b := h a ha b hb
    simp_all
  have : {d | ∃ u ∈ C, ∃ v ∈ C, u ≠ v ∧ hammingDist u v ≤ d} = (∅ : Set ℕ) := by
    apply Set.eq_empty_iff_forall_not_mem.mpr
    simp [this]
  simp [this]

@[simp]
theorem codeDist_le_card (C : Set (n → R)) : codeDist C ≤ Fintype.card n := by
  by_cases h : Subsingleton C
  · simp
  · simp at h
    unfold Set.Nontrivial at h
    obtain ⟨u, hu, v, hv, huv⟩ := h
    refine Nat.sInf_le ?_
    simp
    refine ⟨u, And.intro hu ⟨v, And.intro hv ⟨huv, hammingDist_le_card_fintype⟩⟩⟩

/-- If `u` and `v` are two codewords of `C` with distance less than `codeDist C`,
then they are the same. -/
theorem eq_of_lt_codeDist {C : Set (n → R)} {u v : n → R} (hu : u ∈ C) (hv : v ∈ C)
    (huv : Δ₀(u, v) < ‖C‖₀) : u = v := by
  simp only [codeDist] at huv
  by_contra hNe
  push_neg at hNe
  revert huv
  simp
  refine Nat.sInf_le ?_
  simp only [Set.mem_setOf_eq]
  refine ⟨u, And.intro hu ⟨v, And.intro hv ⟨hNe, le_rfl⟩⟩⟩

@[simp]
theorem distFromCode_of_empty (u : n → R) : Δ₀(u, (∅ : Set (n → R))) = ⊤ := by
  simp [distFromCode]

theorem distFromCode_eq_top_iff_empty (u : n → R) (C : Set (n → R)) : Δ₀(u, C) = ⊤ ↔ C = ∅ := by
  apply Iff.intro
  · simp only [distFromCode]
    intro h
    apply Set.eq_empty_iff_forall_not_mem.mpr
    intro v hv
    apply sInf_eq_top.mp at h
    revert h
    simp
    refine ⟨Fintype.card n, v, And.intro hv ⟨?_, ?_⟩⟩
    · norm_num; exact hammingDist_le_card_fintype
    · norm_num
  · intro h; subst h; simp

@[simp]
theorem distFromCode_of_mem (C : Set (n → R)) {u : n → R} (h : u ∈ C) : Δ₀(u, C) = 0 := by
  simp only [distFromCode]
  apply ENat.sInf_eq_zero.mpr
  simp [h]

theorem distFromCode_eq_zero_iff_mem (C : Set (n → R)) (u : n → R) : Δ₀(u, C) = 0 ↔ u ∈ C := by
  apply Iff.intro
  · simp only [distFromCode]
    intro h
    apply ENat.sInf_eq_zero.mp at h
    revert h
    simp
  · intro h; exact distFromCode_of_mem C h

theorem distFromCode_eq_of_lt_half_codeDist (C : Set (n → R)) (u : n → R) {v w : n → R}
    (hv : v ∈ C) (hw : w ∈ C) (huv : Δ₀(u, v) < ‖C‖₀ / 2) (hvw : Δ₀(u, w) < ‖C‖₀ / 2) : v = w := by
  apply eq_of_lt_codeDist hv hw
  calc
    Δ₀(v, w) ≤ Δ₀(v, u) + Δ₀(u, w) := by exact hammingDist_triangle v u w
    _ = Δ₀(u, v) + Δ₀(u, w) := by simp only [hammingDist_comm]
    _ < ‖C‖₀ / 2 + ‖C‖₀ / 2 := by omega
    _ ≤ ‖C‖₀ := by omega

section Computable

/-- Computable version of the Hamming distance of a code `C`, assuming `C` is a `Fintype`.

The return type is `ℕ∞` since we use `Finset.min`. -/
def codeDist' (C : Set (n → R)) [Fintype C] : ℕ∞ :=
  Finset.min <| ((@Finset.univ (C × C) _).filter (fun p => p.1 ≠ p.2)).image
    (fun ⟨u, v⟩ => hammingDist u.1 v.1)

notation "‖" C "‖₀'" => codeDist' C

variable {C : Set (n → R)} [Fintype C]

@[simp]
theorem codeDist'_empty : ‖(∅ : Set (n → R))‖₀' = ⊤ := by
  simp [codeDist']

@[simp]
theorem codeDist'_subsingleton [Subsingleton C] : ‖C‖₀' = ⊤ := by
  simp [codeDist']
  apply Finset.min_eq_top.mpr
  simp [Finset.filter_eq_empty_iff]
  have h := @Subsingleton.elim C _
  simp_all
  exact h

theorem codeDist'_eq_codeDist : ‖C‖₀'.toNat = ‖C‖₀ := by
  by_cases h : Subsingleton C
  · simp
  · simp [codeDist, codeDist']
    have : codeDist' C ≠ ⊤ := by sorry
    sorry
    -- apply (ENat.toNat_eq_iff this).mp
    -- apply Finset.min_eq_top.mp
    -- simp [this]

/-- Computable version of the distance from a vector `u` to a code `C`, assuming `C` is a `Fintype`.
  -/
def distFromCode' (C : Set (n → R)) [Fintype C] (u : n → R) : ℕ∞ :=
Finset.min <| (@Finset.univ C _).image (fun v => hammingDist u v.1)

notation "Δ₀'(" u ", " C ")" => distFromCode' C u

end Computable

end Distance

section Linear

variable {k : Type*} [Fintype k] [CommSemiring R]

/-- Define a linear code from its generator matrix -/
def codeByGenMatrix (G : Matrix k n R) : Submodule R (n → R) :=
  LinearMap.range G.vecMulLinear
  -- Submodule.span R (Set.range G)

/-- Define a linear code from its (parity) check matrix -/
def codeByCheckMatrix (H : Matrix k n R) : Submodule R (n → R) :=
  LinearMap.ker H.mulVecLin

/-- The Hamming distance of a linear code can also be defined as the minimum Hamming norm of a
  non-zero vector in the code -/
noncomputable def linearCodeDist (C : Submodule R (n → R)) : ℕ :=
  sInf {d | ∃ u ∈ C, u ≠ 0 ∧ hammingNorm u ≤ d}

-- Require `[CommRing R]`
theorem codeDist_eq_linearCodeDist (C : Submodule R (n → R)) :
    codeDist C.carrier = linearCodeDist C := by
  simp [codeDist, linearCodeDist]
  congr; unfold setOf; funext d
  apply Eq.propIntro <;> intro h
  · obtain ⟨u, hu, v, hv, huv, hDist⟩ := h
    -- let w := u - v
    -- have hw : w ∈ C := by simp [Submodule.add_mem]
    -- refine ⟨w, And.intro hw ⟨v, And.intro hv ⟨huv, ?_⟩⟩⟩
    sorry
  · obtain ⟨u, hu, hNorm, hDist⟩ := h
    -- refine ⟨u, And.intro hu ⟨v, And.intro hv ⟨huv, ?_⟩⟩⟩
    sorry

section Computable

variable [DecidableEq n] [Fintype R]

/-- A computable version of the Hamming distance of a linear code `C`. -/
def linearCodeDist' (C : Submodule R (n → R)) [DecidablePred (· ∈ C)] : ℕ∞ :=
  Finset.min <| ((Finset.univ (α := C)).filter (fun v => v ≠ 0)).image (fun v => hammingNorm v.1)

end Computable

/-- The interleaving of a linear code `C` over index set `ι` is the submodule spanned by
`ι × n`-matrices whose rows are elements of `C`. -/
def interleaveCode (C : Submodule R (n → R)) (ι : Type*) : Submodule R ((ι × n) → R) :=
  Submodule.span R {v | ∀ i, ∃ c ∈ C, c = fun j => v (i, j)}

notation:20 C "^⋈" ι => interleaveCode C ι

-- instance : Fintype (interleaveCode C ι) := sorry

/-- Interleave two functions `u v : α → β`. -/
def Function.interleave₂ {α β : Type*} (u v : α → β) : (Fin 2) × α → β :=
  Function.uncurry (fun a => if a = 0 then u else v)

notation:20 u "⋈" v => Function.interleave₂ u v

end Linear

variable [Finite R]

open Fintype

/-- **Singleton bound** for arbitrary codes -/
theorem singleton_bound (C : Set (n → R)) :
    (ofFinite C).card ≤ (ofFinite R).card ^ (card n - ‖C‖₀ + 1) := sorry

variable [DivisionRing R]

/-- **Singleton bound** for linear codes -/
theorem singleton_bound_linear (C : Submodule R (n → R)) :
    Module.finrank R C ≤ card n - (codeDist C.carrier) + 1 := by sorry
  -- have : (ofFinite C).card = (ofFinite R).card ^ (Module.finrank R C) := by

-- #check card_eq_pow_finrank

-- #check cardinal_mk_eq_cardinal_mk_field_pow_rank
