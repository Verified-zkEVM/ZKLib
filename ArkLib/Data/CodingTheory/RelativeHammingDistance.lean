/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Katerina Hristova, František Silváši, Julian Sutherland
-/

import Mathlib.InformationTheory.Hamming
import Mathlib.Analysis.Normed.Field.Lemmas

/-!
Proved definitions of relative Hamming distance and related notions for a linear code `LC`,
including corner cases.
-/
open Classical

variable {ι : Type*} [Fintype ι]
         {F : Type*}
         {u v w c : ι → F}
         {C : Set (ι → F)}

@[simp]
lemma Fintype.zero_lt_card [Nonempty ι] : 0 < Fintype.card ι := by
  have := Fintype.card_ne_zero (α := ι); omega

noncomputable section

section

variable [Nonempty ι]

/--
relative Hamming distance between two vectors.
-/
def relHammingDist (u v : ι → F) : ℚ :=
  (hammingDist u v : ℚ) / (Fintype.card ι : ℚ)

@[simp]
lemma relHammingDist_le_one : relHammingDist u v ≤ 1 := by
  unfold relHammingDist
  rw [div_le_iff₀ (by simp)]
  simp [hammingDist_le_card_fintype]

@[simp]
lemma zero_le_relHammingDist : 0 ≤ relHammingDist u v := by
  unfold relHammingDist
  rw [le_div_iff₀ (by simp)]
  simp

end

/--
`δᵣ(u,v)` denotes the relative Hamming distance between vectors `u` and `v`.
-/
notation "δᵣ(" u ", " v ")" => relHammingDist u v

/--
the range of the relative Hamming distance function.
-/
def relHammingDistRange (ι : Type*) [Fintype ι] : Set ℚ :=
  { d : ℚ | ∃ d' : ℕ, d' ≤ Fintype.card ι ∧ d = d' / Fintype.card ι }

@[simp]
lemma relHammingDist_mem_relHammingDistRange : δᵣ(u, v) ∈ relHammingDistRange ι :=
  ⟨hammingDist _ _, Finset.card_filter_le _ _, rfl⟩

@[simp]
lemma finite_relHammingDistRange [Nonempty ι] : (relHammingDistRange ι).Finite := by
  simp only [relHammingDistRange, ← Set.finite_coe_iff, Set.coe_setOf]
  exact
    finite_iff_exists_equiv_fin.2
      ⟨Fintype.card ι + 1,
        ⟨⟨
        λ ⟨s, _⟩ ↦ ⟨(s * Fintype.card ι).num.toNat, by aesop (add safe (by omega))⟩,
        λ n ↦ ⟨n / Fintype.card ι, by use n; simp; omega⟩,
        λ ⟨_, _, _, h₂⟩ ↦ by field_simp [h₂],
        λ _ ↦ by simp
        ⟩⟩
      ⟩

@[simp]
lemma finite_offDiag [Finite F] : C.offDiag.Finite := Set.Finite.offDiag (Set.toFinite _)

/--
The set of possible distances between distinct codewords in a given code.
-/
def d_C (C : Set (ι → F)) : Set ℚ :=
  { d : ℚ | ∃ p ∈ Set.offDiag C, δᵣ(p.1, p.2) = d }

section

@[simp]
lemma d_C_subset_relHammingDistRange : d_C C ⊆ relHammingDistRange ι :=
  λ _ _ ↦ by aesop (add simp d_C)

@[simp]
lemma finite_d_C [Nonempty ι] : (d_C C).Finite :=
  Set.Finite.subset finite_relHammingDistRange d_C_subset_relHammingDistRange

end

/--
relative Hamming distance of a code.
-/
def minRelHammingDistCode [Nonempty ι] (C : Set (ι → F)) : ℚ :=
  haveI : Fintype (d_C C) := @Fintype.ofFinite _ finite_d_C
  if h : (d_C C).Nonempty
  then (d_C C).toFinset.min' (Set.toFinset_nonempty.2 h)
  else 0

/--
`δᵣ C` denotes the minimum relative Hamming distance of a code `C`
-/
notation "δᵣ" C => minRelHammingDistCode C

/--
`d_w` is the set of values of relHamming distance between a vector `w` and codewords `c ∈ C`.
-/
def d_w (w : ι → F) (C : Set (ι → F)) : Set ℚ :=
  { d : ℚ | ∃ c ∈ C, c ≠ w ∧ δᵣ(w, c) = d }

@[simp]
lemma d_w_subset_relHammingDistRange : d_w w C ⊆ relHammingDistRange ι :=
  λ d h ↦ by aesop (add simp d_w)

@[simp]
lemma finite_d_w [Nonempty ι] : (d_w w C).Finite :=
  Set.Finite.subset finite_relHammingDistRange d_w_subset_relHammingDistRange

instance [Nonempty ι] : Fintype (d_w w C) := @Fintype.ofFinite _ finite_d_w

/--
The relative Hamming distance from a vector to a code.
-/
def relHammingDistToCode [Nonempty ι] (w : ι → F) (C : Set (ι → F)) : ℚ :=
  if h : (d_w w C).Nonempty
  then (d_w w C).toFinset.min' (Set.toFinset_nonempty.2 h)
  else 0

/--
`δᵣ(w,C)` denotes the relative Hamming distance between a vector `w` and a code `C`.
-/
notation "δᵣ(" w ", " C ")" => relHammingDistToCode w C

@[simp]
lemma zero_mem_RelHammingDistRange : 0 ∈ relHammingDistRange ι := by use 0; simp

@[simp]
lemma relHammingDistToCode_mem_relHammingDistRange [Nonempty ι] :
  δᵣ(c, C) ∈ relHammingDistRange ι := by
  unfold relHammingDistToCode
  split_ifs
  · exact Set.mem_of_subset_of_mem (s₁ := (d_w c C).toFinset) (by simp) (Finset.min'_mem _ _)
  · simp

end
