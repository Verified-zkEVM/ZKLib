/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Katerina Hristova, František Silváši, Julian Sutherland
-/

import Mathlib.InformationTheory.Hamming
import Mathlib.Analysis.Normed.Field.Lemmas

/-!
Proved definitions of relative Hamming distance and related notions for linear codes,
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
The relative Hamming distance between two vectors.
-/
def relHammingDist (u v : ι → F) : ℚ :=
  (hammingDist u v : ℚ) / (Fintype.card ι : ℚ)

/--
The relative Hamming distance between two vectors is at most `1`.
-/
@[simp]
lemma relHammingDist_le_one : relHammingDist u v ≤ 1 := by
  unfold relHammingDist
  rw [div_le_iff₀ (by simp)]
  simp [hammingDist_le_card_fintype]

/--
The relative Hamming distance between two vectors is non-negative.
-/
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
The range of the relative Hamming distance function.
-/
def relHammingDistRange (ι : Type*) [Fintype ι] : Set ℚ :=
  { d : ℚ | ∃ d' : ℕ, d' ≤ Fintype.card ι ∧ d = d' / Fintype.card ι }

/--
The range of the relative Hamming distance is well-defined.
-/
@[simp]
lemma relHammingDist_mem_relHammingDistRange : δᵣ(u, v) ∈ relHammingDistRange ι :=
  ⟨hammingDist _ _, Finset.card_filter_le _ _, rfl⟩

/--
The range of the relative Hamming distance function is a finite set.
-/
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

/--
The set of pairs of distinct elements from a finite set is finite.
-/
@[simp]
lemma finite_offDiag [Finite F] : C.offDiag.Finite := Set.Finite.offDiag (Set.toFinite _)

/--
The set of possible distances between distinct codewords in a code.
-/
def setPossibleDistC (C : Set (ι → F)) : Set ℚ :=
  { d : ℚ | ∃ p ∈ Set.offDiag C, δᵣ(p.1, p.2) = d }

section

/--
The set of possible distances between distinct codewords in a code is a subset of the range of the
relative Hamming distance function.
-/
@[simp]
lemma setPossibleDistC_subset_relHammingDistRange : setPossibleDistC C ⊆ relHammingDistRange ι :=
  λ _ _ ↦ by aesop (add simp setPossibleDistC)

/--
The set of possible distances between distinct codewords in a code is a finite set.
-/
@[simp]
lemma finite_setPossibleDistC [Nonempty ι] : (setPossibleDistC C).Finite :=
  Set.Finite.subset finite_relHammingDistRange setPossibleDistC_subset_relHammingDistRange

end

/--
The minimum relative Hamming distance of a code.
-/
def minRelHammingDistCode [Nonempty ι] (C : Set (ι → F)) : ℚ :=
  haveI : Fintype (setPossibleDistC C) := @Fintype.ofFinite _ finite_setPossibleDistC
  if h : (setPossibleDistC C).Nonempty
  then (setPossibleDistC C).toFinset.min' (Set.toFinset_nonempty.2 h)
  else 0

/--
`δᵣ C` denotes the minimum relative Hamming distance of a code `C`.
-/
notation "δᵣ" C => minRelHammingDistCode C

/--
The set of possible relative Hamming distances from a vector to a code.
-/
def setPossibleDistToC (w : ι → F) (C : Set (ι → F)) : Set ℚ :=
  { d : ℚ | ∃ c ∈ C, c ≠ w ∧ δᵣ(w, c) = d }

/--
The range set of possible relative Hamming distances from a vector to a code is a subset
of the range of the relative Hamming distance function.
-/
@[simp]
lemma setPossibleDistToC_subset_relHammingDistRange : setPossibleDistToC w C ⊆ relHammingDistRange ι :=
  λ d h ↦ by aesop (add simp setPossibleDistToC)

/--
The set of possible relative Hamming distances from a vector to a code is a finite set.
-/
@[simp]
lemma finite_setPossibleDistToC [Nonempty ι] : (setPossibleDistToC w C).Finite :=
  Set.Finite.subset finite_relHammingDistRange setPossibleDistToC_subset_relHammingDistRange

instance [Nonempty ι] : Fintype (setPossibleDistToC w C)
  := @Fintype.ofFinite _ finite_setPossibleDistToC

/--
The relative Hamming distance from a vector to a code.
-/
def relHammingDistToCode [Nonempty ι] (w : ι → F) (C : Set (ι → F)) : ℚ :=
  if h : (setPossibleDistToC w C).Nonempty
  then (setPossibleDistToC w C).toFinset.min' (Set.toFinset_nonempty.2 h)
  else 0

/--
`δᵣ(w,C)` denotes the relative Hamming distance between a vector `w` and a code `C`.
-/
notation "δᵣ(" w ", " C ")" => relHammingDistToCode w C

@[simp]
lemma zero_mem_relHammingDistRange : 0 ∈ relHammingDistRange ι := by use 0; simp

/--
The relative Hamming distances between a vector and a codeword is in the
range of the relative Hamming distance function.
-/
@[simp]
lemma relHammingDistToCode_mem_relHammingDistRange [Nonempty ι] :
  δᵣ(c, C) ∈ relHammingDistRange ι := by
  unfold relHammingDistToCode
  split_ifs
  · exact Set.mem_of_subset_of_mem (s₁ := (setPossibleDistToC c C).toFinset) (by simp) (Finset.min'_mem _ _)
  · simp

end
