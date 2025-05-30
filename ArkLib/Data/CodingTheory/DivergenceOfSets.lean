/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Katerina Hristova, František Silváši, Julian Sutherland
-/

import ArkLib.Data.CodingTheory.RelativeHammingDistance

/-!
Proved definition for divergence of arbitrary sets.
-/

namespace DivergenceOfSets

noncomputable section

open Classical

variable {ι : Type*} [Fintype ι]
         {F : Type*}
         {U V C : Set (ι → F)}

/--
The set of possible relative Hamming distances between two sets.
-/
def setPossibleDistBetweenSets [Nonempty ι] (U V : Set (ι → F)) : Set ℚ :=
  { d : ℚ | ∃ u ∈ U, δᵣ(u,V) = d }

/--
The set of possible relative Hamming distances between two sets is well-defined.
-/
@[simp]
lemma setPossibleDistBetweenSets_subset_relHammingDistRange [Nonempty ι] :
setPossibleDistBetweenSets U C ⊆ relHammingDistRange ι :=
  λ _ _ ↦ by aesop (add simp setPossibleDistBetweenSets)

/--
The set of possible relative Hamming distances between two sets is finite.
-/
@[simp]
lemma finite_setPossibleDistBetweenSets [Nonempty ι] : (setPossibleDistBetweenSets U V).Finite :=
  Set.Finite.subset finite_relHammingDistRange setPossibleDistBetweenSets_subset_relHammingDistRange

/--
Divergence of two arbitrary sets.
-/
def divergenceSets [Nonempty ι] (U : Set (ι → F)) (V : Set (ι → F)) : ℚ :=
  have : Fintype (setPossibleDistBetweenSets U V) :=
  @Fintype.ofFinite _ finite_setPossibleDistBetweenSets
  if h : (setPossibleDistBetweenSets U V).Nonempty
  then (setPossibleDistBetweenSets U V).toFinset.max' (Set.toFinset_nonempty.2 h)
  else 0

  end

  end DivergenceOfSets
