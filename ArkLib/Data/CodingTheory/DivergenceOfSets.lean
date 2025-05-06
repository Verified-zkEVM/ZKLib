/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Katerina Hristova, František Silváši, Julian Sutherland
-/

import ArkLib.Data.CodingTheory.RelativeHammingDistance

/-!
Proved definiton for divergence of an arbitrary set `U` from an arbitrary set `V`.
-/

namespace DivergenceOfSets

noncomputable section

open Classical

variable {ι : Type*} [Fintype ι]
         {F : Type*}
         {U V C : Set (ι → F)}

/--
`d_U` is the set of achievable relative Hamming distances between elements `u ∈ U` and `V`.
-/
def d_U [Nonempty ι] (U V : Set (ι → F)) : Set ℚ :=
  { d : ℚ | ∃ u ∈ U, δᵣ(u,V) = d }

@[simp]
lemma d_U_subset_relHammingDistRange [Nonempty ι] :
d_U U C ⊆ RelativeHamming.distRange ι :=
  λ _ _ ↦ by aesop (add simp d_U)

@[simp]
lemma finite_d_U [Nonempty ι] : (d_U U V).Finite :=
  Set.Finite.subset RelativeHamming.finite_relHammingDistRange d_U_subset_relHammingDistRange

/--
divergence of an arbitrary set `U` from an arbitrary set `V`.
-/
def div_U_from_V [Nonempty ι] (U : Set (ι → F)) (V : Set (ι → F)) : ℚ :=
  have : Fintype (d_U U V) := @Fintype.ofFinite _ finite_d_U
  if h : (d_U U V).Nonempty
  then (d_U U V).toFinset.max' (Set.toFinset_nonempty.2 h)
  else 0

  end

  end DivergenceOfSets
