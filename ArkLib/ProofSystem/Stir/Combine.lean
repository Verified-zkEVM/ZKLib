/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Least Authority
-/

import ArkLib.Data.CodingTheory.FieldReedSolomon
import ArkLib.Data.CodingTheory.ProximityBound
import ArkLib.Data.CodingTheory.RelativeHammingDistance


import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Probability.Distributions.Uniform

open Finset ReedSolomon
open scoped BigOperators NNReal

namespace Combine
variable {m n : ℕ}
         {F : Type*} [Field F] [Fintype F] [DecidableEq F]
         {ι : Type*} [Fintype ι] {domain : ι ↪ F}

/-! Section 4.5 in https://eprint.iacr.org/2024/390.pdf -/

/-- Geometric series formula in a field, for a unit `r : Fˣ`. -/
lemma geometric_sum_units {r :  Units F} {a : ℕ} :
  ∑ j : Fin (a + 1), (r ^ (j:ℕ) : F) =
    if r = 1 then (a + 1 : F)
    else (1 - r ^ (a + 1)) / (1 - r) := by sorry

/-- Coefficients r_i as used in the definition of Combine(),
r_i := r^{i + sum_{j < i}(d* - d_j)}, note that r_0 = 1 holds in the generic form as well.
(We iterate over 0...m-1, instead of 1...m as in STIR)-/
def ri (dstar : ℕ) (degs : Fin m → ℕ) (r : F) (i : Fin m) : F :=
  r^(i.val + ∑ j < i, (dstar - degs j))

/-- Combine(d*, r, (f_0, d_0), …, (f_{m-1}, d_{m-1}))(x)
:= sum_{i=0}^{m-1} r_i * f_i(x) * ( sum_{l=0}^{d* - d_i -1} (r·x)^l ) -/
def combineInterm
  (dstar : ℕ) (r : F) (fs : Fin m → ι → F) (degs : Fin m → ℕ)
  (hdegs : ∀ i, degs i ≤ dstar) : ι → F :=
    fun x =>
        ∑ i, (ri dstar degs r i) * fs i x * (∑ l < (dstar - degs i + 1),(r * (domain x))^l)

def conditionalExp
  (domain : ι ↪ F) (dstar : ℕ) (degree : ℕ) (r : F) : ι → F :=
  fun x =>
    let q := r * (domain x)
    if q = 1 then (dstar - degree + 1 : F)
    else (1 - q^(dstar - degree + 1)) / (1 - q)


/-- Combine(d*, r, (f_0, d_0), …, (f_{m-1}, d_{m-1}))(x) :=
      sum_{i=1}^m r_i * f_i(x) * ( (1 - (x*r)^(d* - d_i + 1)) / (1 - x*r) )    for x*r != 1,
      sum_{i=1}^m r_i * f_i(x) * ( d* - d_i + 1 )                              for x*r == 1. -/
def combineFinal
  (domain : ι ↪ F) (dstar : ℕ) (r : F) (fs : Fin m → ι → F)
  (degs : Fin m → ℕ) (hdegs : ∀ i, degs i ≤ dstar) : ι → F :=
    fun x =>
       ∑ i, (ri dstar degs r i) * fs i x * conditionalExp domain dstar (degs i) r x

/-- DegCor(d*, r, f, d)(x) := f(x) * ( sum_{l=0}^{d* - d} (r * x)^l ) -/
def degreeCorrInterm
  (dstar degree : ℕ) (r : F) (f : ι → F) (hd : degree ≤ dstar) : ι → F :=
    fun x =>
      let geom := ∑ l < (dstar - degree + 1), (r * (domain x)) ^ l
      f x * geom

/-- DegCor(d*, r, f, d)(x) :=
      f(x) * ( (1 - (x*r)^(d* - d + 1)) / (1 - x*r) )    for x*r != 1,
      f(x) * ( d* - d + 1 )                              for x*r = 1. -/
def degreeCorrFinal
(dstar degree : ℕ) (r : F) (f : ι → F) (hd : degree ≤ dstar) : ι → F :=
  fun x =>
    f x * conditionalExp domain dstar degree r x

/-- δ ∈ (0, min {1 − B⋆(ρ), 1 − ρ − 1/|L|}) -/
 noncomputable def combineRange
  {F : Type*} [Fintype F] (ι : Finset F) (degree : ℕ) : ℝ :=
    min (1- Bstar (rate degree ι)) (1- (rate degree ι) - 1/ Fintype.card F)

/--
If the random shift `r` causes the combined function to be far from
the degree `d⋆` RS code with probability exceeding `err*`,
then there is a large subset `S ⊆ L` on which each `fᵢ`
agrees with a degree `dᵢ` Reed–Solomon codeword. -/
lemma combine
  {dstar m : ℕ} {ι : Finset F} {domain : ι ↪ F} {L : Finset ι} [Nonempty ι]
  (fs : Fin m → ι → F) (degs : Fin m → ℕ) (hdegs : ∀ i, degs i ≤ dstar)
  (δ : ℝ) (hδPos : δ > 0) (hδLt : δ < combineRange ι dstar)
  (hProb : (PMF.uniformOfFintype F).toOuterMeasure
              { r | δᵣ((combineFinal domain dstar r fs degs hdegs), ↑(code F ι domain dstar)) ≤ δ} >
                err' F dstar (rate dstar ι) δ (m * (dstar + 1) - ∑ i, degs i)) :
    ∃ S : Finset ι,
      S ⊆ L ∧
      S.card ≥ (1 - δ) * L.card ∧
      ∀ i : Fin m, ∃ u : (ι → F),
      u ∈ ↑(code F ι domain (degs i)) ∧
      ∀ x : ι, x ∈ S → fs i x = u x := by sorry

end Combine
