/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Least Authority
-/

import ArkLib.ProofSystem.Stir.ToCodingTheory.ProximityBound
import ArkLib.ProofSystem.Stir.ToCodingTheory.FracHammingDist
import ArkLib.ProofSystem.Stir.ToCodingTheory.ReedSolomonCodes

import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Data.Finset.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Data.Fintype.Units

namespace Combine

/-! Section 4.5 in https://eprint.iacr.org/2024/390.pdf -/

/-- Geometric series formula in a field, for a unit `r : Fˣ`. -/
lemma geometric_sum_units {F : Type*} [Field F] [DecidableEq F] (r :  Units F) (a : ℕ) :
  -- STIR defines this for r ∈ 𝔽, but this requires 0^0=1. I think we can get away with r being invertible
  ∑ j : Fin (a + 1), (r ^ (j:ℕ) : F) =
    if r = 1 then (a + 1 : F)
    else (1 - r ^ (a + 1)) / (1 - r) := by sorry

/-- Coefficients r_i as used in the definition of Combine(), r_0 := 1, r_i := r^{i + sum_{j < i}(d* - d_j)}    for i > 0  (We range 0...m-1, not 1...m as in STIR)-/
def ri {F : Type*} [Field F] {m : ℕ} (dstar : ℕ) (degs : Fin m → ℕ) (r : F) (i : Fin m) : F :=
  if i.val = 0 then (1:F)
  else r^(i.val + (Finset.univ.filter (· < i)).sum fun j => dstar - degs j)

/-- Combine(d*, r, (f_0, d_0), …, (f_{m-1}, d_{m-1}))(x) := sum_{i=0}^{m-1} r_i * f_i(x) * ( sum_{l=0}^{d* - d_i -1} (r·x)^l ) -/
def combineInterm
  {F : Type*} [Field F]
  (L : Finset F)
  (m : ℕ)
  (dstar : ℕ)
  (r : F)
  (fs : Fin m → L → F)
  (degs : Fin m → ℕ)
  (hdegs : ∀ i, degs i ≤ dstar) : L → F :=
    fun x =>
      (Finset.univ : Finset (Fin m)).sum
      fun i =>
        let di := degs i
        let geom := (Finset.range (dstar - di + 1)).sum fun l => (r * x.val)^l
        (ri dstar degs r i) * fs i x * geom

/-- Combine(d*, r, (f_0, d_0), …, (f_{m-1}, d_{m-1}))(x) :=
      sum_{i=1}^m r_i * f_i(x) * ( (1 - (x*r)^(d* - d_i + 1)) / (1 - x*r) )    for x*r != 1,
      sum_{i=1}^m r_i * f_i(x) * ( d* - d_i + 1 )                              for x*r == 1. -/
def combineFinal
  {F : Type*} [Field F] [DecidableEq F]
  {L : Finset F}
  {m : ℕ}
  (dstar : ℕ)
  (r : F)
  (fs : Fin m → L → F)
  (degs : Fin m → ℕ)
  (hdegs : ∀ i, degs i ≤ dstar) : L → F :=
    fun x =>
      let q := r * x.val
      (Finset.univ : Finset (Fin m)).sum
      fun i =>
        let di := degs i
        let geom := if q = 1 then (dstar - di + 1 : F)
                    else (1 - q^(dstar - di + 1)) / (1 - q)
        (ri dstar degs r i) * fs i x * geom

/-- DegCor(d*, r, f, d)(x) := f(x) * ( sum_{l=0}^{d* - d} (r * x)^l ) -/
def degreeCorrInterm
{F : Type*} [Field F]
(L : Finset F)
(dstar : ℕ)
(r : F)
(f : L → F)
(d : ℕ)
(hd : d ≤ dstar) : L → F :=
  fun x =>
    let geom := (Finset.range (dstar - d + 1)).sum fun l => (r * x.val) ^ l
    f x * geom

/-- DegCor(d*, r, f, d)(x) :=
      f(x) * ( (1 - (x*r)^(d* - d + 1)) / (1 - x*r) )    for x*r != 1,
      f(x) * ( d* - d + 1 )                              for x*r = 1. -/
def degreeCorrFinal
{F : Type*} [Field F] [DecidableEq F]
(L : Finset F)
(dstar : ℕ)
(r : F)
(f : L → F)
(d : ℕ)
(hd : d ≤ dstar) : L → F :=
  fun x =>
    let q := r * x.val
    let exp := dstar - d + 1
    let geom := if q = 1 then (dstar - d + 1 : F)
                else (1 - q ^ exp) / (1 - q)
    f x * geom

/-- δ ∈ (0, min {1 − B⋆(ρ), 1 − ρ − 1/|L|}) -/
 noncomputable def combineRange
  {F : Type*} [Field F] [Fintype F] [DecidableEq F]
  {L : Finset F}
  {d : ℕ}
  (C : ReedSolomonCode F L d): ℝ :=
   min (1- Bstar C.rate) (1- C.rate - 1/ Fintype.card F)

/--
If the random shift `r` causes the combined function to be far from the degree-`d⋆` RS code with probability exceeding `err*`, then there is a large subset `S ⊆ L` on which each `fᵢ` agrees with a degree-`dᵢ` Reed–Solomon codeword. -/
lemma combine
  {F : Type*} [Field F] [Fintype F] [DecidableEq F]
  {L : Finset F}
  {dstar : ℕ}
  {m : ℕ}
  (Cstar : ReedSolomonCode F L dstar)
  (fs   : Fin m → L → F)
  (degs : Fin m → ℕ)
  (hdegs : ∀ i, degs i ≤ dstar)
  (δ    : {δ // 0 < δ ∧ δ < combineRange Cstar })
  (Ci : (i: Fin m) → ReedSolomonCode F L (degs i))
  (hProb : (PMF.uniformOfFintype F).toOuterMeasure { r |
          fractionalHammingDistSet
            (combineFinal dstar r fs degs hdegs)
            (Cstar.code)
            (Cstar.nonempty)
          ≤ δ.val} > err' F dstar Cstar.rate δ (m * (dstar + 1) - ((Finset.univ : Finset (Fin m)).sum degs))) :
    ∃ S : Finset F,
      S ⊆ L ∧
      S.card ≥ (1 - δ.val) * L.card ∧
      ∀ i : Fin m, ∃ u : (L → F),
      u ∈ (Ci i).code ∧
      ∀ x : L, x.val ∈ S → fs i x = u x := by sorry

end Combine
