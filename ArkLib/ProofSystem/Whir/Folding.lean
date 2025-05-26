/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Least Authority
-/

import ArkLib.Data.CodingTheory.SmoothDomain
import ArkLib.Data.CodingTheory.SmoothReedSolomon

namespace Fold

open Vector Finset

variable {F : Type*} [Field F]
variable {ι : Type*} [Field F] [Pow ι ℕ] [Coe ι F]


/--Type-level version of Lpow: elements of the image S.map (x ↦ x ^ 2^k).-/
def LpowT (S : Finset ι) (k : ℕ) := { y : ι // ∃ x ∈ S, y = x ^ (2^k) }

/--∃ x ∈ S, such that `y = x ^ 2^(k+1)`. extract_x returns `z = x ^ 2^k` such that `y = z^2`.-/
noncomputable def extract_x
  (S : Finset ι) (k : ℕ) (y : LpowT S (k + 1)) : LpowT S k :=
  let x := Classical.choose y.property
  let hx := Classical.choose_spec y.property
  let z := x ^ (2^k)
  ⟨z, ⟨x, hx.1, rfl⟩⟩

/--Given a function `f : LpowT S k → F`, foldf operates on two inputs:
  element `y ∈ LpowT S (k+1)`, hence `∃ x ∈ S, s.t. y = x ^ 2^(k+1)` and `α ∈ F`.
  It obtains the root of y as `xPow := extract_x S k y` -- here xPow is of the form x ^ 2^k.
  It returns the value `f(xPow) + f(- xPow)/2 + α • (f(xPow) - f(- xPow))/ 2•xPow`. -/
noncomputable def foldf (S : Finset ι) [LinearOrder ι]
{k : ℕ} [ Neg (LpowT S k) ] (y : LpowT S (k+1)) (f : LpowT S k → F) (α : F) : F :=
  let xPow := extract_x S k y
  let fx := f xPow
  let f_negx := f (-xPow)
  (fx + f_negx) / 2 + α • ((fx - f_negx) / (2 * (xPow.val : F)))


/--the function fold_k_core runs a recursion, for i, a vector `αs` of size (i+1) and
  a vector of (i+1) functions `fᵢ: LpowT S i → F`
  For i = 0, fold_k_core returns f₀ evaluated at x ∈ S, such that x^2 = y.
  For i = (i'+1) ≠ 0,
    αs is parsed as α || αs', where αs' is of size i
    function `fk : LpowT S i → F` is obtained by making a recursive call to
      `fold_k_core` on input `αs'`
    we obtain the final function `LpowT S (i+1) → F` by invoking `foldf` with `fk` and `α`.-/
noncomputable def fold_k_core (S : Finset ι) [LinearOrder ι] [∀ i : ℕ, Neg (LpowT S i)]
  : (i : ℕ) → (αs : Vector F (i+1)) →
    ((j : Fin (i+1)) → LpowT S j → F) →
    LpowT S (i+1) → F
| 0, _, fi => fun y =>
    let x := extract_x S 0 y
    fi 0 x
| i'+1, αs, fi => fun y =>
    let α := αs.head
    let αs' := αs.tail
    let fi' : (j : Fin (i'+1)) → LpowT S j → F :=
      fun j xj => fi (Fin.castSucc j) xj
    let fk := fold_k_core S i' αs' fi'
    foldf S y fk α

/--fold_k takes a vector `αs` of size (k+1) and a vector of (k+1) functions `fⱼ : Lpowt S j → F`
  and returns a function `Fold : LpowT S (k+1) → F` -/
noncomputable def fold_k (S : Finset ι) [LinearOrder ι]
  {k : ℕ} [∀ k : ℕ, Neg (LpowT S k)]
  (fi : (j : Fin (k+1)) → LpowT S j → F)
  (αs : Vector F (k+1)) : LpowT S (k+1) → F :=
  fold_k_core S k αs fi


end Fold
