/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Least Authority
-/

import ArkLib.Data.CodingTheory.SmoothReedSolomon

namespace ReedSolomon

open Finset SmoothDomain

variable {F : Type*} [Field F]

/-- Auxiliary function to assign values to the weight polynomial variables:
    index `0` ↦ `p.eval b`, index `j+1` ↦ `b j`. -/
private def toWeightAssignment
  {m : ℕ} (p : MvPolynomial (Fin m) F)
  (b : Fin m → Fin 2) : Fin (m+1) → F :=
    let b' : Fin m → F := fun i => ↑(b i : ℕ)
    Fin.cases (MvPolynomial.eval b' p)
              (fun i => ↑(b i : ℕ))

/-- constraint is true, if ∑ {b ∈ {0,1}^m} w(f(b),b) = σ for given
    m-variate polynomial `f` and `(m+1)`-variate polynomial `w`-/
def weightConstraint
  [DecidableEq F] {m : ℕ} (f : MvPolynomial (Fin m) F)
  (w : MvPolynomial (Fin (m+1)) F) (σ : F): Prop :=
    ∑ b : Fin m → Fin 2 , w.eval (toWeightAssignment f b) = σ

variable [DecidableEq F]
         {ι : Type*} [Fintype ι] [DecidableEq ι]

/--Definition 4.5
  Constraint Reed Solomon codes are smooth codes who's decoded m-variate
  polynomial satisfies the weight constraint for given `w` and `σ`.-/
def constraintCode
  (domain : ι ↪ F) [Smooth domain] (m : ℕ)
  (w : MvPolynomial (Fin (m+1)) F) (σ : F) : Set (ι → F) :=
    { f | ∃ (h : f ∈ smoothCode domain m),
      weightConstraint (mVdecode (⟨f, h⟩ : smoothCode domain m)) w σ }

/--Definition 4.6
  Multi-constraint Reed Solomon codes are smooth codes who's decoded m-variate
  polynomial satisfies the `t` weight constraints for given `w₀,...,wₜ₋₁` and
    `σ₀,...,σₜ₋₁`.-/
def multiConstraintCode
  (domain : ι ↪ F) [Smooth domain] (m t : ℕ)
  (w : Fin t → MvPolynomial (Fin (m+1)) F) (σ : Fin t → F) : Set (ι → F) :=
    { f |
      ∃ (h : f ∈ smoothCode domain m),
        ∀ i : Fin t, weightConstraint (mVdecode (⟨f, h⟩ : smoothCode domain m)) (w i) (σ i)}

end ReedSolomon
