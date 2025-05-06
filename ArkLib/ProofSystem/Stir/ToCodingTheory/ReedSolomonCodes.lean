/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Least Authority
-/

import ArkLib.ProofSystem.Stir.ToCodingTheory.FracHammingDist
import ArkLib.ProofSystem.Stir.ToCodingTheory.ErrCorrCodes

import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Tactic.NormNum
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.LinearAlgebra.Lagrange


/-!
# Construction of Reed–Solomon Codes

Given a finite field `F`, a nonempty set of evaluation points `L ⊆ F`,
and a degree bound `d`, we construct the Reed–Solomon code as follows:

1. **Polynomials of bounded degree.**
We collect all univariate polynomials over `F` of degree < `d` into
the finite set `polynomialsUpTo F d : Finset (Polynomial F)` by
identifying each polynomial with its list of coefficients in Fin d → F.

2. **Evaluation map.** Each polynomial `p` in `polynomialsUpTo F d`
is evaluated at every point in `L`, yielding a function `L → F`,
i.e `polynomialEvalOn F L : Polynomial F → (↑L → F)`

3. **Reed–Solomon code.** The set of codewords is defined as the image of the above evaluation map.

The construction ensures that C.code is constructive and of
Fintype `Finset (L → F)`, which makes constructions like
filtering and Lagrange interpolation more convinient.

-/

/-- Polynomials of degree `< d` over a finite field `F` -/
noncomputable def polynomialsUpTo
  (F : Type*) [Field F] [Fintype F] [DecidableEq F]
  (d : ℕ) : Finset (Polynomial F) :=
    (Finset.univ : Finset (Fin d → F)).image
    (fun c => ∑ i : Fin d, Polynomial.monomial (i : ℕ) (c i))

/-- Evaluate a polynomial `p` at each `x ∈ L`, returning a function `↑L → F`. -/
def polynomialEvalOn
  (F : Type*) [Field F] [Fintype F] [DecidableEq F]
  (L : Finset F) (p : Polynomial F) : ↑L → F :=
    fun (x : ↑L) => p.eval x.val


/-- The ReedSolomonCode structure, storing the codewords as `Finset (L → F)`. -/
structure ReedSolomonCode
  (F : Type*) [Field F] [Fintype F] [DecidableEq F]
  (L : Finset F)
  (d : ℕ) where
    nonempty_L : L.Nonempty
    L_ne_F     : L ≠ (Finset.univ : Finset F)
    code       : Finset (L → F)
    code_def   : code = (polynomialsUpTo F d).image (polynomialEvalOn F L)



namespace ReedSolomonCode

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {L : Finset F} {d : ℕ}

/-TODO: Make C.d a positive number, because expressions like (1-C.d) occure
  e.g. in the OutOfDomainSmpl lemma and for d=0 this makes no sense-/

/-- Given a codeword f ∈ C.code, C.poly(f) computes an associated polynomial
\hat{f} with \hat{f}(l) = f(l) ∀ l ∈ L and deg(\hat{f}) < d-/
noncomputable def poly (C : ReedSolomonCode F L d) (f : C.code) : Polynomial F :=
  Lagrange.interpolate L.attach (fun i => (i : F)) f

/-- Rate of a Reed-Solomon code ρ := d/|L| -/
noncomputable def rate (_C : ReedSolomonCode F L d) : ℝ := d / L.card

/-- L≠∅ → |C.code| ≥ 2 since |𝔽| ≥ 2 -/
lemma nonempty (C : ReedSolomonCode F L d) : C.code.Nonempty := sorry

/-- Complement of the evaluation set `L` in `F` i.e. `F\L` as a Finset -/
def domainComplement (_C : ReedSolomonCode F L d) : Finset F :=
  Finset.univ \ L

/-- L ≠ F → F\L ≠ ∅ -/
lemma domain_complement_nonempty
  (C : ReedSolomonCode F L d) : Nonempty C.domainComplement := by sorry

/-- Coarce a Reed–Solomon code into a `LinearCode` -/
def toLinearCode (C : ReedSolomonCode F L d) : LinearCode F ↑L :=
  {words := C.code}

end ReedSolomonCode
