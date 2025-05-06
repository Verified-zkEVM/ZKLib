/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Least Authority
-/

import ArkLib.ProofSystem.Stir.ToCodingTheory.FracHammingDist

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic


/-!  ###  Error–correcting codes over an alphabet  -/


/-- An error correcting code of finite length `|ι|` over some finite alphabet `A`. -/
structure ErrCorrCode
  (A : Type*) [Fintype A] [DecidableEq A]
  (ι : Type*) [Fintype ι] where
    words : Finset (ι → A)


namespace ErrCorrCode

variable {A : Type*} [Fintype A] [DecidableEq A] {ι : Type*} [Fintype ι] [DecidableEq ι]


/-- The set `Λ(C, f, δ)` of codewords within fractional Hamming distance `δ`
of function `f: ι → A`. -/
noncomputable def list (C : ErrCorrCode A ι) (f : ι → A) (δ : ℝ) : Finset (ι → A) :=
  C.words.filter (fun c ↦ fractionalHammingDist f c ≤ δ)

/-- A code is `(δ, ℓ)`–list decodable if every function `f : ι → Σ` has at most `ℓ` codewords
within fractional Hamming distance `δ` -/
def listDecodable (C : ErrCorrCode A ι) (δ : ℝ ) (ℓ : ℝ) : Prop :=
  ∀ f : ι → A, (C.list f δ).card ≤ ℓ

/-- A radius `δ` is `within unique decoding` when the code is `(δ, 1)`–list decodable. -/
def withinUniqueDecoding (C : ErrCorrCode A ι) (δ : ℝ) : Prop :=
  C.listDecodable δ 1

/-- L≠∅ → |C.code| ≥ 2 since |𝔽| ≥ 2 -/
lemma nonempty (C : ErrCorrCode A ι) : C.words.Nonempty := sorry

end ErrCorrCode

structure LinearCode
  (F : Type*) [Field F]  [Fintype F]
  (ι : Type*) [Fintype ι] where
  words : Finset (ι → F)

namespace LinearCode

/-- Forget the linear-structure and view a `LinearCode` as `ErrorCorrectingCode`-/
def toErrCorrCode
  {F : Type*} [Field F] [Fintype F] [DecidableEq F]
  {ι : Type*} [Fintype ι]
  (C : LinearCode F ι) : ErrCorrCode F ι :=
    ⟨C.words⟩

end LinearCode
