/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Least Authority
-/
import ArkLib.ProofSystem.Stir.ToCodingTheory.ErrCorrCodes
import ArkLib.ProofSystem.Stir.ToCodingTheory.FracHammingDist
import ArkLib.ProofSystem.Stir.ToCodingTheory.ReedSolomonCodes

namespace Quotienting

/-- PolyAns S Ans is the unique interpolating polynomial of degree < |S|
   with PolyAns(s) = Ans(s) for each s ∈ S.

  Note: For S=∅ we get PolyAns(x) = 0 (the zero polynomial) -/
noncomputable def ansPoly
  (F : Type*) [Field F] [Fintype F] [DecidableEq F]
  (S : Finset F)
  (Ans : S → F) : Polynomial F :=
  Lagrange.interpolate S.attach (fun i => (i : F)) Ans

/-- VanishingPoly is the vanishing polynomial on S, i.e. the unique polynomial of degree |S|+1
   that is 0 at each s ∈ S and is not the zero polynomial. I.e V(X) = ∏(s ∈ S) (X - s). -/
noncomputable def vanishingPoly
  (F : Type*) [Field F] [Fintype F] [DecidableEq F]
  (S : Finset F) : Polynomial F :=
  ∏ s in S, (Polynomial.X - Polynomial.C s)

noncomputable def polyQuotient
  {F : Type*} [Field F] [Fintype F] [DecidableEq F]
  {d : ℕ}
  (f : Polynomial F) (hf : f.degree < d)
  (S : Finset F) (hS : S.card < d) : Polynomial F :=
    let pAns := ansPoly F S (fun s => f.eval s)
    let pV   := vanishingPoly F S
    (f - pAns) / pV

noncomputable def quotient
  (F : Type*) [Field F] [Fintype F] [DecidableEq F]
  (L : Finset F)
  (f : L → F)
  (S : Finset F)
  (Ans : S → F)
  (Fill : S → F)
  : L → F :=
    let pAns := ansPoly F S Ans
    let pV   := vanishingPoly F S
    fun x =>
      if hx : x.val ∈ S then
        Fill ⟨x.val, hx⟩
      else
        (f x - pAns.eval x.val) / pV.eval x.val

/-- We define the set T(f,L,S,Ans) as the set of all points x ∈ L that lie in S such that
  the AnsPoly disagrees with f. Formally: T := { x ∈ L | x ∈ S ∧ AnsPoly x ≠ f x }. -/
noncomputable def T
  (F : Type*) [Field F] [Fintype F] [DecidableEq F]
  (L : Finset F)
  (f : L → F)
  (S : Finset F)
  (Ans : S → F) : Finset F :=
  (L.attach.filter (λ x ↦ (ansPoly F S Ans).eval x.val ≠ f x)).image Subtype.val

/- Quotienting Lemma-/
lemma quotienting
  {F : Type*} [Field F] [Fintype F] [DecidableEq F]
  {L : Finset F}
  {d : ℕ}
  (S : Finset F) (hS_lt : S.card < d)
  (C1 : ReedSolomonCode F L d)
  (C2 : ReedSolomonCode F L (d - S.card))
  (f : L → F)
  (Ans Fill : S → F)
  (δ : ℝ) (hδ : 0 < δ ∧ δ < 1)
  (h : ∀ u, u ∈ C1.toLinearCode.toErrCorrCode.list f δ →
  ∃ (x : ↑L) (hx : x.val ∈ S), u x ≠ Ans ⟨x.val, hx⟩) :
    (fractionalHammingDistSet (quotient F L f S Ans Fill) C2.code C2.nonempty : ℝ)
      + ((T F L f S Ans).card : ℝ) / (L.card : ℝ) > δ := by
  sorry

end Quotienting
