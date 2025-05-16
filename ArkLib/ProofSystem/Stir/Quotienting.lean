/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Least Authority
-/
import ArkLib.Data.CodingTheory.FieldReedSolomon
import ArkLib.Data.CodingTheory.ListDecodeability
import ArkLib.Data.CodingTheory.RelativeHammingDistance

open ReedSolomon ListDecodable

namespace Quotienting
variable {n : ℕ}
         (F : Type*) [Field F] [Fintype F] [DecidableEq F]
         (ι : Finset F)

/-- ansPoly S Ans is the unique interpolating polynomial of degree < |S|
    with Ans'(s) = Ans(s) for each s ∈ S.

    Note: For S=∅ we get Ans'(x) = 0 (the zero polynomial) -/
noncomputable def ansPoly (S : Finset F) (Ans : S → F) : Polynomial F :=
  Lagrange.interpolate S.attach (fun i => (i : F)) Ans

/-- VanishingPoly is the vanishing polynomial on S, i.e. the unique polynomial of degree |S|+1
    that is 0 at each s ∈ S and is not the zero polynomial. That is V(X) = ∏(s ∈ S) (X - s). -/
noncomputable def vanishingPoly (S : Finset F) : Polynomial F :=
  ∏ s ∈ S, (Polynomial.X - Polynomial.C s)

/-- funcQuotient is the quotient function that outputs
    if x ∈ S,  Fill(x).
    else       (f(x) - Ans'(x)) / V(x).
    Note here that, V(x) = 0 ∀ x ∈ S, otherwise V(x) ≠ 0. -/
noncomputable def funcQuotient (f : ι → F) (S : Finset F) (Ans Fill : S → F) : ι → F :=
  fun x =>
    if hx : x.val ∈ S then Fill ⟨x.val, hx⟩ -- if x ∈ S,  Fill(x).
    else (f x - (ansPoly F S Ans).eval x.val) / (vanishingPoly F S).eval x.val
    -- else, (f(x) - Ans'(x)) / V(x).

/-- polyQuotient is the polynomial derived from the polynomials fPoly, Ans' and V, where
    Ans' is a polynomial s.t. Ans'(x) = fPoly(x) for x ∈ S, and
    V is the vanishing polynomial on S as before.
    Then, polyQuotient = (fPoly - Ans') / V, where
    polyQuotient.degree < (fPoly.degree - ι.card) -/
noncomputable def polyQuotient {degree : ℕ} (S : Finset F) (fPoly : Polynomial F)
(hPoly : fPoly.degree < degree) : Polynomial F :=
  (fPoly - (ansPoly F S (fun s => fPoly.eval s))) / (vanishingPoly F S)

/-- We define the set disagreementSet(f,ι,S,Ans) as the set of all points x ∈ ι that lie in S
such that the Ans' disagrees with f, we have
disagreementSet := { x ∈ L | x ∈ S ∧ AnsPoly x ≠ f x }. -/
noncomputable def disagreementSet (f : ι → F) (S : Finset F) (Ans : S → F) : Finset F :=
  (ι.attach.filter (λ x ↦ (ansPoly F S Ans).eval x.val ≠ f x)).image Subtype.val

/- Quotienting Lemma-/
lemma quotienting {degree : ℕ} {domain : ι ↪ F} (S : Finset F) (hS_lt : S.card < degree)
  (C1 : code F ι domain degree) (C2 : code F ι domain (degree - S.card)) (C : Code ι F)
  (f : ι → F) (Ans Fill : S → F) (δ : ℝ) (hδPos : δ > 0) (hδLt : δ < 1)
  (h : ∀ u, u ∈ (relHammingBall C f δ) →
  ∃ (x : ι) (hx : x.val ∈ S), u x ≠ Ans ⟨x.val, hx⟩) :
    δᵣ((funcQuotient F ι f S Ans Fill), C2) +
      ((disagreementSet F ι f S Ans).card : ℝ) / (ι.card : ℝ) > δ := by
  sorry

end Quotienting
