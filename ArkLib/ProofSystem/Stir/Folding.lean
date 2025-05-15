/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Least Authority
-/

import ArkLib.Data.CodingTheory.FieldReedSolomon
import ArkLib.Data.CodingTheory.ProximityBound
import ArkLib.Data.CodingTheory.RelativeHammingDistance
import ArkLib.Data.CodingTheory.SmoothDomain

import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Probability.Distributions.Uniform
import Mathlib.RingTheory.MvPolynomial.Groebner

open SmoothIndex Polynomial ReedSolomon LinearMap

namespace Folding
variable {n : ℕ}
         {F : Type*} [Field F]
         {ι : Finset F}

/-! Section 4.4 in https://eprint.iacr.org/2024/390.pdf -/

/- 𝔽[X,Y] is not an Euclidean Domain, but fixing an order on monomials still allows
   to show existance of bivariate polynomials Q', Q ∈ 𝔽[X;Y] such that
   P = Q' * P' + Q for all P,P' ∈ 𝔽[X,Y] with P' having an invertible leading coefficient
   (which on a field is equivalent to P' not being the zero polynomial).

   This is MonomialOrder.div from Mathlib.RingTheory.MvPolynomial.Groebner

   Using the usual lexicographic order x₀ > x₁ is equal to proposition 6.3 in
   https://people.csail.mit.edu/madhu/papers/2005/rspcpp-full.pdf under the
   substitution z = x₀ and y = x₁, hence the following definition constructs
   Q ∈ 𝔽[Z,Y] with P(z,y) = Q'(z,y) * R(z,y) + Q(z,y)
-/


/-- Given `P, P' ∈ 𝔽[Z,Y]`, `P' ≠ 0`, computes `Q ∈ 𝔽[Z,Y]`,
with `P(z,y) = Q'(z,y) * P'(z,y) + Q(z,y)` for some `Q' ∈ 𝔽[Z,Y]` -/
noncomputable def modBivar (P P' : MvPolynomial (Fin 2) F)
    (hlg : IsUnit ((MonomialOrder.lex).leadingCoeff P')) : MvPolynomial (Fin 2) F :=
      -- Lexicographic order on `Fin 2`.
      let ord : MonomialOrder (Fin 2) := MonomialOrder.lex -- TODO: check if lex really is x₀ > x₁
      -- Wrap the single divisor into a family indexed by `Unit`.
      let b : Unit → MvPolynomial (Fin 2) F := fun _ => P'
      -- Unit leading-coeff proof for every index (there is only one).
      have hb : ∀ i : Unit, IsUnit (ord.leadingCoeff (b i)) := by
        intro _; simpa [b, ord] using hlg
      -- Apply Groebner-basis division:
      -- hdiv : ∃ Q', ∃ Q, P =  P' * Q' + Q ∧ (side conditions)
      have hdiv := ord.div (b := b) hb P
      -- Peel off the two nested existentials and return the chosen remainder `r`.
      Classical.choose (Classical.choose_spec hdiv)



/-- maps the univariate polynomial P∈𝔽[Z] to the bivariate polynomial P'∈ 𝔽[Z,Y] with
    P'(z,y) = P(z) -/
noncomputable def uni2bi (p : Polynomial F) : MvPolynomial (Fin 2) F :=
  Polynomial.eval₂ MvPolynomial.C (MvPolynomial.X 0) p

/-- Computes Q(z,y) with P(z) = Q'(z,y) * (y- q(z)) + Q(z,y) as in
    proposition 6.3 from https://people.csail.mit.edu/madhu/papers/2005/rspcpp-full.pdf -/
noncomputable def polyQ (P q : Polynomial F) : MvPolynomial (Fin 2) F :=
  -- Pbi(z,y):= P(z)
  let Pbi : MvPolynomial (Fin 2) F := uni2bi P
  -- P'(z,y) := (y - q(z))
  let P' : MvPolynomial (Fin 2) F := (MvPolynomial.X 1) - uni2bi q
  -- proof that leading coefficient f q is not zero
  have h_unit : IsUnit ((MonomialOrder.lex).leadingCoeff P') := sorry
  modBivar Pbi P' h_unit

/-- Helper For Readability: Evaluate a bivariate polynomial Q at (a, b) ∈ F×F -/
def evalBivar
  (Q : MvPolynomial (Fin 2) F) (a b : F) : F := MvPolynomial.eval (Fin.cases a (fun _ ↦ b)) Q

/-The STIR paper assumes that the polynomials f(.) and Q(q(.),.)
are fully determined by their evaluations on F, which is not
necessarily true for arbitrary polynomials of degrees larger
than |F|. So we include an assumption in what follows that q
has degree < |F| from which the uniqueness of f and Q can be
derived from their evaluation on F. Alternatively we could use
the identify of polynomials  f(.) = Q(q(.), .) instead -/
/-- Fact 4.6.1 in STIR -/

lemma exists_unique_bivariate
  [Fintype F] (q : Polynomial F) (hdeg_q_min : q.natDegree > 0)
  (hdeg_q_max : q.natDegree < Fintype.card F)
  (f : Polynomial F) :
    -- Q ∈ 𝔽[X,Y]
    ∃! Q : MvPolynomial (Fin 2) F,
      -- deg_x(Q) = Floor ( deg() / deg(q) )
      -- This is natrual number division towards zero, which is floor
      (MvPolynomial.degreeOf 0 Q = (Polynomial.natDegree f) / (Polynomial.natDegree q)) ∧
      -- deg_y(Q) < deg (q)
      (MvPolynomial.degreeOf 1 Q < Polynomial.natDegree q) ∧
      -- point‑wise equality on F: f(z) = Q(q(z), z)
      (∀ z : F, Polynomial.eval z f = evalBivar Q (Polynomial.eval z q) z) ∧
  (∀ t : ℕ, f.natDegree < t * q.natDegree → MvPolynomial.degreeOf 0 Q < t):=
  /- The proof can parallel `def polyQ` using the properties guranteed
  from MonomialOrder.div from Mathlib.RingTheory.MvPolynomial.Groebner -/
  by sorry

/-- Fact 4.6.2 in STIR-/
lemma degree_bound_bivariate
  {F  : Type*} [Field F] [Fintype F]
  (q : Polynomial F) (hdeg_q_min : q.natDegree > 0) (hdeg_q_max : q.natDegree < Fintype.card F)
  {t : ℕ}
  (Q : MvPolynomial (Fin 2) F)
  (hdegX : MvPolynomial.degreeOf 0 Q < t)
  (hdegY : MvPolynomial.degreeOf 1 Q < q.natDegree) :
  (MvPolynomial.eval₂Hom (Polynomial.C : F →+* Polynomial F)
      (fun i : Fin 2 => if i = 0 then q else Polynomial.X) Q).natDegree < t * q.natDegree :=
by sorry

/-- `polyFold(f, k r)` “folds” the polynomial `f` producing a new polynomial of deree  `< ‖f‖/k`.-/
noncomputable def polyFold
  [Fintype F] [DecidableEq F]
  (f : Polynomial F)
  (k : ℕ) (hk0 : 0 < k) (hkfin : k < Fintype.card F)
  (r : F): Polynomial F :=
    let q : Polynomial F := Polynomial.X ^ k
    let hdeg_q_min : q.natDegree > 0 := sorry
    let hdeg_q_max : q.natDegree < Fintype.card F := sorry
  -- choose the unique bivariate lift Q
    let Q : MvPolynomial (Fin 2) F := polyQ f q
    MvPolynomial.eval₂Hom
      (Polynomial.C : F →+* Polynomial F)
      (fun i : Fin 2 => if i = 0 then Polynomial.X else Polynomial.C r)
      Q

/-- For x ∈ L^k, p_x ∈ 𝔽[X] is the degree < k polynomial
where p_x(y) = f(y) for every y ∈ L such that y^k = x.-/
noncomputable def xPoly
  {F : Type*} [Field F] [DecidableEq F]
  (ι : Finset F)
  (f : ι → F)
  (k : ℕ)
  (x : powIndex ι k) : Polynomial F :=
    let S := powFiber ι k x
    Lagrange.interpolate
      S.attach
      Subtype.val
      fun i =>
        let hL : i.1 ∈ ι := (Finset.mem_filter.1 i.2).1
        f ⟨i.1, hL⟩




/-- Fold(f,k, α) : L^K → 𝔽;  Fold(f, k, α)(x) := p_x(α) -/
noncomputable def fold
  {F  : Type*} [Field F] [Fintype F] [DecidableEq F]
  {ι : Finset F}
  (f : ι → F)
  (k : ℕ)
  (α : F) : powIndex ι k → F :=
    fun x => (xPoly ι f k x).eval α

/-- min{∆(f, RSC[F, L, d]), 1 − B^⋆(ρ)} -/
noncomputable def foldingRange
  [Fintype F] [DecidableEq F]
  {ι : Finset F} {domain : ι ↪ F}
  {degree : ℕ}
  (C : code F ι domain degree)
  (f : ι → F) : ℝ :=
   min (δᵣ(f,C)) (1 - Bstar (rate C))

lemma folding
  [Fintype F] [DecidableEq F]
  {ι₁ : Finset F} {domain₁ : ι₁ ↪ F}
  {degree : ℕ} -- Can lean really deduce it?
  (k : ℕ) -- We might need an assumption that k is a factor of d
  (ι₂ : Finset F) (hι₂ : ι₂ = powIndex ι₁ k) {domain₂ : ι₂ ↪ F}
  (C1 : code F ι₁ domain₁ degree)
  (C2 : code F ι₂ domain₂ (degree / k)) (f : ι₁ → F)
  (δ : ℚ) (hδPos: δ > 0) (hδLt : δ < foldingRange C1 f) :
    (PMF.uniformOfFintype F).toOuterMeasure { r : F |
            δᵣ((fold f k r),C2) ≤ δ} > err' F (degree/k) (rate C1) δ k
            -- Double check if this really is C1.rate not C2.rate
    := by sorry

end Folding
