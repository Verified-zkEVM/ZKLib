/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Least Authority
-/

import ArkLib.Data.CodingTheory.FieldReedSolomon
import ArkLib.Data.CodingTheory.ListDecodeability
import ArkLib.Data.CodingTheory.RelativeHammingDistance
import ArkLib.Data.CodingTheory.SmoothDomain
import ArkLib.ProofSystem.Stir.ProximityBound

import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Probability.Distributions.Uniform
import Mathlib.RingTheory.MvPolynomial.Groebner

open SmoothDomain Polynomial ReedSolomon LinearMap Finset ListDecodable

namespace Folding
variable {n : ℕ}
         {F : Type } [Field F] [Fintype F]
         {ι : Finset F} {domain : ι → F}

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



/-- The STIR paper assumes that the polynomials fPoly(.) and Q(qPoly(.),.) are
    fully determined by their evaluations on F. This is not necessarily true
    for arbitrary polynomials of degrees larger than |F|. So we include an
    assumption in what follows that qPoly has degree < |F| from which the
    uniqueness of fPoly and Q can be derived from their evaluation on F.
    Alternatively we could use the identity of polynomials
    fPoly(.) = Q(qPoly(.), .) instead.

    Below we present Fact 4.6.1 from STIR -/
lemma exists_unique_bivariate
  (qPoly : Polynomial F) (hdeg_q_min : qPoly.natDegree > 0)
  (hdeg_q_max : qPoly.natDegree < Fintype.card F) (fPoly : Polynomial F) :
    -- Q ∈ 𝔽[X,Y]
    ∃! Q : MvPolynomial (Fin 2) F,
      -- deg_x(Q) = Floor ( deg(fPoly) / deg(qPoly) )
      -- This is natural number division towards zero, which is floor
      (MvPolynomial.degreeOf 0 Q = (Polynomial.natDegree fPoly) / (Polynomial.natDegree qPoly)) ∧
      -- deg_y(Q) < deg (q)
      (MvPolynomial.degreeOf 1 Q < Polynomial.natDegree qPoly) ∧
      -- point‑wise equality on F: f(z) = Q(q(z), z)
      (∀ z : F, Polynomial.eval z fPoly = evalBivar Q (Polynomial.eval z qPoly) z) ∧
      (∀ t : ℕ, fPoly.natDegree < t * qPoly.natDegree → MvPolynomial.degreeOf 0 Q < t) :=
  /- The proof can follow `def polyQ` using the properties guranteed
  from MonomialOrder.div from Mathlib.RingTheory.MvPolynomial.Groebner -/
  by sorry

/-- Fact 4.6.2 in STIR-/
lemma degree_bound_bivariate
  (qPoly : Polynomial F)
  (hdeg_q_min : qPoly.natDegree > 0)
  (hdeg_q_max : qPoly.natDegree < Fintype.card F)
  {t : ℕ} (Q : MvPolynomial (Fin 2) F)
  (hdegX : MvPolynomial.degreeOf 0 Q < t)
  (hdegY : MvPolynomial.degreeOf 1 Q < qPoly.natDegree) :
  (MvPolynomial.eval₂Hom (Polynomial.C : F →+* Polynomial F)
      (fun i : Fin 2 => if i = 0 then qPoly else Polynomial.X) Q).natDegree < t * qPoly.natDegree :=
    by sorry

/-- `polyFold(f, k r)` “folds” the polynomial `f` producing a new polynomial of deree  `< ‖f‖/k`.-/
noncomputable def polyFold
  [DecidableEq F] (fPoly : Polynomial F)
  (k : ℕ) (hk0 : 0 < k) (hkfin : k < Fintype.card F)
  (r : F): Polynomial F :=
    let qPoly : Polynomial F := Polynomial.X ^ k
    let hdeg_q_min : qPoly.natDegree > 0 := sorry
    let hdeg_q_max : qPoly.natDegree < Fintype.card F := sorry
  -- choose the unique bivariate lift Q
    let Q : MvPolynomial (Fin 2) F := polyQ fPoly qPoly
    MvPolynomial.eval₂Hom
      (Polynomial.C : F →+* Polynomial F)
      (fun i : Fin 2 => if i = 0 then Polynomial.X else Polynomial.C r) Q

/-- For x ∈ L^k, p_x ∈ 𝔽[X] is the degree < k polynomial
where p_x(y) = f(y) for every y ∈ L such that y^k = x.-/
noncomputable def xPoly
  [DecidableEq F] (f : ι → F) (domain : ι ↪ F) (k : ℕ) (x : indexPow ι k) : Polynomial F :=
    let powFiber := powFiber ι k x -- f⁻¹(x) for the surjection x ∈ ιᵏ
    let fiberDomain := fiber (pow domain k) x -- The fiber domain `f⁻¹(x) ↪ F`
    let g : {y // y ∈ powFiber} → F :=
    fun y => f ⟨y.val, (Finset.mem_filter.mp y.prop).left⟩
    (Lagrange.interpolate univ fiberDomain) g


/-- Fold(f,k,α) : L^K → 𝔽;  Fold(f, k, α)(x) := p_x(α) -/
noncomputable def fold
  [DecidableEq F] (domain : ι ↪ F) (f : ι → F) (k : ℕ) (α : F) : indexPow ι k → F :=
    fun x => (xPoly f domain k x).eval α

/-- min{∆(f, RSC[F, L, d]), 1 − B^⋆(ρ)} -/
noncomputable def foldingRange
   (degree : ℕ) [Nonempty ι] (domain : ι ↪ F) (f : ι → F)  : ℝ :=
    let C : Set (ι → F) := code F ι domain degree
    min δᵣ(f, C) (1 - Bstar (rate degree ι))

lemma folding
  [DecidableEq F] [Nonempty ι]
  (domain : ι ↪ F) (f : ι → F) (k : ℕ) (x : indexPow ι k)
  [Nonempty {x : F // x ∈ indexPow ι k}]
  {degree : ℕ} (δ : ℚ) (hδPos : δ > 0)
  (hδLt : δ < foldingRange degree domain f) :
  (PMF.uniformOfFintype F).toOuterMeasure { r : F |
    δᵣ((fold domain f k r), ↑(code F (indexPow ι k) (pow domain k) (degree / k))) ≤ δ
  } > err' F (degree / k) (rate degree ι) δ k :=
by sorry





end Folding
