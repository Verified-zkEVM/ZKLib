-- This file is from Bolton Bailey

import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Finset.Basic
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Algebra.Ring.InjSurj
import Mathlib.Algebra.Tropical.Basic
import Mathlib.Algebra.Polynomial.Degree.Definitions
import Lean.Data.RBMap

def List.matchLength (a : List α) (b : List α) (unit : α) : List α × List α :=
  if a.length < b.length then
    (a ++ .replicate (b.length - a.length) unit, b)
  else
    (a, b ++ .replicate (a.length - b.length) unit)

section Polynomial

/-- A type analogous to `Polynomial` that supports computable operations. This polynomial is represented internally as a list of coefficients. For example the list `[1,2,3]` represents the polynomial `1 + 2x + 3x^2`.
 -/
def Polynomial' (R : Type) := List R

instance inhabitedPolynomial' (R : Type) [Inhabited R] : Inhabited (Polynomial' R) := ⟨[Inhabited.default]⟩
instance (R : Type) [DecidableEq R] : DecidableEq (Polynomial' R) := List.hasDecEq

def Polynomial'.mk {R : Type} [Semiring R] (l : List R) : Polynomial' R := l

def Polynomial'.toList {R : Type} [Semiring R] (p : Polynomial' R) : List R := p

/-- Evaluates a polynomial at a given value. -/
def Polynomial'.eval {R : Type} [Zero R] [Add R] [Mul R] [HPow R ℕ R] (r : R) (p : Polynomial' R) : R :=
  (p.enum.map (fun ⟨i, a⟩ => a * r ^ i)).sum

def Polynomial'.eval₂ {R S₁ : Type} [Semiring R] [Semiring S] (f : R → S) (x : S) (p : Polynomial' R) : S :=
  (p.enum.map (fun ⟨i, a⟩ => f a * x ^ i)).sum


def Polynomial'.C {R : Type} [Semiring R] (r : R) : Polynomial' R := [r]

def Polynomial'.X {R : Type} [Semiring R] : Polynomial' R := [0, 1]

def Polynomial'.add {R : Type} [Semiring R] (p q : Polynomial' R) : Polynomial' R :=
  let ⟨p', q'⟩ := List.matchLength p q 0
  List.zipWith (· + ·) p' q'

def Polynomial'.smul {R : Type} [Semiring R] (r : R) (p : Polynomial' R) : Polynomial' R :=
  List.map (fun a => r * a) p

def Polynomial'.nsmul {R : Type} [Semiring R] (n : ℕ) (p : Polynomial' R) : Polynomial' R :=
  List.map (fun a => n * a) p

def Polynomial'.zsmul {R : Type} [Ring R] (n : ℤ) (p : Polynomial' R) : Polynomial' R :=
  List.map (fun a => n * a) p

def Polynomial'.mul {R : Type} [Semiring R] (p q : Polynomial' R) : Polynomial' R :=
  (p.enum).foldl (fun a ⟨n, b⟩ => a.add (Polynomial'.mk (((List.replicate n (0 : R))) ++ (Polynomial'.smul b q).toList))) []

def Polynomial'.neg {R : Type} [Ring R] (p : Polynomial' R) : Polynomial' R := List.map (· * -1) p

def Polynomial'.sub {R : Type} [Ring R] (p q : Polynomial' R) : Polynomial' R := p.add q.neg

def Polynomial'.pow {R : Type} [Semiring R] (p : Polynomial' R) (n : Nat) : Polynomial' R := List.foldl (fun a b => a.mul p) (Polynomial'.C 1) (List.replicate n p) -- TODO more complicated than it needs to be

instance (R : Type) [Semiring R] : Inhabited (Polynomial' R) := ⟨[]⟩


instance {R : Type} [Semiring R] : Zero (Polynomial' R) := ⟨[]⟩
instance {R : Type} [Semiring R] : One (Polynomial' R) := ⟨Polynomial'.C 1⟩
instance {R : Type} [Semiring R] : Add (Polynomial' R) := ⟨Polynomial'.add⟩
instance {R : Type} [Semiring R] : Mul (Polynomial' R) := ⟨Polynomial'.mul⟩
instance {R : Type} [Ring R] : Neg (Polynomial' R) := ⟨Polynomial'.neg⟩
instance {R : Type} [Ring R] : Sub (Polynomial' R) := ⟨Polynomial'.sub⟩
instance {R : Type} [Semiring R] : Pow (Polynomial' R) Nat := ⟨Polynomial'.pow⟩
instance {R : Type} [Semiring R] : SMul ℕ (Polynomial' R) := ⟨Polynomial'.nsmul⟩
instance {R : Type} [Ring R] : SMul ℤ (Polynomial' R) := ⟨Polynomial'.zsmul⟩
instance {R : Type} [Semiring R] : NatCast (Polynomial' R) := ⟨fun n => Polynomial'.C (n : R)⟩
instance {R : Type} [Ring R] : IntCast (Polynomial' R) := ⟨fun n => Polynomial'.C (n : R)⟩


noncomputable def Polynomial'.toPoly {R : Type} [Semiring R] (p : Polynomial' R) : Polynomial R :=
  Polynomial'.eval₂
    (R := R) (S₁ := Polynomial R)
    (fun r : R => Polynomial.C r) (Polynomial.X) p

def Polynomial'.degreeBound {R : Type} [Semiring R] (p : Polynomial' R) : WithBot Nat :=
  match p.length with
  | 0 => ⊥
  | .succ n => n

def Polynomial'.natDegreeBound {R : Type} [Semiring R] (p : Polynomial' R) : Nat :=
  (degreeBound p).getD 0

def Polynomial'.leadingCoeff {R : Type} [Zero R] (p : Polynomial' R) : R :=
  match p with
  | [] => 0
  | a :: [] => a
  | _ :: as => leadingCoeff as

def Polynomial'.Monic {R : Type} [One R] (p : Polynomial' R) : Prop :=
  match p with
  | [] => False
  | a :: [] => a = 1
  | _ :: as => Monic as

def Polynomial'.trim {R : Type} [Semiring R] (p : Polynomial' R) : Polynomial' R :=
  match p with
  | [] => []
  | _ :: [] => []
  | a :: as => a :: trim as


def Polynomial'.divModByMonic_aux {R : Type} [Field R] (p : Polynomial' R) (q : Polynomial' R) :
    Polynomial' R × Polynomial' R :=
  go (p.length - q.length) p q
where
  go : Nat -> Polynomial' R -> Polynomial' R -> Polynomial' R × Polynomial' R
  | 0, p, q => ⟨0, p⟩
  | n+1, p, q =>
      let k := p.length - q.length -- k should equal n, this is technically unneeded
      let q' := C p.leadingCoeff * (q * Polynomial'.X.pow k)
      let p' := (p - q').trim
      let (e, f) := go n p' q
      -- p' = q * e + f
      -- Thus p = p' + q' = q * e + f + p.leadingCoeff * q * X^n = q * (e + p.leadingCoeff * X^n) + f
      ⟨e + C p.leadingCoeff * X^k, f⟩




def Polynomial'.divByMonic {R : Type} [Field R] (p : Polynomial' R) (q : Polynomial' R) :
    Polynomial' R :=
  (divModByMonic_aux p q).1

def Polynomial'.modByMonic {R : Type} [Field R] (p : Polynomial' R) (q : Polynomial' R) :
    Polynomial' R :=
  (divModByMonic_aux p q).2

def Polynomial'.div {R : Type} [Field R] (p q : Polynomial' R) : Polynomial' R := (C (q.leadingCoeff)⁻¹ • p).divByMonic (C (q.leadingCoeff)⁻¹ * q)

def Polynomial'.mod {R : Type} [Field R] (p q : Polynomial' R) : Polynomial' R := (C (q.leadingCoeff)⁻¹ • p).modByMonic (C (q.leadingCoeff)⁻¹ * q)


instance {R : Type} [Field R] : Div (Polynomial' R) := ⟨Polynomial'.div⟩
instance {R : Type} [Field R] : Mod (Polynomial' R) := ⟨Polynomial'.mod⟩

def Polynomial'.divX {R : Type} [Semiring R] (p : Polynomial' R) : Polynomial' R := p.toList.tail

-- unique polynomial of degree n that has nodes at ω^i for i = 0, 1, ..., n-1
def Lagrange.nodal' {F : Type} (n : ℕ) (ω : F) : Polynomial' F := [] -- XXX TODO implement

/--
This function produces the polynomial which is of degree n and is equal to r i at ω^i for i = 0, 1, ..., n-1.
-/
def Lagrange.interpolate' {F : Type} [Semiring F] (n : ℕ) (ω : F) (r : Fin n → F) : Polynomial' F := [] -- XXX TODO implement


section Tropical
/-- This section courtesy of Junyan Xu -/

instance : LinearOrderedAddCommMonoidWithTop (OrderDual (WithBot ℕ)) where
  __ : LinearOrderedAddCommMonoid (OrderDual (WithBot ℕ)) := inferInstance
  __ : Top (OrderDual (WithBot ℕ)) := inferInstance
  le_top _ := bot_le (α := WithBot ℕ)
  top_add' x := WithBot.bot_add x


noncomputable instance (R) [Semiring R] : Semiring (Polynomial R × Tropical (OrderDual (WithBot ℕ))) := inferInstance

noncomputable instance (R) [CommSemiring R] : CommSemiring (Polynomial R × Tropical (OrderDual (WithBot ℕ))) := inferInstance


def TropicallyBoundPoly (R) [Semiring R] : Subsemiring (Polynomial R × Tropical (OrderDual (WithBot ℕ))) where
  carrier := {p | p.1.degree ≤ OrderDual.ofDual p.2.untrop}
  mul_mem' {p q} hp hq := (p.1.degree_mul_le q.1).trans (add_le_add hp hq)
  one_mem' := Polynomial.degree_one_le
  add_mem' {p q} hp hq := (p.1.degree_add_le q.1).trans (max_le_max hp hq)
  zero_mem' := Polynomial.degree_zero.le


noncomputable def Polynomial'.toTropicallyBoundPolynomial {R : Type} [Semiring R] (p : Polynomial' R) :
    Polynomial R × Tropical (OrderDual (WithBot ℕ)) :=
  (Polynomial'.toPoly p, Tropical.trop (OrderDual.toDual (Polynomial'.degreeBound p)))

def degBound (b: WithBot ℕ) : ℕ := match b with
  | ⊥ => 0
  | some n => n + 1

def TropicallyBoundPolynomial.toPolynomial' {R : Type} [Semiring R] (p : Polynomial R × Tropical (OrderDual (WithBot ℕ))) :
    Polynomial' R :=
  match p with
  | (p, n) => List.range (degBound (n.untrop : WithBot ℕ)) |>.map (fun i => p.coeff i)

noncomputable def Equiv.Polynomial'.TropicallyBoundPolynomial {R : Type} [Semiring R] :
    Polynomial' R ≃+* Polynomial R × Tropical (OrderDual (WithBot ℕ)) where
      toFun := Polynomial'.toTropicallyBoundPolynomial
      invFun := TropicallyBoundPolynomial.toPolynomial'
      left_inv := by sorry
      right_inv := by sorry
      map_mul' := by sorry
      map_add' := by sorry

end Tropical


end Polynomial
