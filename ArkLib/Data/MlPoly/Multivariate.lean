/-
Copyright (c) 2024 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/


import Mathlib.Data.Finset.Basic

section MvPoly

-- multivariate polynomials without explicit bound on number of variables
def MvPoly'' (R : Type) := List (R × List ℕ)

def MvPoly' (R : Type) (n : ℕ) := List (R × List (Fin n))

def MvPoly'.C {R : Type} {n : ℕ} [CommSemiring R] (r : R) : MvPoly' R n := [(r, [])]
def MvPoly'.X {R : Type} {n : ℕ} [CommSemiring R] (s : (Fin n)) : MvPoly' R n := [(1, [s])]


def MvPoly'.eval {R : Type} {n : ℕ} [Zero R] [Add R] [Mul R] (f : (Fin n) → R) (p : MvPoly' R n) : R := 0 -- TODO implement
def MvPoly'.eval₂ {R S₁ : Type} {n : ℕ} [CommSemiring R] [Zero S₁] [One S₁] [Add S₁] [Mul S₁] (f : R → S₁) (g : (Fin n) → S₁) (p : MvPoly' R n) : S₁ :=
  (p.map (fun ⟨r, s⟩ => (f r * (s.map g).prod))).sum


def MvPoly'.add {R : Type} {n : ℕ} [CommSemiring R] (p q : MvPoly' R n) : MvPoly' R n := List.append p q
def MvPoly'.mul {R : Type} {n : ℕ} [CommSemiring R] (p q : MvPoly' R n) : MvPoly' R n := List.foldl (fun a b => a.add (List.map (fun ⟨r, s⟩ => (r * b.1, s ++ b.2)) q)) [] p
def MvPoly'.neg {R : Type} {n : ℕ} [CommRing R] (p : MvPoly' R n) : MvPoly' R n := List.map (fun ⟨r, s⟩ => (-r, s)) p
def MvPoly'.sub {R : Type} {n : ℕ} [CommRing R] (p q : MvPoly' R n) : MvPoly' R n := p.add q.neg
def MvPoly'.pow {R : Type} {n : ℕ} [CommSemiring R] (p : MvPoly' R n) (n' : Nat) : MvPoly' R n := List.foldl (fun a b => a.mul p) (MvPoly'.C 1) (List.replicate n' p)

instance {R : Type} {n : ℕ} [CommSemiring R] : Zero (MvPoly' R n) := ⟨[]⟩
instance {R : Type} {n : ℕ} [CommSemiring R] : Add (MvPoly' R n) := ⟨MvPoly'.add⟩
instance {R : Type} {n : ℕ} [CommSemiring R] : Mul (MvPoly' R n) := ⟨MvPoly'.mul⟩
instance {R : Type} {n : ℕ} [CommRing R] : Neg (MvPoly' R n) := ⟨MvPoly'.neg⟩
instance {R : Type} {n : ℕ} [CommRing R] : Sub (MvPoly' R n) := ⟨MvPoly'.sub⟩
instance {R : Type} {n : ℕ} [CommSemiring R] : Pow (MvPoly' R n) Nat := ⟨MvPoly'.pow⟩

end MvPoly
