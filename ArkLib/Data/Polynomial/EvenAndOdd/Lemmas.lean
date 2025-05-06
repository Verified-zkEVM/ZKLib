/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: František Silváši, Julian Sutherland, Ilia Vlasov
-/
import ArkLib.Data.Polynomial.EvenAndOdd.Defs

variable {F: Type} [NonBinaryField F]

private noncomputable def fₑ' (f : Polynomial F) : Polynomial F :=
  match f with
  | ⟨⟨supp, f, pr⟩⟩ => ⟨⟨erase_odd supp, fun n => if Even n then f n else 0, by {
    intro a
    aesop
  }⟩⟩

@[simp]
private lemma fₑ'_coeffs {f : Polynomial F} {n : ℕ}:
    (fₑ' f).coeff n = if Even n then f.coeff n else 0 := by
  rcases f with ⟨⟨supp, g, h⟩⟩
  simp [fₑ']

private noncomputable def x_times_fₒ' (f : Polynomial F) : Polynomial F :=
  match f with
  | ⟨⟨supp, f, pr⟩⟩ => ⟨⟨erase_even supp, fun n => if Odd n then f n else 0, by {
      intro a
      aesop
    }⟩⟩

@[simp]
private lemma x_times_fₒ'_coeff {f : Polynomial F} {n : ℕ}:
    (x_times_fₒ' f).coeff n = if Odd n then f.coeff n else 0 := by
  rcases f with ⟨⟨supp, g, h⟩⟩
  simp [x_times_fₒ']

private noncomputable def fₒ' (f : Polynomial F) : Polynomial F :=
  match f with
  | ⟨⟨supp, f, pr⟩⟩ => ⟨⟨
      shift_left (erase_even supp),
      fun n => if Even n then f (n + 1) else 0, by {
        intro a
        simp [Nat.odd_add_one]
        aesop
    }⟩⟩

@[simp]
private lemma fₒ'_coeff {f : Polynomial F} {n : ℕ} :
    (fₒ' f).coeff n = if Even n then f.coeff (n + 1) else 0 := by
  rcases f with ⟨⟨supp, g, h⟩⟩
  simp [fₒ']

private lemma x_times_fₒ'_eq_x_times_fₒ' {f : Polynomial F} :
    Polynomial.X * (fₒ' f) = x_times_fₒ' f := by
  apply Polynomial.ext
  intro n
  rcases n with _ | n <;> try simp [Nat.odd_add_one]

private lemma really_glorious_lemma {f f' : Polynomial F} (h : 2 * f = 2 * f') :
    f = f' := by
    apply Polynomial.ext
    intro n
    have h_2 : (2 * f).coeff n = (2 * f').coeff n := by simp [h]
    simp at h_2
    aesop

private lemma fₑ_eq_fₑ' {f : Polynomial F} : fₑ f = fₑ' f := by
  apply really_glorious_lemma
  rw [fₑ_by_2]
  apply Polynomial.ext
  intro n
  simp [coeffs_of_comp_minus_x]
  by_cases hpar : Even n <;> try simp [hpar]
  ring_nf

private lemma fₒ_eq_fₒ'_aux' {f : Polynomial F}
  : (f - f.comp (-Polynomial.X)) = (Polynomial.C 2) * x_times_fₒ' f := by
  apply Polynomial.ext
  intro n
  simp [coeffs_of_comp_minus_x]
  by_cases hpar : Even n
  · simp [hpar]
    rw [←Nat.not_odd_iff_even] at hpar
    simp [hpar]
  · simp [hpar]
    simp only [← Nat.not_odd_iff_even, Decidable.not_not] at hpar
    simp [hpar]
    ring_nf

private lemma fₒ_eq_fₒ' {f : Polynomial F} : fₒ f = fₒ' f := by
  simp [fₒ]
  rw [fₒ_eq_fₒ'_aux'
  , ←x_times_fₒ'_eq_x_times_fₒ'
  , ←mul_assoc
  , ←Polynomial.C_mul]
  simp [Polynomial.mul_divByMonic_cancel_left]

@[simp]
lemma fₒ_coeff {f : Polynomial F} {n : ℕ} :
    (fₒ f).coeff n = if Even n then f.coeff (n + 1) else 0 := by
  simp [fₒ_eq_fₒ']

@[simp]
lemma fₑ_coeff {f : Polynomial F} {n : ℕ} :
    (fₑ f).coeff n = if Even n then f.coeff n else 0 := by
  simp [fₑ_eq_fₑ']

lemma f_eq_fₑ_plus_x_fₒ {f : Polynomial F} :
  f = fₑ f + Polynomial.X * fₒ f := by
  apply Polynomial.ext
  intro n
  simp
  rw [mul_comm Polynomial.X]
  rcases n with _ | n <;> try simp
  by_cases hPar : Even (n + 1) <;> try simp [hPar]
  · rw [Nat.even_add_one] at hPar
    simp [hPar]
  · rw [Nat.even_add_one] at hPar
    simp at hPar
    simp [hPar]

lemma fₒ_even {f : Polynomial F} :
    EvenPoly (fₒ f) := by
  intro n hOdd
  simp
  intro h
  rw [←Nat.not_even_iff_odd] at hOdd
  tauto

lemma fₑ_even {f : Polynomial F} :
    EvenPoly (fₑ f) := by
  intro n hOdd
  simp
  intro h
  rw [←Nat.not_even_iff_odd] at hOdd
  tauto

lemma evenize_eq_comp_x_squared {f : Polynomial F} :
    evenize f = f.comp (Polynomial.X * Polynomial.X) := by
  apply Polynomial.ext
  intro n
  simp [comp_x_square_coeff]

lemma deevenize_comp_x_squared {f : Polynomial F} (hEven : EvenPoly f):
    (deevenize f).comp (Polynomial.X * Polynomial.X) = f := by
  apply Polynomial.ext
  intro n
  rw [comp_x_square_coeff]
  simp
  by_cases hPar : Even n <;> simp [hPar]
  · rw [Nat.mul_div_eq_iff_dvd.2 (by {
      rw [Nat.even_iff] at hPar
      omega
    })]
  · symm ; apply hEven
    rw [←Nat.not_even_iff_odd]
    exact hPar

lemma evenize_is_even {f : Polynomial F} :
    EvenPoly (evenize f) := by
  intros n hOdd
  simp
  intros hEven
  rw [←Nat.not_odd_iff_even] at hEven
  tauto

lemma eq_evenize_deevenize {f : Polynomial F} (hEven : EvenPoly f):
    evenize (deevenize f) = f := by
  apply Polynomial.ext
  intro n
  simp
  by_cases hPar : Even n <;> simp [hPar]
  · rw [Nat.mul_div_eq_iff_dvd.2 (by {
      rw [Nat.even_iff] at hPar
      omega
    })]
  · rw [hEven _ (Nat.not_even_iff_odd.1 hPar)]

lemma even_eval {f : Polynomial F} {s : F} (hEven : EvenPoly f) :
  f.eval (-s) = f.eval s := by
  rw [←eq_evenize_deevenize (f := f) hEven,
      evenize_eq_comp_x_squared]
  simp [Polynomial.eval_comp, Polynomial.eval_mul]

lemma deevenize_evenize {f : Polynomial F} :
    deevenize (evenize f) = f := by
  apply Polynomial.ext
  simp

lemma evenize_eval {f : Polynomial F} {s : F}:
    (evenize f).eval s = f.eval (s * s) := by
  rw [evenize_eq_comp_x_squared]
  simp [Polynomial.eval_comp, Polynomial.eval_mul]

lemma fₑ_x_eval_eq {f : Polynomial F} {s : F} :
    (fₑ_x f).eval (s * s) = (fₑ f).eval s := by
  unfold fₑ_x
  rw [←eq_evenize_deevenize (f := fₑ f)
      , evenize_eval
      , deevenize_evenize]
  exact fₑ_even

lemma fₒ_x_eval_eq {f : Polynomial F} {s : F} :
    (fₒ_x f).eval (s * s) = (fₒ f).eval s := by
  unfold fₒ_x
  rw [←eq_evenize_deevenize (f := fₒ f)
      , evenize_eval
      , deevenize_evenize]
  exact fₒ_even
