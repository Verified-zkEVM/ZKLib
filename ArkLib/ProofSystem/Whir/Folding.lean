/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Least Authority
-/

import ArkLib.Data.CodingTheory.RelativeHammingDistance
import ArkLib.Data.CodingTheory.SmoothReedSolomon
import ArkLib.ProofSystem.Whir.BlockRelDistanceGeneric
import ArkLib.ProofSystem.Whir.GenMutualCorrAgreement

namespace Fold

open Vector Finset BlockRelDistance
variable {F : Type*} [Field F] {ι : Type*} [Pow ι ℕ]


/--∃ x ∈ S, such that `y = x ^ 2^(k+1)`. extract_x returns `z = x ^ 2^k` such that `y = z^2`.-/
noncomputable def extract_x
  (S : Finset ι) (φ : ι ↪ F) (k : ℕ) (y : indexPowT S φ (k + 1)) : indexPowT S φ k :=
  let x := Classical.choose y.property
  let hx := Classical.choose_spec y.property
  let z := (φ x) ^ (2^k)
  ⟨z, ⟨x, hx.1, rfl⟩⟩

/--Given a function `f : LpowT S k → F`, foldf operates on two inputs:
  element `y ∈ LpowT S (k+1)`, hence `∃ x ∈ S, s.t. y = x ^ 2^(k+1)` and `α ∈ F`.
  It obtains the square root of y as `xPow := extract_x S k y` -- here xPow is of the form x ^ 2^k.
  It returns the value `f(xPow) + f(- xPow)/2 + α • (f(xPow) - f(- xPow))/ 2•xPow`. -/
noncomputable def foldf (S : Finset ι) (φ : ι ↪ F)
  {k : ℕ} [ Neg (indexPowT S φ k) ] (y : indexPowT S φ (k+1))
  (f : indexPowT S φ k → F) (α : F) : F :=
  let xPow := extract_x S φ k y
  let fx := f xPow
  let f_negx := f (-xPow)
  (fx + f_negx) / 2 + α • ((fx - f_negx) / (2 * (xPow.val : F)))

/-- Helper to recursively descend to base level 0 by repeated extraction. -/
noncomputable def descend_to_0
  (S : Finset ι) (φ : ι ↪ F) : ∀ (j : ℕ), indexPowT S φ j → indexPowT S φ 0
| 0, x => x
| (j+1), y => descend_to_0 S φ j (extract_x S φ j y)

/--the function fold_k_core runs a recursion, for i, a vector `αs` of size (i+1) and
  a vector of (i+1) functions `fᵢ: LpowT S i → F`
  For i = 0, fold_k_core returns f₀ evaluated at x ∈ S, such that x^2 = y.
  For i = (i'+1) ≠ 0,
    αs is parsed as α || αs', where αs' is of size i
    function `fk : LpowT S i → F` is obtained by making a recursive call to
      `fold_k_core` on input `αs'`
    we obtain the final function `LpowT S (i+1) → F` by invoking `foldf` with `fk` and `α`.-/
noncomputable def fold_k_core {S : Finset ι} {φ : ι ↪ F} (f : (indexPowT S φ 0) → F)
  [∀ i : ℕ, Neg (indexPowT S φ i)] : (i : ℕ) → (αs : Vector F i) →
    ((j : Fin i) → indexPowT S φ j → F) → indexPowT S φ i → F
| 0, _, _ => fun x₀ => f x₀
| k+1, αs, fi => fun y =>
    let α := αs.head
    let αs' := αs.tail
    let fi' : (j : Fin k) → indexPowT S φ j → F :=
      fun j xj => fi (Fin.castSucc j) xj
    let fk := fold_k_core f k αs' fi'
    foldf S φ y fk α


/--fold_k takes a vector `αs` of size (k+1) and a vector of (k+1) functions `fⱼ : Lpowt S j → F`
  and returns a function `Fold : LpowT S (k+1) → F` -/
noncomputable def fold_k
  {S : Finset ι} {φ : ι ↪ F} {k : ℕ}
  [∀ j : ℕ, Neg (indexPowT S φ j)]
  (f : (indexPowT S φ 0) → F) (αs : Vector F k) : indexPowT S φ k → F :=
  let fi : (j : Fin k) → indexPowT S φ j → F :=
    fun j x => f (descend_to_0 S φ j x)
  fold_k_core f k αs fi



noncomputable def fold_k_set
  {S : Finset ι} {φ : ι ↪ F} {k : ℕ}
  [∀ j : ℕ, Neg (indexPowT S φ j)]
  (set : Set ((indexPowT S φ 0) → F)) (αs : Vector F k) : Set (indexPowT S φ k → F) :=
    { g | ∃ f ∈ set, g = fold_k f αs }

namespace FoldingLemmas

open CorrelatedAgreement SmoothDomain ReedSolomon NNReal Generator ListDecodable
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
         {ι : Type*} [Fintype ι] [Pow ι ℕ] [DecidableEq ι]

class GenMutualCorrParams (S : Finset ι) (φ : ι ↪ F) (k : ℕ) where
  m : ℕ

  inst1 : ∀ i : Fin (k+1), Fintype (indexPowT S φ i)
  inst2 : ∀ i : Fin (k+1), Nonempty (indexPowT S φ i)
  inst3 : ∀ i : Fin (k+1), DecidableEq (indexPowT S φ i)

  φ_i : ∀ i : Fin (k+1), (indexPowT S φ i) ↪ F
  inst4 : ∀ i : Fin (k+1), Smooth (φ_i i)

  Genᵢ : ∀ i : Fin (k+1), ProximityGenerator (indexPowT S φ i) F
  Gen_αᵢ : ∀ i : Fin (k+1), ProximityGenerator (indexPowT S φ i) F
  hgen : ∀ i : Fin (k+1), ∀ α : F, Gen_αᵢ i = proximityGenerator_α (Genᵢ i) α (φ_i i) m
  BStarᵢ : ∀ i : Fin (k+1), (Set (indexPowT S φ i → F)) → ℕ → ℝ≥0
  errStarᵢ : ∀ i : Fin (k+1), (Set (indexPowT S φ i → F)) → ℕ → ℝ≥0 → ℝ≥0
  h : ∀ i : Fin (k+1), genMutualCorrAgreement (Gen_αᵢ i)
        (BStarᵢ i (Gen_αᵢ i).C (Gen_αᵢ i).l)
        (errStarᵢ i (Gen_αᵢ i).C (Gen_αᵢ i).l)


--Folding preserves list decoding
theorem folding_listdecoding_if_genMutualCorrAgreement
  {S : Finset ι} {φ : ι ↪ F} {k m j : ℕ} [Smooth φ]
  {S' : Finset (indexPowT S φ 0)} {φ' : (indexPowT S φ 0) ↪ F}
  [∀ i : ℕ, Fintype (indexPowT S φ i)] [DecidableEq (indexPowT S φ 0)] [Smooth φ']
  [h : ∀ {f : (indexPowT S φ 0) → F}, DecidableBlockDisagreement 0 k f S' φ']
  [∀ i : ℕ, Neg (indexPowT S φ i)]
  {C : Set ((indexPowT S φ 0) → F)} (hcode : C = smoothCode F (indexPowT S φ 0) φ' m) (hLe : k ≤ m)
  {GenFunₐ : F → Vector F k} {δ : ℝ≥0}
  {params : GenMutualCorrParams S φ k} :
    let _ : ∀ j : Fin (k + 1), Fintype (indexPowT S φ j) := params.inst1
    let _ : ∀ j : Fin (k + 1), Nonempty (indexPowT S φ j) := params.inst2
    let _ : ∀ j : Fin (k + 1), DecidableEq (indexPowT S φ j) := params.inst3
    let _ : ∀ j : Fin (k + 1), Smooth (params.φ_i j) := params.inst4
    let _ : Fintype (indexPowT S φ k) := params.inst1 ⟨k, Nat.lt_succ_self _⟩

    Pr_{α ← F} [  ∀ {f : (indexPowT S φ 0) → F}
                  (hδLe : δ ≤ 1 - Finset.univ.sup (fun j => params.BStarᵢ j (params.Gen_αᵢ j).C 2)),

                    let listBlock : Set ((indexPowT S φ 0) → F) := Λᵣ(0, k, f, S', C, hcode, δ)
                    let vec_α := GenFunₐ α
                    let fold := fold_k f vec_α
                    let foldSet := fold_k_set listBlock vec_α
                    let kFin : Fin (k + 1) := ⟨k, sorry⟩
                    let Cₖ := (params.Gen_αᵢ kFin).C
                    let listHamming := relHammingBall Cₖ fold δ

                    foldSet ≠ listHamming
                ] ≤ (∑ i : Fin (k+1), params.errStarᵢ i (params.Gen_αᵢ i).C 2 δ) := by sorry


lemma folding_preserves_listdecoding_base
  {S : Finset ι} {k m : ℕ} {φ : ι ↪ F} [Smooth φ] {δ : ℝ≥0}
  {S_0 : Finset (indexPowT S φ 0)} {S_1 : Finset (indexPowT S φ 1)}
  {φ_0 : (indexPowT S φ 0) ↪ F} {φ_1 : (indexPowT S φ 1) ↪ F}
  [∀ i : ℕ, Fintype (indexPowT S φ i)] [∀ i : ℕ, DecidableEq (indexPowT S φ i)]
  [Smooth φ_0] [Smooth φ_1]
  [h : ∀ {f : (indexPowT S φ 0) → F}, DecidableBlockDisagreement 0 k f S_0 φ_0]
  [h : ∀ {f : (indexPowT S φ 1) → F}, DecidableBlockDisagreement 1 k f S_1 φ_1]
  [∀ i : ℕ, Neg (indexPowT S φ i)]
  {C : Set ((indexPowT S φ 0) → F)} (hcode : C = smoothCode F (indexPowT S φ 0) φ_0 m)
  (C' : Set ((indexPowT S φ 1) → F)) (hcode' : C' = smoothCode F (indexPowT S φ 1) φ_1 (m-1))
  {BStar : (Set (indexPowT S φ 1 → F)) → ℕ → ℝ≥0}
  {errStar : (Set (indexPowT S φ 1 → F)) → ℕ → ℝ≥0 → ℝ≥0} :
    Pr_{α ← F} [ ∀ { f : (indexPowT S φ 0) → F} (hδLe: δ ≤ 1 - (BStar C' 2)),

               let listBlock : Set ((indexPowT S φ 0) → F) := Λᵣ(0, k, f, S_0, C, hcode, δ)
               let vec_α : Vector F 1 := Vector.ofFn (fun _ : Fin 1 => α)
               let foldSet := fold_k_set listBlock vec_α
               let fold := fold_k f vec_α
               let listBlock' : Set ((indexPowT S φ 1) → F) := Λᵣ(1, k, fold, S_1, C', hcode', δ)

               foldSet ≠ listBlock'
             ] ≤ errStar C' 2 δ
  := by sorry

end FoldingLemmas
end Fold
