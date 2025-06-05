/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Least Authority
-/

import ArkLib.Data.CodingTheory.RelativeHammingDistance
import ArkLib.Data.CodingTheory.SmoothReedSolomon
import ArkLib.Data.MvPolynomial.LinearMvExtension
import ArkLib.ProofSystem.Whir.BlockRelDistanceGeneric
import ArkLib.ProofSystem.Whir.GenMutualCorrAgreement

namespace Fold

open BlockRelDistance Vector Finset
variable {F : Type*} [Field F] {ι : Type*} [Pow ι ℕ]

/--∃ x ∈ S, such that `y = x ^ 2^(k+1)`. extract_x returns `z = x ^ 2^k` such that `y = z^2`.-/
noncomputable def extract_x
  (S : Finset ι) (φ : ι ↪ F) (k : ℕ) (y : indexPowT S φ (k + 1)) : indexPowT S φ k :=
  let x := Classical.choose y.property
  let hx := Classical.choose_spec y.property
  let z := (φ x) ^ (2^k)
  ⟨z, ⟨x, hx.1, rfl⟩⟩

/--Given a function `f : (ι^(2ᵏ)) → F`, foldf operates on two inputs:
  element `y ∈ LpowT S (k+1)`, hence `∃ x ∈ S, s.t. y = x ^ 2^(k+1)` and `α ∈ F`.
  It obtains the square root of y as `xPow := extract_x S φ k y`, here xPow is of the form x ^ 2^k.
  It returns the value `f(xPow) + f(- xPow)/2 + α • (f(xPow) - f(- xPow))/ 2•xPow`. -/
noncomputable def foldf (S : Finset ι) (φ : ι ↪ F)
  {k : ℕ} [ Neg (indexPowT S φ k) ] (y : indexPowT S φ (k+1))
  (f : indexPowT S φ k → F) (α : F) : F :=
  let xPow := extract_x S φ k y
  let fx := f xPow
  let f_negx := f (-xPow)
  (fx + f_negx) / 2 + α • ((fx - f_negx) / (2 * (xPow.val : F)))

/--the function fold_k_core runs a recursion,
    for a function `f : ι → F` and a vector `αs` of size i
  For i = 0, fold_k_core returns f evaluated at x ∈ S
  For i = (k+1) ≠ 0,
    αs is parsed as α || αs', where αs' is of size k
    function `fk : (ι^2ᵏ) → F` is obtained by making a recursive call to
      `fold_k_core` on input `αs'`
    we obtain the final function `(ι^(2^(k+1))) → F` by invoking `foldf` with `fk` and `α`.-/
noncomputable def fold_k_core {S : Finset ι} {φ : ι ↪ F} (f : (indexPowT S φ 0) → F)
  [∀ i : ℕ, Neg (indexPowT S φ i)] : (i : ℕ) → (αs : Fin i → F) →
    indexPowT S φ i → F
| 0, _ => fun x₀ => f x₀
| k+1, αs => fun y =>
    let α := αs 0
    let αs' : Fin k → F := fun i => αs (Fin.succ i)
    let fk := fold_k_core f k αs'
    foldf S φ y fk α

/--Definition 4.14, part 1
  fold_k takes a function `f : ι → F and a vector `αs` of size k
  and returns a function `Fold : (ι^2ᵏ) → F` -/
noncomputable def fold_k
  {S : Finset ι} {φ : ι ↪ F} {k : ℕ}
  [∀ j : ℕ, Neg (indexPowT S φ j)]
  (f : (indexPowT S φ 0) → F) (αs : Fin k → F) : indexPowT S φ k → F :=
  fold_k_core f k αs

/--Definition 4.14, part 2
  fold_k takes a set of functions `set : Set (ι → F) and a vector `αs` of size k
  and returns a set of functions `Foldset : Set ((ι^2ᵏ) → F)` -/
noncomputable def fold_k_set
  {S : Finset ι} {φ : ι ↪ F} {k : ℕ}
  [∀ j : ℕ, Neg (indexPowT S φ j)]
  (set : Set ((indexPowT S φ 0) → F)) (αs : Fin k → F) : Set (indexPowT S φ k → F) :=
    { g | ∃ f ∈ set, g = fold_k f αs }

namespace FoldingLemmas

open CorrelatedAgreement Generator LinearMvExtension ListDecodable
     NNReal ReedSolomon SmoothDomain

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
         {ι : Type*} [Fintype ι] [Pow ι ℕ] [DecidableEq ι]

/--Claim 4.15
  Let `f : ι → F`, `α ∈ Fᵏ` is the folding randomness, and let `g : (ι^(2ᵏ) → F) = fold_k(f,α)`
  for k ≤ m, `f ∈ RS[F,ι,m]` then we have `g ∈ RS[F,ι^(2ᵏ),(m-k)]`
  if fPoly be the multilinear extension of f, then we have
  (m-k)-variate multilinear extension of g as `gPoly = fPoly(α₁,α₂,...αₖ,X_k,..,X_{m-1})`-/
lemma fold_f_g
  {S : Finset ι} {φ : ι ↪ F} {k m : ℕ}
  {φ_0 : (indexPowT S φ 0) ↪ F}
  [Fintype (indexPowT S φ 0)] [DecidableEq (indexPowT S φ 0)] [Smooth φ_0]
  {φ_k : (indexPowT S φ k) ↪ F}
  [Fintype (indexPowT S φ k)] [DecidableEq (indexPowT S φ k)] [Smooth φ_k]
  [∀ i : ℕ, Neg (indexPowT S φ i)]
  (αs : Fin k → F) (hk : k ≤ m)
  (f : smoothCode F (indexPowT S φ 0) φ_0 m) :
  let f_fun := (f : (indexPowT S φ 0) → F)
  let fPoly := mVdecode f
  let g := fold_k f_fun αs
  let gPoly := partialEval fPoly αs
  g ∈ smoothCode F (indexPowT S φ k) φ_k (m-k) :=
sorry

/--
The `GenMutualCorrParams` class captures the necessary ingrediants and assumptions
to model a sequence of proximity generators and associated correctness parameters
for a set of smooth ReedSolomon codes. It contains the following fields:

- `m`: the target polynomial degree bound used for proximity code generation.
- `inst1`, `inst2`, `inst3`: typeclass instances required to operate on `ι^(2ⁱ)`
    (finiteness, nonemptiness, and decidable equality).
- `φ_i`: per-round embeddings from `ι^(2ⁱ)` into `F`.
- `inst4`: smoothness assumption for each `φ_i`.
- `Genᵢ`: the base proximity generators at each round `i`.
- `Gen_αᵢ`: the proximity generators wrt the generator function Gen(l,α) : {1,α,α²,..,α^{l-1}}
    defined as per `hgen`
- `BStarᵢ`, `errStarᵢ`: parameters denoting code agreement thresholds
    and error probabilities per round.
- `h`: main agreement assumption, stating that each `Gen_αᵢ` satisfies mutual correlated agreement
    for its underlying code.
-/
class GenMutualCorrParams (S : Finset ι) (φ : ι ↪ F) (k : ℕ) where
  m : ℕ

  inst1 : ∀ i : Fin (k+1), Fintype (indexPowT S φ i)
  inst2 : ∀ i : Fin (k+1), Nonempty (indexPowT S φ i)
  inst3 : ∀ i : Fin (k+1), DecidableEq (indexPowT S φ i)

  φ_i : ∀ i : Fin (k+1), (indexPowT S φ i) ↪ F
  inst4 : ∀ i : Fin (k+1), Smooth (φ_i i)

  Genᵢ : ∀ i : Fin (k+1), ProximityGenerator (indexPowT S φ i) F
  Gen_αᵢ : ∀ i : Fin (k+1), ProximityGenerator (indexPowT S φ i) F
  hgen : ∀ i : Fin (k+1), ∀ α : F, Gen_αᵢ i = proximityGenerator_α (Genᵢ i) α (φ_i i) (m-i)
  BStarᵢ : ∀ i : Fin (k+1), (Set (indexPowT S φ i → F)) → ℕ → ℝ≥0
  errStarᵢ : ∀ i : Fin (k+1), (Set (indexPowT S φ i → F)) → ℕ → ℝ≥0 → ℝ≥0
  h : ∀ i : Fin (k+1), genMutualCorrAgreement (Gen_αᵢ i)
        (BStarᵢ i (Gen_αᵢ i).C (Gen_αᵢ i).l)
        (errStarᵢ i (Gen_αᵢ i).C (Gen_αᵢ i).l)

/--Lemma 4.20
  Let C = RS[F,ι,m] be a smooth ReedSolomon code, for k ≤ m and 0 ≤ i < k
  Let Cⁱ = RS[F,ι^(2ⁱ),m-i] and let Gen(l,α) be a proxmity generator with
  mutual correlated agreement for C⁰,...,C^{k-1} with proximity bounds BStar and errStar
  Then for every `f : ι → F` and `δ ∈ (0, 1 - max {i < k} BStar(Cⁱ, 2))`
    `Pr_{α ← F} [ fold_k_set(Λᵣ(0,k,f,S',C,hcode,δ),vecα) ≠ Λ(Cᵏ,fold_k(f,vecα),δ)]
      < ∑ i ≤ k errStar(Cⁱ,2,δ)`,
  where fold_k_set and fold_k are as defined above,
  vecα is generated from α as `{1,α,α²,..}`
  `Λᵣ(0,k,f,S',C,hcode,δ)` corresponds to the Ball of radius δ centered at f,
  wrt (0,k)-wise block relative distance.
  `Λ(Cᵏ,fold(f,vecα),δ)` is the Ball of radius δ at f, wrt the relative Hamming distance
  Below, we use an instance of the class `GenMutualCorrParams` to capture the
  conditions of proxmity generator with mutual correlated agreement for codes
  C⁰,...,C^{k-1}.
-/
theorem folding_listdecoding_if_genMutualCorrAgreement
  {S : Finset ι} {φ : ι ↪ F} {k m j : ℕ} [Smooth φ]
  {S' : Finset (indexPowT S φ 0)} {φ' : (indexPowT S φ 0) ↪ F}
  [∀ i : ℕ, Fintype (indexPowT S φ i)] [DecidableEq (indexPowT S φ 0)] [Smooth φ']
  [h : ∀ {f : (indexPowT S φ 0) → F}, DecidableBlockDisagreement 0 k f S' φ']
  [∀ i : ℕ, Neg (indexPowT S φ i)]
  {C : Set ((indexPowT S φ 0) → F)} (hcode : C = smoothCode F (indexPowT S φ 0) φ' m) (hLe : k ≤ m)
  {GenFunₐ : F → Fin k → F} {δ : ℝ≥0}
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
                ] < (∑ i : Fin (k+1), params.errStarᵢ i (params.Gen_αᵢ i).C 2 δ) := by sorry

/--Lemma 4.21
  Let `C = RS[F,ι,m]` be a smooth ReedSolomon code and k ≤ m
  Denote `C' = RS[F,ι^2,m-1]`, then for every `f : ι → F` and `δ ∈ (0, 1 - BStar(C',2))`
    `Pr_{α ← F} [ fold_k_set(Λᵣ(0,k,f,S_0,C,δ),α) ≠ Λᵣ(1,k-1,foldf(f,α),S_1,C',δ) ]
      < errStar(C',2,δ)`
    where `foldf(f,α)` returns a function `ι^2 → F`,
    S_0 and S_1 denote finite sets of elements of type ι and ι², and
    Λᵣ denotes the Ball of radius δ wrt block relative distance.
    Λᵣ(0,k,f,S_0,C) denotes Λᵣ at f : ι → F for code C and
    Λᵣ(1,k-1,foldf(f,α),S_1,C') denotes Λᵣ at foldf : ι^2 → F for code C'.-/
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
               let vec_α : Fin 1 → F := (fun _ : Fin 1 => α)
               let foldSet := fold_k_set listBlock vec_α
               let fold := fold_k f vec_α
               let listBlock' : Set ((indexPowT S φ 1) → F) := Λᵣ(1, k, fold, S_1, C', hcode', δ)

               foldSet ≠ listBlock'
             ] < errStar C' 2 δ
  := by sorry

/--Lemma 4.22
  Following same parameters as Lemma 4.21 above, and states
  `∀ α : F, Λᵣ(0,k,f,S_0,C,δ),α) ⊆ Λᵣ(1,k-1,foldf(f,α),S_1,C',δ)`-/
lemma folding_preserves_listdecoding_bound
  {S : Finset ι} {k m : ℕ} {φ : ι ↪ F} [Smooth φ] {δ : ℝ≥0} {f : (indexPowT S φ 0) → F}
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
      ∀ α : F,
        let listBlock : Set ((indexPowT S φ 0) → F) := Λᵣ(0, k, f, S_0, C, hcode, δ)
        let vec_α : Fin 1 → F := (fun _ : Fin 1 => α)
        let foldSet := fold_k_set listBlock vec_α
        let fold := fold_k f vec_α
        let listBlock' : Set ((indexPowT S φ 1) → F) := Λᵣ(1, k, fold, S_1, C', hcode', δ)

        foldSet ⊆ listBlock'
  := by sorry

/--Lemma 4.23
  following same parameters as Lemma 4.21 above, and states
  Pr_{α ← F} [ Λᵣ(1,k-1,foldf(f,α),S_1,C',δ) ¬ ⊆ Λᵣ(0,k,f,S_0,C,δ),α) ] < errStar(C',2,δ)-/
lemma folding_preserves_listdecoding_base_ne_subset
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
               let vec_α : Fin 1 → F := (fun _ : Fin 1 => α)
               let foldSet := fold_k_set listBlock vec_α
               let fold := fold_k f vec_α
               let listBlock' : Set ((indexPowT S φ 1) → F) := Λᵣ(1, k, fold, S_1, C', hcode', δ)

               ¬ (listBlock' ⊆ foldSet)
             ] < errStar C' 2 δ
  := by sorry

end FoldingLemmas
end Fold
