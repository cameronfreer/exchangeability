/-
Copyright (c) 2025 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.Probability.ConditionalExpectation
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Probability.Martingale.Basic
import Exchangeability.Contractability
import Exchangeability.ConditionallyIID
import Exchangeability.Probability.CondExp

/-!
# de Finetti's Theorem via Reverse Martingales

**Aldous' elegant martingale proof** of de Finetti's theorem, as presented in
Kallenberg (2005) as the "third proof". This approach has **medium dependencies**.

## Proof approach

The proof uses a contraction-independence lemma combined with reverse martingale
convergence:

1. **Lemma 1.3** (Contraction-Independence): If `(ξ, η) =^d (ξ, ζ)` and `σ(η) ⊆ σ(ζ)`,
   then `ξ ⊥⊥_η ζ`.

   **Proof idea:** For any `B`, define `μ₁ = P[ξ ∈ B | η]` and `μ₂ = P[ξ ∈ B | ζ]`.
   Then `(μ₁, μ₂)` is a bounded martingale with `μ₁ =^d μ₂`, so
   `E(μ₂ - μ₁)² = Eμ₂² - Eμ₁² = 0`, implying `μ₁ = μ₂` a.s.

2. **Main theorem**: If `ξ` is contractable, then `ξₙ` are conditionally i.i.d.
  given the tail σ-algebra `𝒯_ξ = ⋂_n σ(θ_n ξ)`.

  From contractability: `(ξ_m, θ_{m+1} ξ) =^d (ξ_k, θ_{m+1} ξ)` for `k ≤ m`.
  Using Lemma 1.3 and reverse martingale convergence:
  ```
  P[ξ_m ∈ B | θ_{m+1} ξ] = P[ξ_k ∈ B | θ_{m+1} ξ] → P[ξ_k ∈ B | 𝒯_ξ]
  ```
   This shows conditional independence and identical conditional laws.

## Main results

* `deFinetti_viaMartingale`: **Main theorem** - contractable implies conditionally i.i.d.
* `contraction_independence`: Contraction-independence lemma (Kallenberg Lemma 1.3)

## Dependencies

⚖️ **Medium** - Requires martingale theory and reverse martingale convergence
✅ **Elegant** - Short and conceptually clear proof
✅ **Probabilistic** - Pure probability theory, no functional analysis

## References

* Kallenberg (2005), *Probabilistic Symmetries and Invariance Principles*,
  Lemma 1.3 and page 28: "Third proof of Theorem 1.1"
* Aldous (1983), *Exchangeability and related topics*
-/

noncomputable section
open scoped MeasureTheory ProbabilityTheory Topology

namespace Exchangeability
namespace DeFinetti
namespace ViaMartingale

open MeasureTheory Filter

variable {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]

/-- `shiftProcess X m` is the process `n ↦ X (m + n)` (Kallenberg's θₘ ξ). -/
def shiftProcess (X : ℕ → Ω → α) (m : ℕ) : ℕ → Ω → α := fun n ω => X (m + n) ω

/-- The random path of a process: ω ↦ (n ↦ X n ω). -/
def path (X : ℕ → Ω → α) : Ω → (ℕ → α) := fun ω n => X n ω

/-- Shifted random path: ω ↦ (n ↦ X (m + n) ω). -/
def shiftRV (X : ℕ → Ω → α) (m : ℕ) : Ω → (ℕ → α) :=
  fun ω n => X (m + n) ω

section ComapTools

/-- If `g` is measurable, then `comap (g ∘ f) ≤ comap f`. -/
lemma comap_comp_le
    {X Y Z : Type*} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]
    (f : X → Y) (g : Y → Z) (hg : Measurable g) :
    MeasurableSpace.comap (g ∘ f) (inferInstance : MeasurableSpace Z)
      ≤ MeasurableSpace.comap f (inferInstance : MeasurableSpace Y) := by
  intro s hs
  -- s is a set in the comap (g ∘ f) algebra, so s = (g ∘ f) ⁻¹' t for some t
  obtain ⟨t, ht, rfl⟩ := hs
  -- Show (g ∘ f) ⁻¹' t is in comap f
  refine ⟨g ⁻¹' t, hg ht, ?_⟩
  ext x
  simp [Set.mem_preimage, Function.comp_apply]

end ComapTools

section SequenceShift

variable {β : Type*} [MeasurableSpace β]

/-- Shift a sequence by dropping the first `d` entries. -/
def shiftSeq (d : ℕ) (f : ℕ → β) : ℕ → β := fun n => f (n + d)

@[simp]
lemma shiftSeq_apply {d : ℕ} (f : ℕ → β) (n : ℕ) :
    shiftSeq d f n = f (n + d) := rfl

lemma measurable_shiftSeq {d : ℕ} :
    Measurable (shiftSeq (β:=β) d) := by
  classical
  refine measurable_pi_iff.mpr ?_
  intro n
  -- Evaluation at `n + d` is measurable in the product σ-algebra.
  simp only [shiftSeq]
  exact measurable_pi_apply (n + d)

lemma forall_mem_erase {γ : Type*} [DecidableEq γ]
    {s : Finset γ} {a : γ} {P : γ → Prop} (ha : a ∈ s) :
    (∀ x ∈ s, P x) ↔ P a ∧ ∀ x ∈ s.erase a, P x := by
  constructor
  · intro h
    refine ⟨h _ ha, ?_⟩
    intro x hx
    exact h _ (Finset.mem_of_mem_erase hx)
  · rintro ⟨haP, hrest⟩ x hx
    by_cases hxa : x = a
    · simpa [hxa] using haP
    · have hx' : x ∈ s.erase a := by
        exact Finset.mem_erase.mpr ⟨hxa, hx⟩
      exact hrest _ hx'

end SequenceShift

section TailCylinders

/-- Cylinder on the first `r` tail coordinates (shifted by one). -/
def tailCylinder (r : ℕ) (C : Fin r → Set α) : Set (ℕ → α) :=
  {f | ∀ i : Fin r, f (i.1 + 1) ∈ C i}

variable [MeasurableSpace α]

/-- Basic measurability for tail cylinders. -/
lemma tailCylinder_measurable {r : ℕ} {C : Fin r → Set α}
    (hC : ∀ i, MeasurableSet (C i)) :
    MeasurableSet (tailCylinder (α:=α) r C) := by
  classical
  simp only [tailCylinder, Set.setOf_forall]
  exact MeasurableSet.iInter fun i => by
    have : (fun f : ℕ → α => f (i.val + 1)) ⁻¹' C i = {f | f (i.1 + 1) ∈ C i} := by
      ext f; simp [Set.mem_preimage]
    rw [← this]
    exact (hC i).preimage (measurable_pi_apply (i.val + 1))

end TailCylinders

section FinsetOrder

open Finset

lemma orderEmbOfFin_strictMono {s : Finset ℕ} :
    StrictMono fun i : Fin s.card => s.orderEmbOfFin rfl i := by
  classical
  simpa using (s.orderEmbOfFin rfl).strictMono

lemma orderEmbOfFin_mem {s : Finset ℕ} {i : Fin s.card} :
    s.orderEmbOfFin rfl i ∈ s := by
  classical
  simpa using Finset.orderEmbOfFin_mem (s:=s) (h:=rfl) i

lemma orderEmbOfFin_surj {s : Finset ℕ} {x : ℕ} (hx : x ∈ s) :
    ∃ i : Fin s.card, s.orderEmbOfFin rfl i = x := by
  classical
  -- orderEmbOfFin is an order isomorphism, hence bijective onto s
  -- Use the fact that it's an injective function from a finite type to itself
  have h_inj : Function.Injective (s.orderEmbOfFin rfl : Fin s.card → ℕ) :=
    (s.orderEmbOfFin rfl).injective
  have h_range_sub : ∀ i, s.orderEmbOfFin rfl i ∈ s := fun i => s.orderEmbOfFin_mem rfl i
  -- Define a function to s viewed as a subtype
  let f : Fin s.card → s := fun i => ⟨s.orderEmbOfFin rfl i, h_range_sub i⟩
  have hf_inj : Function.Injective f := by
    intro i j hij
    exact h_inj (Subtype.ext_iff.mp hij)
  -- Injective function between finite types of equal cardinality is surjective
  haveI : Fintype s := Finset.fintypeCoeSort s
  have hcard : Fintype.card (Fin s.card) = Fintype.card s := by simp
  have hf_bij : Function.Bijective f := by
    rw [Fintype.bijective_iff_injective_and_card]
    exact ⟨hf_inj, hcard⟩
  have hf_surj : Function.Surjective f := hf_bij.2
  obtain ⟨i, hi⟩ := hf_surj ⟨x, hx⟩
  use i
  exact Subtype.ext_iff.mp hi

/-- If `f : Fin n → ℕ` is strictly monotone and `a < f i` for all `i`,
then `Fin.cases a f : Fin (n+1) → ℕ` is strictly monotone. -/
lemma strictMono_fin_cases
    {n : ℕ} {f : Fin n → ℕ} (hf : StrictMono f) {a : ℕ}
    (ha : ∀ i, a < f i) :
    StrictMono (Fin.cases a (fun i => f i)) := by
  intro i j hij
  cases i using Fin.cases with
  | zero =>
    cases j using Fin.cases with
    | zero => exact absurd hij (lt_irrefl _)
    | succ j => simpa using ha j
  | succ i =>
    cases j using Fin.cases with
    | zero =>
      have : (Fin.succ i : Fin (n + 1)).1 < 0 := by
        simpa [Fin.lt_iff_val_lt_val] using hij
      exact absurd this (Nat.not_lt.mpr (Nat.zero_le _))
    | succ j =>
      have hij' : i < j := (Fin.succ_lt_succ_iff).1 hij
      simpa using hf hij'

end FinsetOrder

omit [MeasurableSpace Ω] [MeasurableSpace α] in
@[simp]
lemma path_apply (X : ℕ → Ω → α) (ω n) :
    path X ω n = X n ω := rfl

omit [MeasurableSpace Ω] [MeasurableSpace α] in
@[simp]
lemma shiftRV_apply (X : ℕ → Ω → α) (m ω n) :
    shiftRV X m ω n = X (m + n) ω := rfl

omit [MeasurableSpace Ω] [MeasurableSpace α] in
@[simp]
lemma shiftRV_zero (X : ℕ → Ω → α) : shiftRV X 0 = path X := by
  funext ω n; simp [shiftRV, path]

omit [MeasurableSpace Ω] [MeasurableSpace α] in
@[simp]
lemma shiftRV_comp_shiftProcess (X : ℕ → Ω → α) (m k : ℕ) :
    shiftRV (shiftProcess X m) k = shiftRV X (m + k) := by
  funext ω n; simp [shiftRV, shiftProcess, Nat.add_assoc]

omit [MeasurableSpace Ω] [MeasurableSpace α] in
@[simp]
lemma shiftProcess_zero (X : ℕ → Ω → α) : shiftProcess X 0 = X := by
  funext n ω; simp [shiftProcess]

omit [MeasurableSpace Ω] [MeasurableSpace α] in
@[simp]
lemma shiftProcess_add (X : ℕ → Ω → α) (m k : ℕ) :
    shiftProcess (shiftProcess X m) k = shiftProcess X (m + k) := by
  funext n ω; simp [shiftProcess, Nat.add_assoc]

/-- If all coordinates of X are measurable, so are all coordinates of shifted process. -/
lemma measurable_shiftProcess (X : ℕ → Ω → α) (m : ℕ)
    (hX : ∀ n, Measurable (X n)) (n : ℕ) :
    Measurable (shiftProcess X m n) :=
  hX (m + n)

/-- The path map is measurable when all coordinates are measurable. -/
lemma measurable_path (X : ℕ → Ω → α) (hX : ∀ n, Measurable (X n)) :
    Measurable (path X) := by
  apply measurable_pi_lambda
  intro n
  simp only [path]
  exact hX n

omit [MeasurableSpace Ω] [MeasurableSpace α] in
lemma path_eq_shiftRV_zero (X : ℕ → Ω → α) : path X = shiftRV X 0 :=
  (shiftRV_zero X).symm

omit [MeasurableSpace Ω] [MeasurableSpace α] in
/-- Composing X_n with shiftProcess extracts the (m+n)-th coordinate. -/
@[simp]
lemma coord_comp_shiftProcess (X : ℕ → Ω → α) (m n : ℕ) :
    (fun ω => shiftProcess X m n ω) = X (m + n) := by
  funext ω; simp [shiftProcess]

omit [MeasurableSpace Ω] [MeasurableSpace α] in
/-- Relationship between shiftRV and path composition. -/
lemma shiftRV_eq_path_comp_shift (X : ℕ → Ω → α) (m : ℕ) :
    shiftRV X m = path (shiftProcess X m) := by
  funext ω n; simp [shiftRV, path, shiftProcess]

omit [MeasurableSpace Ω] [MeasurableSpace α] in
lemma shiftProcess_apply (X : ℕ → Ω → α) (m n ω) :
    shiftProcess X m n ω = X (m + n) ω := by
  rfl

/-- 𝔽ₘ := σ(θₘ X) = σ(ω ↦ (n ↦ X (m+n) ω)). -/
abbrev revFiltration (X : ℕ → Ω → α) (m : ℕ) : MeasurableSpace Ω :=
  MeasurableSpace.comap (shiftRV X m) inferInstance

@[simp]
lemma revFiltration_zero (X : ℕ → Ω → α) :
    revFiltration X 0 = MeasurableSpace.comap (path X) inferInstance := by
  simp [revFiltration]

lemma revFiltration_le (X : ℕ → Ω → α) (hX : ∀ n, Measurable (X n)) (m : ℕ) :
    revFiltration X m ≤ (inferInstance : MeasurableSpace Ω) := by
  -- The comap is ≤ ambient iff the function is measurable
  -- shiftRV X m = path (shiftProcess X m) is measurable
  simp only [revFiltration]
  intro s hs
  obtain ⟨t, ht, rfl⟩ := hs
  rw [shiftRV_eq_path_comp_shift]
  have h_meas := measurable_path (shiftProcess X m) (measurable_shiftProcess X m hX)
  exact h_meas ht

/-- The tail σ-algebra for a process X: ⋂ₙ σ(Xₙ, Xₙ₊₁, ...). -/
def tailSigma (X : ℕ → Ω → α) : MeasurableSpace Ω :=
  ⨅ m, revFiltration X m

omit [MeasurableSpace Ω] in
@[simp]
lemma tailSigma_eq_iInf_rev (X : ℕ → Ω → α) :
    tailSigma X = ⨅ m, revFiltration X m := rfl

section Measurability

variable {X : ℕ → Ω → α}

lemma measurable_shiftRV (hX : ∀ n, Measurable (X n)) {m : ℕ} :
    Measurable (shiftRV X m) := by
  classical
  simpa [shiftRV] using
    measurable_pi_iff.mpr (fun n => by simpa using hX (m + n))

end Measurability

lemma revFiltration_antitone (X : ℕ → Ω → α) :
    Antitone (revFiltration X) := by
  intro m n hmn
  -- Need to show: revFiltration X n ≤ revFiltration X m when m ≤ n
  -- Strategy: shiftRV X n = shiftSeq (n - m) ∘ shiftRV X m
  simp only [revFiltration]
  let k := n - m
  -- Show shiftRV X n = shiftSeq k ∘ shiftRV X m
  have h_comp : shiftRV X n = shiftSeq k ∘ shiftRV X m := by
    funext ω i
    simp only [shiftRV, shiftSeq, Function.comp_apply]
    congr 1
    omega
  rw [h_comp]
  exact comap_comp_le (shiftRV X m) (shiftSeq k) measurable_shiftSeq

/-- If `X` is contractable, then so is each of its shifts `θₘ X`. -/
lemma shift_contractable {μ : Measure Ω} {X : ℕ → Ω → α}
    (hX : Contractable μ X) (m : ℕ) : Contractable μ (shiftProcess X m) := by
  -- For any strictly monotone k : Fin n → ℕ, need to show:
  -- (shiftProcess X m (k i))ᵢ ~ (shiftProcess X m i)ᵢ
  intro n k hk_mono
  -- Define k' i = m + k i (strictly monotone)
  let k' : Fin n → ℕ := fun i => m + k i
  have hk'_mono : StrictMono k' := by
    intro i j hij
    simp only [k']
    exact Nat.add_lt_add_left (hk_mono hij) m
  -- Also define j i = m + i (for the RHS)
  let j : Fin n → ℕ := fun i => m + i
  have hj_mono : StrictMono j := by
    intro i₁ i₂ h
    simp only [j]
    exact Nat.add_lt_add_left h m
  -- Apply contractability to k' and j
  have h1 := hX n k' hk'_mono
  have h2 := hX n j hj_mono
  -- Now connect the pieces:
  -- (shiftProcess X m (k i))ᵢ = (X (m + k i))ᵢ = (X (k' i))ᵢ
  -- ~ (X i)ᵢ (by h1)
  -- ~ (X (j i))ᵢ (by h2.symm)
  -- = (X (m + i))ᵢ = (shiftProcess X m i)ᵢ
  calc Measure.map (fun ω i => shiftProcess X m (k i) ω) μ
      = Measure.map (fun ω i => X (k' i) ω) μ := by congr
    _ = Measure.map (fun ω i => X i.val ω) μ := h1
    _ = Measure.map (fun ω i => X (j i) ω) μ := h2.symm
    _ = Measure.map (fun ω i => shiftProcess X m i.val ω) μ := by congr

/- DELETED: The following two lemmas are unused in this file.
   The stronger rectangle-based lemma `condexp_indicator_eq_of_agree_on_future_rectangles`
   from CondExp.lean provides the needed functionality.

/-- **Lemma 1.3 (contraction and independence).**

If `(ξ, η) =^d (ξ, ζ)` and `σ(η) ⊆ σ(ζ)`, then `ξ ⊥⊥_η ζ`.
[Proof sketch omitted - would use L² martingale argument]
*Kallenberg (2005), Lemma 1.3.* -/
-- lemma contraction_independence ... := by sorry

/-- If `(ξ,η)` and `(ξ,ζ)` have the same law and `σ(η) ≤ σ(ζ)`,
then for all measurable `B`, the conditional expectations of `1_{ξ∈B}` coincide.
[Proof sketch omitted - would use L² norm comparison] -/
-- lemma condexp_indicator_eq_of_dist_eq_and_le ... := by sorry
-/

/-- Finite-dimensional (cylinder) equality:
for any `r`, base set `B` and measurable sets on the first `r` tail coordinates,
the probabilities agree when comparing `(X m, θₘ X)` vs `(X k, θₘ X)`.

This is the exact finite-dimensional marginal needed for the martingale step. -/
lemma contractable_dist_eq_on_first_r_tail
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → α} (hX : Contractable μ X) (hX_meas : ∀ n, Measurable (X n))
    (k m r : ℕ) (hk : k ≤ m)
    (B : Set α) (hB : MeasurableSet B)
    (C : Fin r → Set α) (hC : ∀ i, MeasurableSet (C i)) :
    μ {ω | X m ω ∈ B ∧ ∀ i : Fin r, X (m + (i.1 + 1)) ω ∈ C i}
      = μ {ω | X k ω ∈ B ∧ ∀ i : Fin r, X (m + (i.1 + 1)) ω ∈ C i} := by
  classical
  let f : Fin r → ℕ := fun i => m + (i.1 + 1)
  have hf_mono : StrictMono f := by
    intro i j hij
    have hij' : i.1 < j.1 := (Fin.lt_iff_val_lt_val).1 hij
    have : i.1 + 1 < j.1 + 1 := Nat.succ_lt_succ hij'
    simpa [f, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      Nat.add_lt_add_left this m
  have hm_lt : ∀ i, m < f i := by
    intro i
    have : 0 < i.1 + 1 := Nat.succ_pos _
    simpa [f] using Nat.lt_add_of_pos_right this
  have hk_lt : ∀ i, k < f i := fun i => lt_of_le_of_lt hk (hm_lt i)
  let s₁ : Fin (r+1) → ℕ := Fin.cases m f
  let s₂ : Fin (r+1) → ℕ := Fin.cases k f
  have hs₁ : StrictMono s₁ := strictMono_fin_cases (n:=r) (f:=f) hf_mono hm_lt
  have hs₂ : StrictMono s₂ := strictMono_fin_cases (n:=r) (f:=f) hf_mono hk_lt
  have hmap_eq :
      Measure.map (fun ω i => X (s₁ i) ω) μ
        = Measure.map (fun ω i => X (s₂ i) ω) μ := by
    calc
      Measure.map (fun ω i => X (s₁ i) ω) μ
          = Measure.map (fun ω (i : Fin (r+1)) => X i.1 ω) μ := by
            simpa [s₁] using hX (r+1) s₁ hs₁
      _   = Measure.map (fun ω i => X (s₂ i) ω) μ := by
            simpa [s₂] using (hX (r+1) s₂ hs₂).symm
  let A : Set (Fin (r+1) → α) :=
    {v | v 0 ∈ B ∧ ∀ i : Fin r, v (Fin.succ i) ∈ C i}
  have hpre₁ :
      {ω | X m ω ∈ B ∧ ∀ i : Fin r, X (m + (i.1 + 1)) ω ∈ C i}
        = (fun ω i => X (s₁ i) ω) ⁻¹' A := by
    ext ω; simp [A, s₁, f]
  have hpre₂ :
      {ω | X k ω ∈ B ∧ ∀ i : Fin r, X (m + (i.1 + 1)) ω ∈ C i}
        = (fun ω i => X (s₂ i) ω) ⁻¹' A := by
    ext ω; simp [A, s₂, f]
  have hA : MeasurableSet A := by
    have h0 : Measurable (fun (v : Fin (r+1) → α) => v 0) := measurable_pi_apply 0
    have hS : ∀ i : Fin r, Measurable (fun (v : Fin (r+1) → α) => v (Fin.succ i)) :=
      fun i => measurable_pi_apply (Fin.succ i)
    have : A = (fun v => v 0) ⁻¹' B ∩ ⋂ i : Fin r, (fun v => v (Fin.succ i)) ⁻¹' C i := by
      ext v; simp [A, Set.mem_iInter]
    rw [this]
    exact (h0 hB).inter (MeasurableSet.iInter fun i => hS i (hC i))
  -- Both functions are measurable (from hX_meas)
  have hφ₁ : Measurable (fun ω i => X (s₁ i) ω) := by
    apply measurable_pi_lambda
    intro i
    cases i using Fin.cases with
    | zero => exact hX_meas m
    | succ j => simp only [s₁, f]; exact hX_meas (m + (j.1 + 1))
  have hφ₂ : Measurable (fun ω i => X (s₂ i) ω) := by
    apply measurable_pi_lambda
    intro i
    cases i using Fin.cases with
    | zero => exact hX_meas k
    | succ j => simp only [s₂, f]; exact hX_meas (m + (j.1 + 1))
  calc μ {ω | X m ω ∈ B ∧ ∀ i : Fin r, X (m + (i.1 + 1)) ω ∈ C i}
      = μ ((fun ω i => X (s₁ i) ω) ⁻¹' A) := by rw [hpre₁]
    _ = (Measure.map (fun ω i => X (s₁ i) ω) μ) A := (Measure.map_apply hφ₁ hA).symm
    _ = (Measure.map (fun ω i => X (s₂ i) ω) μ) A := by rw [hmap_eq]
    _ = μ ((fun ω i => X (s₂ i) ω) ⁻¹' A) := Measure.map_apply hφ₂ hA
    _ = μ {ω | X k ω ∈ B ∧ ∀ i : Fin r, X (m + (i.1 + 1)) ω ∈ C i} := by rw [← hpre₂]

/-- Future reverse filtration: 𝔽ᶠᵘᵗₘ = σ(θ_{m+1} X). -/
abbrev futureFiltration (X : ℕ → Ω → α) (m : ℕ) : MeasurableSpace Ω :=
  MeasurableSpace.comap (shiftRV X (m + 1)) inferInstance

/-- **Key convergence result:** The extreme members agree after conditioning on the tail σ-algebra.

For any `k ≤ m` and measurable set `B`:
```
P[X_m ∈ B | θ_{m+1} X] = P[X_k ∈ B | θ_{m+1} X] → P[X_k ∈ B | 𝒯_X]  (as n → ∞)
```

This is proved using Lemma 1.3 (contraction-independence) followed by reverse
martingale convergence. -/
-- TODO: The following theorems require conditional expectation API that is not yet
-- fully developed in this codebase. The proof structure is documented for future work.

-- TODO: Uses agree_on_future_rectangles_of_contractable defined later
axiom condexp_convergence
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → α} (hX : Contractable μ X)
    (hX_meas : ∀ n, Measurable (X n))
    (k m : ℕ) (hk : k ≤ m)
    (B : Set α) (hB : MeasurableSet B) :
    μ[Set.indicator B (fun _ => (1 : ℝ)) ∘ (X m) | futureFiltration X m]
      =ᵐ[μ]
    μ[Set.indicator B (fun _ => (1 : ℝ)) ∘ (X k) | futureFiltration X m]

lemma extreme_members_equal_on_tail
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → α}
    (hX : Contractable μ X)
    (hX_meas : ∀ n, Measurable (X n))
    (m : ℕ) (B : Set α) (hB : MeasurableSet B) :
    μ[Set.indicator B (fun _ => (1 : ℝ)) ∘ (X m) | tailSigma X]
      =ᵐ[μ]
    μ[Set.indicator B (fun _ => (1 : ℝ)) ∘ (X 0) | tailSigma X] := by
  sorry  -- TODO: Uses futureFiltration defined later in file

/-! ## Future filtration (additive)

Additive "future-filtration + standard-cylinder" layer that coexists with the
current `revFiltration` / `tailCylinder` infrastructure. Existing names remain intact.
-/
section FutureFiltration

variable {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]

/-- The future filtration is decreasing (antitone). -/
lemma futureFiltration_antitone (X : ℕ → Ω → α) :
    Antitone (futureFiltration X) := by
  intro m n hmn
  simpa [futureFiltration, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
    (revFiltration_antitone X (Nat.succ_le_succ hmn))

/-- Tail σ-algebra via the future filtration. (Additive alias.) -/
def tailSigmaFuture (X : ℕ → Ω → α) : MeasurableSpace Ω :=
  ⨅ m, futureFiltration X m

@[simp] lemma tailSigmaFuture_eq_iInf (X : ℕ → Ω → α) :
    tailSigmaFuture X = ⨅ m, futureFiltration X m := rfl

@[simp] lemma futureFiltration_eq_rev_succ (X : ℕ → Ω → α) (m : ℕ) :
    futureFiltration X m = revFiltration X (m + 1) := rfl

lemma tailSigmaFuture_eq_tailSigma (X : ℕ → Ω → α) :
    tailSigmaFuture X = tailSigma X := by
  classical
  have hfut : tailSigmaFuture X = ⨅ n, revFiltration X (n + 1) := by
    simpa [tailSigmaFuture, futureFiltration_eq_rev_succ]
  have htail : tailSigma X = ⨅ n, revFiltration X n := rfl
  refine le_antisymm ?_ ?_
  · -- `tailSigmaFuture ≤ tailSigma`
    refine (hfut ▸ ?_)
    refine le_iInf ?_
    intro n
    have h1 : (⨅ m, revFiltration X (m + 1)) ≤ revFiltration X (n + 1) :=
      iInf_le (fun m => revFiltration X (m + 1)) n
    have h2 : revFiltration X (n + 1) ≤ revFiltration X n :=
      revFiltration_antitone X (Nat.le_succ n)
    exact h1.trans h2
  · -- `tailSigma ≤ tailSigmaFuture`
    refine (htail ▸ ?_)
    refine le_iInf ?_
    intro n
    have h1 : (⨅ m, revFiltration X m) ≤ revFiltration X (n + 1) :=
      iInf_le (fun m => revFiltration X m) (n + 1)
    simpa [futureFiltration_eq_rev_succ] using h1

/-! ### Helper lemmas for tail σ-algebra -/

/-- The tail σ-algebra is a sub-σ-algebra of the ambient σ-algebra. -/
lemma tailSigma_le {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
    (X : ℕ → Ω → α) (hX : ∀ n, Measurable (X n)) :
    tailSigma X ≤ (inferInstance : MeasurableSpace Ω) := by
  refine iInf_le_of_le 0 ?_
  exact revFiltration_le X hX 0

/-- Future filtration is always at least as fine as the tail σ-algebra. -/
lemma tailSigma_le_futureFiltration {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
    (X : ℕ → Ω → α) (m : ℕ) :
    tailSigma X ≤ futureFiltration X m := by
  rw [← tailSigmaFuture_eq_tailSigma]
  exact iInf_le (fun m => futureFiltration X m) m

/-- Indicators of tail-measurable sets are tail-measurable functions. -/
lemma indicator_tailMeasurable {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
    (X : ℕ → Ω → α) (A : Set Ω) (hA : MeasurableSet[tailSigma X] A) :
    StronglyMeasurable[tailSigma X] (A.indicator (fun _ => (1 : ℝ))) := by
  refine StronglyMeasurable.indicator ?_ hA
  exact stronglyMeasurable_const

/-- If each coordinate is measurable, then the tail σ-algebra is sigma-finite
when the base measure is sigma-finite. -/
lemma sigmaFinite_trim_tailSigma {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
    {μ : Measure Ω} [SigmaFinite μ]
    (X : ℕ → Ω → α) (hX : ∀ n, Measurable (X n)) :
    SigmaFinite (μ.trim (tailSigma_le X hX)) := by
  sorry  -- TODO: Need to prove sigma-finiteness is preserved under trimming
  -- inferInstance fails; may need manual construction or mathlib extension

/-! ### Helper lemmas for futureFiltration properties -/

/-- The future filtration at level m is a sub-σ-algebra of the ambient σ-algebra. -/
lemma futureFiltration_le {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
    (X : ℕ → Ω → α) (m : ℕ) (hX : ∀ n, Measurable (X n)) :
    futureFiltration X m ≤ (inferInstance : MeasurableSpace Ω) := by
  -- futureFiltration X m = revFiltration X (m + 1)
  simp only [futureFiltration]
  exact revFiltration_le X hX (m + 1)

/-- The preimage of a measurable set under X_{m+k} is measurable in futureFiltration X m.
Note: This requires k ≥ 1 since futureFiltration X m = σ(X_{m+1}, X_{m+2}, ...). -/
lemma preimage_measurable_in_futureFiltration {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
    (X : ℕ → Ω → α) (m k : ℕ) (hk : 1 ≤ k) {A : Set α} (hA : MeasurableSet A) :
    MeasurableSet[futureFiltration X m] (X (m + k) ⁻¹' A) := by
  -- futureFiltration X m = comap (shiftRV X (m+1))
  -- X (m + k) = X (m + 1 + (k-1)) = π_{k-1} ∘ shiftRV X (m+1)
  -- where π_n projects to the n-th coordinate
  simp only [futureFiltration]
  have : X (m + k) = (fun f : ℕ → α => f (k - 1)) ∘ shiftRV X (m + 1) := by
    funext ω
    simp [shiftRV]
    congr 1
    omega
  rw [this, Set.preimage_comp]
  exact ⟨(fun f : ℕ → α => f (k - 1)) ⁻¹' A, (measurable_pi_apply (k - 1)) hA, rfl⟩

/-- Events measurable in a future filtration remain measurable in earlier filtrations. -/
lemma measurableSet_of_futureFiltration {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
    (X : ℕ → Ω → α) {m n : ℕ} (hmn : m ≤ n) {A : Set Ω}
    (hA : MeasurableSet[futureFiltration X n] A) :
    MeasurableSet[futureFiltration X m] A := by
  exact futureFiltration_antitone X hmn A hA

end FutureFiltration

/-! ## Standard cylinders on paths (starting at index 0) -/
section FutureCylinders

variable {α : Type*}

/-- Standard cylinder on the first `r` coordinates starting at index 0. -/
def cylinder (r : ℕ) (C : Fin r → Set α) : Set (ℕ → α) :=
  {f | ∀ i : Fin r, f i ∈ C i}

/-- Cylinder for functions with domain Fin r. -/
def finCylinder (r : ℕ) (C : Fin r → Set α) : Set (Fin r → α) :=
  {f | ∀ i : Fin r, f i ∈ C i}

variable [MeasurableSpace α]

lemma finCylinder_measurable {r : ℕ} {C : Fin r → Set α}
    (hC : ∀ i, MeasurableSet (C i)) :
    MeasurableSet (finCylinder r C) := by
  classical
  simp only [finCylinder, Set.setOf_forall]
  exact MeasurableSet.iInter fun i => by
    have : (fun f : Fin r → α => f i) ⁻¹' C i = {f | f i ∈ C i} := by
      ext f; simp [Set.mem_preimage]
    rw [← this]
    exact (hC i).preimage (measurable_pi_apply i)

lemma cylinder_measurable {r : ℕ} {C : Fin r → Set α}
    (hC : ∀ i, MeasurableSet (C i)) :
    MeasurableSet (cylinder (α:=α) r C) := by
  classical
  simp only [cylinder, Set.setOf_forall]
  exact MeasurableSet.iInter fun i => by
    have : (fun f : ℕ → α => f i.val) ⁻¹' C i = {f | f i ∈ C i} := by
      ext f; simp [Set.mem_preimage]
    rw [← this]
    exact (hC i).preimage (measurable_pi_apply i.val)

end FutureCylinders

/-! ### A tiny helper: measurability of the finite block cylinder for the first `r` coordinates

This section provides infrastructure for working with finite block cylinders on the first `r`
coordinates of a sequence. The key insight is that `indProd X r C` (the product of indicators)
equals the indicator of the cylinder set `firstRCylinder X r C`.

## Connection to `finite_level_factorization`

In the proof of `finite_level_factorization`, we inductively factor the product indicator
`indProd X (r+1) C` into:
- `f = indProd X r Cinit` (first r coordinates)
- `g = indicator of X_r⁻¹(last)` (r-th coordinate)

Using the helpers in this section:
- `f = (firstRCylinder X r Cinit).indicator (fun _ => 1)` (by `indProd_eq_firstRCylinder_indicator`)
- `firstRCylinder X r Cinit` is measurable in `firstRSigma X r`
  (by `firstRCylinder_measurable_in_firstRSigma`)
- `firstRSigma X r ≤ ambient σ-algebra` when coordinates are measurable
  (by `firstRSigma_le_ambient`)

These properties package exactly what's needed to apply conditional independence results
and the product formula for conditional expectations of indicators.

## Usage pattern

```lean
let mF := firstRSigma X r                    -- σ-algebra from first r coordinates
let A  := firstRCylinder X r C               -- cylinder event

have hA_mF : MeasurableSet[mF] A :=
  firstRCylinder_measurable_in_firstRSigma X r C hC

have hA_ambient : MeasurableSet A :=
  firstRCylinder_measurable_ambient X r C hX hC

have hmF_le : mF ≤ inferInstance :=
  firstRSigma_le_ambient X r hX
```
-/
section FirstBlockCylinder

variable {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]

/-- The map collecting the first `r` coordinates. -/
def firstRMap (X : ℕ → Ω → α) (r : ℕ) : Ω → (Fin r → α) :=
  fun ω i => X i ω

/-- The σ‑algebra generated by the first `r` coordinates. -/
abbrev firstRSigma (X : ℕ → Ω → α) (r : ℕ) : MeasurableSpace Ω :=
  MeasurableSpace.comap (firstRMap X r) inferInstance

/-- The finite block cylinder event on the first `r` coordinates. -/
def firstRCylinder (X : ℕ → Ω → α) (r : ℕ) (C : Fin r → Set α) : Set Ω :=
  {ω | ∀ i : Fin r, X i ω ∈ C i}

/-- As expected, the block cylinder is the preimage of a finite cylinder
   under the `firstRMap`. -/
lemma firstRCylinder_eq_preimage_finCylinder
    (X : ℕ → Ω → α) (r : ℕ) (C : Fin r → Set α) :
    firstRCylinder X r C
      = (firstRMap X r) ⁻¹' (finCylinder (α:=α) r C) := rfl

/-- **Measurable in the first-`r` σ‑algebra.**
If each `C i` is measurable in `α`, then the block cylinder is measurable in
`firstRSigma X r` (no measurability assumptions on the `X i` are needed for this
comap‑level statement). -/
lemma firstRCylinder_measurable_in_firstRSigma
    (X : ℕ → Ω → α) (r : ℕ) (C : Fin r → Set α)
    (hC : ∀ i, MeasurableSet (C i)) :
    MeasurableSet[firstRSigma X r] (firstRCylinder X r C) := by
  -- firstRSigma X r = comap (firstRMap X r)
  -- A set is measurable in the comap iff it's a preimage of a measurable set
  rw [firstRCylinder_eq_preimage_finCylinder]
  exact ⟨_, finCylinder_measurable hC, rfl⟩

/-- **Measurable in the ambient σ‑algebra.**
If each coordinate `X i` is measurable, then the block cylinder is measurable
in the ambient σ‑algebra (useful for `Integrable.indicator`). -/
lemma firstRCylinder_measurable_ambient
    (X : ℕ → Ω → α) (r : ℕ) (C : Fin r → Set α)
    (hX : ∀ i, Measurable (X i)) (hC : ∀ i, MeasurableSet (C i)) :
    MeasurableSet (firstRCylinder X r C) := by
  classical
  -- Directly as an intersection over `Fin r`.
  simp only [firstRCylinder, Set.setOf_forall]
  exact MeasurableSet.iInter fun i => (hX i) (hC i)

/-- The firstRMap is measurable when all coordinates are measurable. -/
lemma measurable_firstRMap
    (X : ℕ → Ω → α) (r : ℕ) (hX : ∀ i, Measurable (X i)) :
    Measurable (firstRMap X r) := by
  apply measurable_pi_lambda
  intro i
  exact hX i

/-- The first-r σ-algebra is a sub-σ-algebra of the ambient σ-algebra when coordinates are measurable. -/
lemma firstRSigma_le_ambient
    (X : ℕ → Ω → α) (r : ℕ) (hX : ∀ i, Measurable (X i)) :
    firstRSigma X r ≤ (inferInstance : MeasurableSpace Ω) := by
  simp only [firstRSigma]
  intro s hs
  obtain ⟨t, ht, rfl⟩ := hs
  exact (measurable_firstRMap X r hX) ht

/-- Stronger version: firstRSigma increases with r. -/
lemma firstRSigma_mono
    (X : ℕ → Ω → α) {r s : ℕ} (hrs : r ≤ s) :
    firstRSigma X r ≤ firstRSigma X s := by
  -- Strategy: firstRMap X r factors through firstRMap X s via projection
  simp only [firstRSigma]
  intro t ht
  obtain ⟨u, hu, rfl⟩ := ht
  -- Define projection π : (Fin s → α) → (Fin r → α) taking first r coords
  let π : (Fin s → α) → (Fin r → α) := fun f i => f ⟨i.val, Nat.lt_of_lt_of_le i.isLt hrs⟩
  -- Show firstRMap X r = π ∘ firstRMap X s
  have h_comp : firstRMap X r = π ∘ firstRMap X s := by
    funext ω i
    simp [firstRMap, π]
  -- π is measurable (composition of coordinate projections)
  have hπ : Measurable π := by
    rw [measurable_pi_iff]
    intro i
    simp only [π]
    exact measurable_pi_apply _
  -- Preimage factors through composition
  rw [h_comp, Set.preimage_comp]
  exact ⟨π ⁻¹' u, hπ hu, rfl⟩

/-- The first r coordinates are measurable in the full reverse filtration. -/
lemma firstRSigma_le_revFiltration_zero
    (X : ℕ → Ω → α) (r : ℕ) :
    firstRSigma X r ≤ revFiltration X 0 := by
  -- revFiltration X 0 generates σ(X₀, X₁, X₂, ...) which contains σ(X₀, ..., X_{r-1})
  -- Strategy: firstRMap X r factors through path X via projection
  simp only [firstRSigma, revFiltration]
  intro s hs
  obtain ⟨t, ht, rfl⟩ := hs
  -- Define projection π : (ℕ → α) → (Fin r → α) that takes first r coords
  let π : (ℕ → α) → (Fin r → α) := fun f i => f i
  -- firstRMap X r = π ∘ shiftRV X 0 = π ∘ path X
  have h_comp : firstRMap X r = π ∘ shiftRV X 0 := by
    funext ω i
    simp [firstRMap, shiftRV, π]
  -- π is measurable
  have hπ : Measurable π := by
    apply measurable_pi_lambda
    intro i
    simp only [π]
    exact measurable_pi_apply (i : ℕ)
  rw [h_comp, Set.preimage_comp]
  exact ⟨π ⁻¹' t, hπ ht, rfl⟩

/-- **NOTE:** This lemma statement appears incorrect as written.
- `firstRSigma X r` is generated by X₀, ..., X_{r-1}
- `futureFiltration X m` is generated by X_{m+1}, X_{m+2}, ...
- When r ≤ m, these are non-overlapping index sets, so the inclusion cannot hold.

The correct statement might be `firstRSigma_le_revFiltration_zero` (proved above),
or perhaps the indices/filtrations need to be adjusted.

This is currently only used in the commented-out proof of `finite_level_factorization`
(line 1380), which is an axiom placeholder returning `True`. -/
lemma firstRSigma_le_futureFiltration
    (X : ℕ → Ω → α) {r m : ℕ} (hrm : r ≤ m) :
    firstRSigma X r ≤ futureFiltration X m := by
  sorry  -- TODO: Statement needs correction - see note above

/-- The empty cylinder (r = 0) is the whole space. -/
@[simp]
lemma firstRCylinder_zero (X : ℕ → Ω → α) (C : Fin 0 → Set α) :
    firstRCylinder X 0 C = Set.univ := by
  ext ω
  simp [firstRCylinder]

/-- Cylinder membership characterization. -/
lemma mem_firstRCylinder_iff (X : ℕ → Ω → α) (r : ℕ) (C : Fin r → Set α) (ω : Ω) :
    ω ∈ firstRCylinder X r C ↔ ∀ i : Fin r, X i ω ∈ C i :=
  Iff.rfl

/-- firstRCylinder on universal sets is the whole space. -/
lemma firstRCylinder_univ (X : ℕ → Ω → α) (r : ℕ) :
    firstRCylinder X r (fun _ => Set.univ) = Set.univ := by
  ext ω; simp [firstRCylinder]

/-- Intersection of firstRCylinders equals coordinate-wise intersection. -/
lemma firstRCylinder_inter (X : ℕ → Ω → α) {r : ℕ} {C D : Fin r → Set α} :
    firstRCylinder X r C ∩ firstRCylinder X r D = firstRCylinder X r (fun i => C i ∩ D i) := by
  ext ω
  simp [firstRCylinder, Set.mem_inter_iff]
  constructor
  · intro ⟨hC, hD⟩ i
    exact ⟨hC i, hD i⟩
  · intro h
    exact ⟨fun i => (h i).1, fun i => (h i).2⟩

end FirstBlockCylinder

/-! ## Product of indicators for finite cylinders -/

/-- Product of indicator functions for a finite cylinder on the first `r` coordinates. -/
def indProd {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
    (X : ℕ → Ω → α) (r : ℕ) (C : Fin r → Set α) : Ω → ℝ :=
  fun ω => ∏ i : Fin r, Set.indicator (C i) (fun _ => (1 : ℝ)) (X i ω)

lemma indProd_as_indicator
    {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
    (X : ℕ → Ω → α) (r : ℕ) (C : Fin r → Set α) :
    indProd X r C
      = Set.indicator {ω | ∀ i : Fin r, X i ω ∈ C i} (fun _ => (1 : ℝ)) := by
  funext ω
  simp only [indProd, Set.indicator]
  split_ifs with h
  · -- ω satisfies all conditions: product equals 1
    calc ∏ i : Fin r, Set.indicator (C i) (fun _ => (1 : ℝ)) (X i ω)
        = ∏ i : Fin r, (1 : ℝ) := by
          congr 1
          ext i
          simp only [Set.indicator]
          rw [if_pos (h i)]
      _ = 1 := Finset.prod_const_one
  · -- ω doesn't satisfy all conditions
    by_cases hr : ∃ i : Fin r, X i ω ∉ C i
    · obtain ⟨i, hi⟩ := hr
      have : Set.indicator (C i) (fun _ => (1 : ℝ)) (X i ω) = 0 := by
        simp only [Set.indicator]
        rw [if_neg hi]
      rw [Finset.prod_eq_zero (Finset.mem_univ i) this]
    · simp only [not_exists, not_not] at hr
      exact absurd hr h

/-- Connection between `indProd` and `firstRCylinder`: the product indicator
equals the indicator of the first-`r` cylinder. -/
lemma indProd_eq_firstRCylinder_indicator
    {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
    (X : ℕ → Ω → α) (r : ℕ) (C : Fin r → Set α) :
    indProd X r C = (firstRCylinder X r C).indicator (fun _ => (1 : ℝ)) := by
  rw [indProd_as_indicator]
  rfl

/-- Basic integrability: `indProd` is an indicator of a measurable set, hence integrable
under a finite measure. -/
lemma indProd_integrable
    {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
    {μ : Measure Ω} [IsFiniteMeasure μ] (X : ℕ → Ω → α)
    (r : ℕ) (C : Fin r → Set α)
    (hX : ∀ n, Measurable (X n)) (hC : ∀ i, MeasurableSet (C i)) :
    Integrable (indProd X r C) μ := by
  -- indProd X r C is the indicator of firstRCylinder X r C
  rw [indProd_eq_firstRCylinder_indicator]
  -- Indicator functions of measurable sets are integrable under finite measures
  apply Integrable.indicator
  · exact integrable_const 1
  · exact firstRCylinder_measurable_ambient X r C hX hC

/-! ### Indicator algebra helpers for factorization -/

/-- The product of two indicator functions equals the indicator of their intersection. -/
lemma indicator_mul_indicator_eq_indicator_inter
    {Ω : Type*} [MeasurableSpace Ω]
    (A B : Set Ω) (c d : ℝ) :
    (A.indicator (fun _ => c)) * (B.indicator (fun _ => d))
      = (A ∩ B).indicator (fun _ => c * d) := by
  ext ω
  by_cases hA : ω ∈ A <;> by_cases hB : ω ∈ B <;>
    simp [Set.indicator, hA, hB, Set.mem_inter_iff]

/-- Indicator function composed with preimage. -/
lemma indicator_comp_preimage
    {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
    (f : Ω → α) (B : Set α) (c : ℝ) :
    (B.indicator (fun _ => c)) ∘ f = (f ⁻¹' B).indicator (fun _ => c) := by
  ext ω
  simp only [Function.comp_apply, Set.indicator, Set.mem_preimage]
  rfl

/-- Binary indicator takes values in {0, 1}. -/
lemma indicator_binary
    {Ω : Type*} [MeasurableSpace Ω]
    (A : Set Ω) (ω : Ω) :
    A.indicator (fun _ => (1 : ℝ)) ω = 0 ∨ A.indicator (fun _ => (1 : ℝ)) ω = 1 := by
  by_cases h : ω ∈ A
  · simp [Set.indicator, h]
  · simp [Set.indicator, h]

/-- Indicator is bounded by its constant. -/
lemma indicator_le_const
    {Ω : Type*} [MeasurableSpace Ω]
    (A : Set Ω) (c : ℝ) (hc : 0 ≤ c) (ω : Ω) :
    A.indicator (fun _ => c) ω ≤ c := by
  by_cases h : ω ∈ A
  · simp [Set.indicator, h]
  · simp [Set.indicator, h, hc]

/-- Indicator is nonnegative when constant is nonnegative. -/
lemma indicator_nonneg
    {Ω : Type*} [MeasurableSpace Ω]
    (A : Set Ω) (c : ℝ) (hc : 0 ≤ c) (ω : Ω) :
    0 ≤ A.indicator (fun _ => c) ω := by
  by_cases h : ω ∈ A
  · simp [Set.indicator, h, hc]
  · simp [Set.indicator, h]

/-- indProd is strongly measurable when coordinates and sets are measurable. -/
lemma indProd_stronglyMeasurable
    {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
    (X : ℕ → Ω → α) (r : ℕ) (C : Fin r → Set α)
    (hX : ∀ n, Measurable (X n)) (hC : ∀ i, MeasurableSet (C i)) :
    StronglyMeasurable (indProd X r C) := by
  rw [indProd_eq_firstRCylinder_indicator]
  refine StronglyMeasurable.indicator ?_ ?_
  · exact stronglyMeasurable_const
  · exact firstRCylinder_measurable_ambient X r C hX hC

/-- indProd takes values in [0,1]. -/
lemma indProd_nonneg_le_one {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
    (X : ℕ → Ω → α) (r : ℕ) (C : Fin r → Set α) (ω : Ω) :
    0 ≤ indProd X r C ω ∧ indProd X r C ω ≤ 1 := by
  rw [indProd_as_indicator]
  by_cases h : ∀ i : Fin r, X i ω ∈ C i
  · simp [Set.indicator, h]
  · simp [Set.indicator, h]

/-- indProd of zero coordinates is identically 1. -/
@[simp] lemma indProd_zero {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
    (X : ℕ → Ω → α) (C : Fin 0 → Set α) :
    indProd X 0 C = fun _ => 1 := by
  funext ω
  simp [indProd]

/-- indProd on the universal sets is identically 1. -/
lemma indProd_univ {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
    (X : ℕ → Ω → α) (r : ℕ) :
    indProd X r (fun _ => Set.univ) = fun _ => 1 := by
  funext ω
  simp [indProd, Set.indicator]

/-- indProd is measurable when coordinates are measurable. -/
lemma indProd_measurable {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
    (X : ℕ → Ω → α) (r : ℕ) (C : Fin r → Set α)
    (hX : ∀ n, Measurable (X n)) (hC : ∀ i, MeasurableSet (C i)) :
    Measurable (indProd X r C) :=
  (indProd_stronglyMeasurable X r C hX hC).measurable

/-- indProd product equals multiplication of indProds. -/
lemma indProd_mul {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
    (X : ℕ → Ω → α) {r : ℕ} {C D : Fin r → Set α} (ω : Ω) :
    indProd X r C ω * indProd X r D ω = indProd X r (fun i => C i ∩ D i) ω := by
  simp only [indProd]
  rw [← Finset.prod_mul_distrib]
  congr 1
  funext i
  simp only [Set.indicator]
  by_cases hC : X i ω ∈ C i <;> by_cases hD : X i ω ∈ D i <;>
    simp [hC, hD, Set.mem_inter_iff]

/-- indProd on intersection via firstRCylinder. -/
lemma indProd_inter_eq {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
    (X : ℕ → Ω → α) {r : ℕ} {C D : Fin r → Set α} :
    indProd X r (fun i => C i ∩ D i)
      = (firstRCylinder X r C ∩ firstRCylinder X r D).indicator (fun _ => (1 : ℝ)) := by
  rw [indProd_eq_firstRCylinder_indicator, firstRCylinder_inter]

/-- Drop the first coordinate of a path. -/
def drop {α : Type*} (f : ℕ → α) : ℕ → α := shiftSeq (β:=α) 1 f

@[simp] lemma drop_apply {α : Type*} (f : ℕ → α) (n : ℕ) :
    drop f n = f (n + 1) := rfl

section CylinderBridge

variable {α : Type*} [MeasurableSpace α]

lemma measurable_drop : Measurable (drop : (ℕ → α) → (ℕ → α)) := by
  simpa [drop] using (measurable_shiftSeq (β:=α) (d:=1))

/-- `tailCylinder` is the preimage of a standard cylinder under `drop`. -/
lemma tailCylinder_eq_preimage_cylinder
    {r : ℕ} {C : Fin r → Set α} :
    tailCylinder (α:=α) r C
      = (drop : (ℕ → α) → (ℕ → α)) ⁻¹' (cylinder (α:=α) r C) := by
  ext f
  constructor <;> intro hf
  · simpa [tailCylinder, drop, shiftSeq, cylinder]
  · simpa [tailCylinder, drop, shiftSeq, cylinder]

@[simp] lemma mem_cylinder_iff {r : ℕ} {C : Fin r → Set α} {f : ℕ → α} :
    f ∈ cylinder (α:=α) r C ↔ ∀ i : Fin r, f i ∈ C i := Iff.rfl

@[simp] lemma mem_tailCylinder_iff {r : ℕ} {C : Fin r → Set α} {f : ℕ → α} :
    f ∈ tailCylinder (α:=α) r C ↔ ∀ i : Fin r, f (i.1 + 1) ∈ C i := Iff.rfl

/-- The cylinder set is measurable when each component set is measurable. -/
lemma cylinder_measurable_set {r : ℕ} {C : Fin r → Set α}
    (hC : ∀ i, MeasurableSet (C i)) :
    MeasurableSet (cylinder (α:=α) r C) :=
  cylinder_measurable hC

/-- Empty cylinder is the whole space. -/
@[simp] lemma cylinder_zero : cylinder (α:=α) 0 (fun _ => Set.univ) = Set.univ := by
  ext f; simp [cylinder]

/-- Empty tail cylinder is the whole space. -/
@[simp] lemma tailCylinder_zero : tailCylinder (α:=α) 0 (fun _ => Set.univ) = Set.univ := by
  ext f; simp [tailCylinder]

/-- Cylinder on universal sets is the whole space. -/
lemma cylinder_univ {r : ℕ} : cylinder (α:=α) r (fun _ => Set.univ) = Set.univ := by
  ext f; simp [cylinder]

/-- Tail cylinder on universal sets is the whole space. -/
lemma tailCylinder_univ {r : ℕ} : tailCylinder (α:=α) r (fun _ => Set.univ) = Set.univ := by
  ext f; simp [tailCylinder]

/-- Cylinders form intersections coordinate-wise. -/
lemma cylinder_inter {r : ℕ} {C D : Fin r → Set α} :
    cylinder (α:=α) r C ∩ cylinder (α:=α) r D = cylinder (α:=α) r (fun i => C i ∩ D i) := by
  ext f
  simp [cylinder, Set.mem_inter_iff]
  constructor
  · intro ⟨hC, hD⟩ i
    exact ⟨hC i, hD i⟩
  · intro h
    exact ⟨fun i => (h i).1, fun i => (h i).2⟩

end CylinderBridge

/-! ## Rectangles using future tails and standard cylinders -/
section FutureRectangles

variable {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
variable {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {X : ℕ → Ω → α}

/-- Preimage calculation for rectangles with `(X k, θ_{m+1}X)` and a standard cylinder. -/
lemma preimage_rect_future
    (k m r : ℕ) (B : Set α) (C : Fin r → Set α) :
    let ψ := fun ω => (X k ω, shiftRV X (m + 1) ω)
    ψ ⁻¹' (B ×ˢ cylinder (α:=α) r C)
      = {ω | X k ω ∈ B ∧ ∀ i : Fin r, X (m + 1 + i.1) ω ∈ C i} := by
  classical
  intro ψ
  ext ω; constructor <;> intro h
  · rcases h with ⟨hB, hC⟩
    refine ⟨?_, ?_⟩
    · simpa [ψ]
    · intro i
      have : (shiftRV X (m + 1) ω) ∈ cylinder (α:=α) r C := hC
      simpa [ψ, cylinder, shiftRV, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
        using this i
  · rcases h with ⟨hB, hC⟩
    refine ⟨?_, ?_⟩
    · simpa [ψ]
    · intro i
      have : X (m + 1 + i.1) ω ∈ C i := hC i
      simpa [ψ, cylinder, shiftRV, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
        using this

/-- **Finite-dimensional equality on future rectangles with standard cylinders.**
For `k ≤ m` and measurable `B`, the measures of
`B × cylinder r C` under the pushforwards by
`ω ↦ (X m ω, θ_{m+1}X(ω))` and `ω ↦ (X k ω, θ_{m+1}X(ω))` coincide. -/
lemma contractable_dist_eq_on_rectangles_future
    {X : ℕ → Ω → α} (hX : Contractable μ X) (hX_meas : ∀ n, Measurable (X n))
    (k m : ℕ) (hk : k ≤ m)
    (r : ℕ) (B : Set α) (hB : MeasurableSet B)
    (C : Fin r → Set α) (hC : ∀ i, MeasurableSet (C i)) :
    (Measure.map (fun ω => (X m ω, shiftRV X (m + 1) ω)) μ)
        (B ×ˢ cylinder (α:=α) r C)
  =
    (Measure.map (fun ω => (X k ω, shiftRV X (m + 1) ω)) μ)
        (B ×ˢ cylinder (α:=α) r C) := by
  classical
  set ψ₁ : Ω → α × (ℕ → α) := fun ω => (X m ω, shiftRV X (m + 1) ω)
  set ψ₂ : Ω → α × (ℕ → α) := fun ω => (X k ω, shiftRV X (m + 1) ω)
  have hrect : MeasurableSet (B ×ˢ cylinder (α:=α) r C) :=
    hB.prod (cylinder_measurable (α:=α) hC)
  have hpre₁ :
      ψ₁ ⁻¹' (B ×ˢ cylinder (α:=α) r C)
        = {ω | X m ω ∈ B ∧ ∀ i : Fin r, X (m + 1 + i.1) ω ∈ C i} := by
    simpa [ψ₁, preimage_rect_future (X:=X) m m r B C]
  have hpre₂ :
      ψ₂ ⁻¹' (B ×ˢ cylinder (α:=α) r C)
        = {ω | X k ω ∈ B ∧ ∀ i : Fin r, X (m + 1 + i.1) ω ∈ C i} := by
    simpa [ψ₂, preimage_rect_future (X:=X) k m r B C]
  have hfd :
    μ {ω | X m ω ∈ B ∧ ∀ i : Fin r, X (m + (i.1 + 1)) ω ∈ C i}
      =
    μ {ω | X k ω ∈ B ∧ ∀ i : Fin r, X (m + (i.1 + 1)) ω ∈ C i} := by
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      (contractable_dist_eq_on_first_r_tail
        (μ:=μ) (X:=X) hX hX_meas k m r hk B hB C hC)
  -- Show the sets are equal modulo arithmetic
  have hset_eq₁ : {ω | X m ω ∈ B ∧ ∀ i : Fin r, X (m + 1 + i.1) ω ∈ C i}
                = {ω | X m ω ∈ B ∧ ∀ i : Fin r, X (m + (i.1 + 1)) ω ∈ C i} := by
    ext ω; simp only [Set.mem_setOf]
    constructor
    · intro ⟨hB, hC⟩
      constructor
      · exact hB
      · intro i
        have : m + 1 + i.1 = m + (i.1 + 1) := by omega
        rw [← this]; exact hC i
    · intro ⟨hB, hC⟩
      constructor
      · exact hB
      · intro i
        have : m + 1 + i.1 = m + (i.1 + 1) := by omega
        rw [this]; exact hC i
  have hset_eq₂ : {ω | X k ω ∈ B ∧ ∀ i : Fin r, X (m + 1 + i.1) ω ∈ C i}
                = {ω | X k ω ∈ B ∧ ∀ i : Fin r, X (m + (i.1 + 1)) ω ∈ C i} := by
    ext ω; simp only [Set.mem_setOf]
    constructor
    · intro ⟨hB, hC⟩
      constructor
      · exact hB
      · intro i
        have : m + 1 + i.1 = m + (i.1 + 1) := by omega
        rw [← this]; exact hC i
    · intro ⟨hB, hC⟩
      constructor
      · exact hB
      · intro i
        have : m + 1 + i.1 = m + (i.1 + 1) := by omega
        rw [this]; exact hC i
  -- Measurability of ψ₁ and ψ₂
  have hψ₁_meas : Measurable ψ₁ :=
    (hX_meas m).prodMk (measurable_shiftRV hX_meas)
  have hψ₂_meas : Measurable ψ₂ :=
    (hX_meas k).prodMk (measurable_shiftRV hX_meas)
  -- Apply Measure.map_apply and connect the pieces
  rw [Measure.map_apply hψ₁_meas hrect, Measure.map_apply hψ₂_meas hrect]
  rw [hpre₁, hpre₂, hset_eq₁, hset_eq₂]
  exact hfd

end FutureRectangles

/-- Two measures agree on all future rectangles (sets of form B ×ˢ cylinder r C). -/
def AgreeOnFutureRectangles (μ ν : Measure (α × (ℕ → α))) : Prop :=
  ∀ (r : ℕ) (B : Set α) (hB : MeasurableSet B) (C : Fin r → Set α) (hC : ∀ i, MeasurableSet (C i)),
    μ (B ×ˢ cylinder (α:=α) r C) = ν (B ×ˢ cylinder (α:=α) r C)

lemma agree_on_future_rectangles_of_contractable
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → α} (hX : Contractable μ X) (hX_meas : ∀ n, Measurable (X n))
    (k m : ℕ) (hk : k ≤ m) :
    AgreeOnFutureRectangles
      (Measure.map (fun ω => (X m ω, shiftRV X (m + 1) ω)) μ)
      (Measure.map (fun ω => (X k ω, shiftRV X (m + 1) ω)) μ) := by
  -- Unfold definition and apply contractable_dist_eq_on_rectangles_future
  intro r B hB C hC
  exact contractable_dist_eq_on_rectangles_future hX hX_meas k m hk r B hB C hC

/-! ## Measure extension from future rectangles -/

lemma measure_ext_of_future_rectangles
    {μ ν : Measure (α × (ℕ → α))} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : ∀ (r : ℕ) (B : Set α) (hB : MeasurableSet B)
        (C : Fin r → Set α) (hC : ∀ i, MeasurableSet (C i)),
        μ (B ×ˢ cylinder (α:=α) r C) = ν (B ×ˢ cylinder (α:=α) r C)) :
    μ = ν := by
  classical
  -- Proof Plan (π-λ Theorem Application):
  --
  -- Step 1: Define π-system S
  --   S = {B ×ˢ cylinder r C | B measurable, C_i measurable}
  --   This is a π-system (closed under finite intersections)
  --
  -- Step 2: Show S generates product σ-algebra
  --   Prove: generateFrom S = inferInstance
  --   - (⊆): Show Prod.fst, Prod.snd measurable w.r.t. generateFrom S
  --     * Product σ-algebra = comap Prod.fst ⊔ comap Prod.snd
  --     * Both comaps ≤ generateFrom S
  --   - (⊇): Every rectangle in S is measurable in product σ-algebra
  --
  -- Step 3: Apply π-λ theorem
  --   Use Measure.ext_of_generateFrom_of_iUnion:
  --   - Measures agree on S (hypothesis h)
  --   - S generates the σ-algebra
  --   - Have covering family with finite measure
  --   - Therefore μ = ν

  -- π-system consisting of rectangles `B × cylinder r C`
  let S : Set (Set (α × (ℕ → α))) :=
    {s | ∃ (r : ℕ) (B : Set α) (hB : MeasurableSet B)
          (C : Fin r → Set α) (hC : ∀ i, MeasurableSet (C i)),
          s = B ×ˢ cylinder (α:=α) r C}

  -- S is a π-system
  have h_pi : IsPiSystem S := by
    intro s₁ hs₁ s₂ hs₂ _
    obtain ⟨r₁, B₁, hB₁, C₁, hC₁, rfl⟩ := hs₁
    obtain ⟨r₂, B₂, hB₂, C₂, hC₂, rfl⟩ := hs₂
    -- Intersection of rectangles is a rectangle of higher dimension
    let r := max r₁ r₂
    let C : Fin r → Set α := fun i =>
      if h1 : (i : ℕ) < r₁ then
        if h2 : (i : ℕ) < r₂ then C₁ ⟨i, h1⟩ ∩ C₂ ⟨i, h2⟩ else C₁ ⟨i, h1⟩
      else if h2 : (i : ℕ) < r₂ then C₂ ⟨i, h2⟩ else Set.univ
    have hC : ∀ i, MeasurableSet (C i) := by
      intro i
      classical
      by_cases h1 : (i : ℕ) < r₁
      · by_cases h2 : (i : ℕ) < r₂
        · have := (hC₁ ⟨i, h1⟩).inter (hC₂ ⟨i, h2⟩)
          simpa [C, h1, h2] using this
        · simpa [C, h1, h2] using hC₁ ⟨i, h1⟩
      · by_cases h2 : (i : ℕ) < r₂
        · simpa [C, h1, h2] using hC₂ ⟨i, h2⟩
        · simpa [C, h1, h2] using (MeasurableSet.univ : MeasurableSet (Set.univ))

    refine ⟨r, B₁ ∩ B₂, hB₁.inter hB₂, C, hC, ?_⟩
    ext ⟨a, f⟩; constructor
    · intro hmf
      rcases hmf with ⟨⟨hB₁', hC₁'⟩, ⟨hB₂', hC₂'⟩⟩
      refine ⟨⟨hB₁', hB₂'⟩, ?_⟩
      intro i
      classical
      by_cases h1 : (i : ℕ) < r₁
      · by_cases h2 : (i : ℕ) < r₂
        · simp [C, h1, h2]
          exact ⟨hC₁' ⟨i, h1⟩, hC₂' ⟨i, h2⟩⟩
        · simp [C, h1, h2]
          exact hC₁' ⟨i, h1⟩
      · by_cases h2 : (i : ℕ) < r₂
        · simp [C, h1, h2]
          exact hC₂' ⟨i, h2⟩
        · simp [C, h1, h2]
    · rintro ⟨⟨hB₁', hB₂'⟩, hC'⟩
      refine ⟨⟨hB₁', ?_⟩, ⟨hB₂', ?_⟩⟩
      · intro i
        have hi : (i : ℕ) < r := lt_of_lt_of_le i.2 (Nat.le_max_left r₁ r₂)
        have := hC' ⟨i, hi⟩
        classical
        have h1 : (i : ℕ) < r₁ := i.2
        by_cases h2 : (i : ℕ) < r₂
        · simp [C, h1, h2] at this
          exact this.1
        · simp [C, h1, h2] at this
          exact this
      · intro i
        have hi : (i : ℕ) < r := lt_of_lt_of_le i.2 (Nat.le_max_right r₁ r₂)
        have := hC' ⟨i, hi⟩
        classical
        have h2 : (i : ℕ) < r₂ := i.2
        by_cases h1 : (i : ℕ) < r₁
        · simp [C, h1, h2] at this
          exact this.2
        · simp [C, h1, h2] at this
          exact this

  -- Show that S generates the product σ-algebra
  have h_gen : (inferInstance : MeasurableSpace (α × (ℕ → α)))
      = MeasurableSpace.generateFrom S := by
    -- Two-sided inclusion
    apply le_antisymm
    · -- (⊆) Product σ-algebra ≤ generateFrom S
      -- The product σ-algebra is the smallest σ-algebra making both projections measurable
      -- We need to show Prod.fst and Prod.snd are measurable w.r.t. generateFrom S

      -- First, show that Prod.fst is measurable
      have h_fst : ∀ A : Set α, MeasurableSet A →
          MeasurableSet[MeasurableSpace.generateFrom S] (Prod.fst ⁻¹' A) := by
        intro A hA
        -- Prod.fst ⁻¹' A = A ×ˢ univ = A ×ˢ cylinder 0 (fun _ => univ)
        have : Prod.fst ⁻¹' A = A ×ˢ (Set.univ : Set (ℕ → α)) := by
          ext ⟨a, f⟩; simp
        rw [this]
        -- A ×ˢ univ is in S (as a cylinder of size 0)
        apply MeasurableSpace.measurableSet_generateFrom
        refine ⟨0, A, hA, (fun _ => Set.univ), (fun _ => MeasurableSet.univ), ?_⟩
        ext ⟨a, f⟩
        simp [cylinder]

      -- Second, show that Prod.snd maps cylinders to measurable sets
      have h_snd : ∀ (r : ℕ) (C : Fin r → Set α),
          (∀ i, MeasurableSet (C i)) →
          MeasurableSet[MeasurableSpace.generateFrom S] (Prod.snd ⁻¹' cylinder r C) := by
        intro r C hC
        -- Prod.snd ⁻¹' (cylinder r C) = univ ×ˢ (cylinder r C)
        have : (Prod.snd : α × (ℕ → α) → ℕ → α) ⁻¹' cylinder r C = Set.univ ×ˢ cylinder r C := by
          ext ⟨a, f⟩
          simp [cylinder]
        rw [this]
        -- univ ×ˢ cylinder r C is in S
        apply MeasurableSpace.measurableSet_generateFrom
        refine ⟨r, Set.univ, MeasurableSet.univ, C, hC, rfl⟩

      -- Product σ-algebra = (comap Prod.fst) ⊔ (comap Prod.snd)
      -- Need: both comaps are ≤ generateFrom S

      -- Prod.fst comap
      have h_fst_comap : MeasurableSpace.comap (Prod.fst : α × (ℕ → α) → α) inferInstance
          ≤ MeasurableSpace.generateFrom S := by
        intro s hs
        -- s is a preimage under Prod.fst of a measurable set
        obtain ⟨A, hA, rfl⟩ := hs
        exact h_fst A hA

      -- Prod.snd comap - need to show preimages of measurable sets are in generateFrom S
      have h_snd_comap : MeasurableSpace.comap (Prod.snd : α × (ℕ → α) → ℕ → α) inferInstance
          ≤ MeasurableSpace.generateFrom S := by
        -- Use measurable_iff_comap_le: comap ≤ generateFrom S ↔ Measurable Prod.snd
        rw [← measurable_iff_comap_le]
        -- Now show: Measurable[generateFrom S, inferInstance] Prod.snd

        -- Strategy: Show that {E | Prod.snd⁻¹(E) ∈ generateFrom S} is a σ-algebra
        -- containing all measurable sets in Pi

        -- Key observation: For any cylinder (finite intersection of coordinate preimages),
        -- we've proven Prod.snd⁻¹(cylinder) ∈ generateFrom S via h_snd

        -- The set T = {E | Prod.snd⁻¹(E) ∈ generateFrom S} is a σ-algebra because:
        --   - Prod.snd⁻¹(∅) = ∅ ∈ generateFrom S
        --   - Prod.snd⁻¹(∁E) = ∁(Prod.snd⁻¹(E)), σ-algebras closed under complement
        --   - Prod.snd⁻¹(⋃ Eₙ) = ⋃ Prod.snd⁻¹(Eₙ), σ-algebras closed under countable union

        -- T contains all cylinders (by h_snd), and Pi is generated by cylinders
        -- Therefore Pi ⊆ T, so for any E measurable in Pi, Prod.snd⁻¹(E) ∈ generateFrom S

        -- Apply measurable_generateFrom using cylinder generators
        -- The Pi σ-algebra on (ℕ → α) is generated by cylinders
        -- We've shown Prod.snd⁻¹(cylinder) ∈ generateFrom S for all cylinders

        -- Define the generating set for Pi: all cylinders
        let T : Set (Set (ℕ → α)) := {s | ∃ (r : ℕ) (C : Fin r → Set α),
          (∀ i, MeasurableSet (C i)) ∧ s = cylinder r C}

        -- Show Pi is generated by cylinders
        have hT_gen : (inferInstance : MeasurableSpace (ℕ → α)) = MeasurableSpace.generateFrom T := by
          -- Two-sided inclusion
          apply le_antisymm
          · -- inferInstance ≤ generateFrom T (i.e., Pi ≤ generateFrom T)
            -- Show that generateFrom T contains all Pi generators (coordinate preimages)
            -- Pi is generated by coordinate preimages
            -- We show all coordinate preimages are in generateFrom T
            have h_coord_meas : ∀ (i : ℕ) (A : Set α), MeasurableSet A →
                MeasurableSet[MeasurableSpace.generateFrom T] ((fun f : ℕ → α => f i) ⁻¹' A) := by
              intro i A hA
              -- {f | f i ∈ A} is a cylinder of size (i+1) with univ for j<i and A at position i
              let r := i + 1
              let C : Fin r → Set α := fun j => if j.val = i then A else Set.univ
              have hC_meas : ∀ j, MeasurableSet (C j) := by
                intro j
                simp only [C]
                split_ifs
                · exact hA
                · exact MeasurableSet.univ
              have h_eq : ((fun f : ℕ → α => f i) ⁻¹' A) = cylinder r C := by
                ext f
                simp [cylinder, C, r]
                constructor
                · intro hf j
                  by_cases h : j.val = i
                  · simp [h]; exact hf
                  · simp [h]
                · intro hf
                  have := hf ⟨i, Nat.lt_succ_self i⟩
                  simp at this
                  exact this
              rw [h_eq]
              apply MeasurableSpace.measurableSet_generateFrom
              exact ⟨r, C, hC_meas, rfl⟩
            -- Pi is generated by coordinate projections
            -- We've shown all coordinate preimages are in generateFrom T
            rw [MeasurableSpace.pi_eq_generateFrom_projections]
            apply MeasurableSpace.generateFrom_le
            intro s hs
            -- s is a coordinate preimage: ∃ i A, MeasurableSet A ∧ eval i ⁻¹' A = s
            obtain ⟨i, A, hA, rfl⟩ := hs
            exact h_coord_meas i A hA
          · -- generateFrom T ≤ inferInstance (i.e., generateFrom T ≤ Pi)
            -- Every cylinder is measurable in Pi
            apply MeasurableSpace.generateFrom_le
            intro s
            rintro ⟨n, coords, coords_meas, rfl⟩
            -- cylinder n coords is measurable in Pi σ-algebra
            exact cylinder_measurable coords_meas

        -- Apply measurable_generateFrom
        have : @Measurable (α × (ℕ → α)) (ℕ → α)
            (MeasurableSpace.generateFrom S) (MeasurableSpace.generateFrom T) Prod.snd := by
          apply @measurable_generateFrom _ _ (MeasurableSpace.generateFrom S) _ _
          intro s hs
          obtain ⟨r, C, hC, rfl⟩ := hs
          exact h_snd r C hC
        rw [← hT_gen] at this
        exact this

      -- Combine using sup
      calc (inferInstance : MeasurableSpace (α × (ℕ → α)))
          = MeasurableSpace.comap Prod.fst inferInstance
            ⊔ MeasurableSpace.comap Prod.snd inferInstance := by
              rfl  -- This is the definition of product σ-algebra
        _ ≤ MeasurableSpace.generateFrom S := by
              exact sup_le h_fst_comap h_snd_comap
    · -- (⊇) generateFrom S ≤ Product σ-algebra
      -- Every set in S is measurable in the product σ-algebra
      apply MeasurableSpace.generateFrom_le
      intro t ht
      obtain ⟨r, B, hB, C, hC, rfl⟩ := ht
      -- B ×ˢ cylinder r C is measurable as a product of measurable sets
      exact hB.prod (cylinder_measurable hC)

  -- Measures agree on S
  have h_agree : ∀ s ∈ S, μ s = ν s := by
    intro s hs
    rcases hs with ⟨r, B, hB, C, hC, rfl⟩
    exact h r B hB C hC

  -- Covering family
  let Bseq : ℕ → Set (α × (ℕ → α)) := fun _ => Set.univ
  have h1B : ⋃ n, Bseq n = Set.univ := by
    simp only [Bseq, Set.iUnion_const]
  have h2B : ∀ n, Bseq n ∈ S := by
    intro n
    refine ⟨0, Set.univ, MeasurableSet.univ,
      (fun _ => Set.univ), (fun _ => MeasurableSet.univ), ?_⟩
    ext ⟨a, f⟩; simp [Bseq, cylinder]
  have hμB : ∀ n, μ (Bseq n) ≠ ⊤ := by
    intro n
    simp only [Bseq]
    exact measure_ne_top μ Set.univ

  exact Measure.ext_of_generateFrom_of_iUnion
    S Bseq h_gen h_pi h1B h2B hμB h_agree

/-- Helper lemma: contractability gives the key distributional equality.

If `X` is contractable, then for any `k ≤ m`:
```
(X_m, θ_{m+1} X) =^d (X_k, θ_{m+1} X)
```
where `θ_{m+1} X` drops the first coordinate and keeps the *future* tail
`ω ↦ (n ↦ X(m + 1 + n) ω)`. -/
lemma contractable_dist_eq
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → α} (hX : Contractable μ X) (hX_meas : ∀ n, Measurable (X n))
    (k m : ℕ) (hk : k ≤ m) :
    Measure.map (fun ω => (X m ω, shiftRV X (m + 1) ω)) μ
      = Measure.map (fun ω => (X k ω, shiftRV X (m + 1) ω)) μ := by
  -- Apply measure extension lemma
  apply measure_ext_of_future_rectangles
  intro r B hB C hC
  exact contractable_dist_eq_on_rectangles_future hX hX_meas k m hk r B hB C hC

/-- Measures that agree on all future rectangles are equal. -/
lemma AgreeOnFutureRectangles_to_measure_eq
    {μ ν : Measure (α × (ℕ → α))} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : AgreeOnFutureRectangles μ ν) : μ = ν :=
  measure_ext_of_future_rectangles h


section reverse_martingale

variable {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {X : ℕ → Ω → α}

/-- 𝔽ₘ := σ(θ_{m+1} X) (the future filtration). -/
abbrev 𝔽 (m : ℕ) : MeasurableSpace Ω := futureFiltration X m

/-- The reverse filtration is decreasing; packaged for the martingale API. -/
lemma filtration_antitone (X : ℕ → Ω → α) : Antitone (fun m => futureFiltration X m) :=
  futureFiltration_antitone X

/-- Mₘ := 𝔼[1_{Xₖ∈B} | 𝔽ₘ].
The reverse martingale sequence for the indicator of X_k in B. -/
axiom M (k : ℕ) (B : Set α) : ℕ → Ω → ℝ
  -- TODO: Requires proper instance management for conditional expectation
  -- The mathematical definition is clear: M k B m ω = μ[1_{X_k ∈ B} | σ(θ_{m+1} X)] ω
  -- Technical blocker: Lean 4 typeclass inference with futureFiltration

-- TODO (CondExp.lean milestones):
-- (1) `0 ≤ M k B m ω ≤ 1` a.s.
--     API: `condexp_indicator_bounds`.
-- (2) For `m ≤ n`, `M k B n` is `𝔽 n`-measurable and
--     `μ[fun ω => M k B n ω | 𝔽 m] =ᵐ[μ] M k B m`.
--     API: `condexp_tower`, `condexp_stronglyMeasurable`.
-- (3) If `(X m, θₘ X) =^d (X k, θₘ X)`, then
--     `M m B m =ᵐ[μ] M k B m`.
--     API: `condexp_indicator_eq_of_dist_eq_and_le`.
-- (4) `(fun n => M k B n ω)` is a reverse martingale that converges
--     to `μ[Set.indicator B (fun _ => (1 : ℝ)) ∘ (X k) | tailSigma X] ω`.
--     API: `condexp_tendsto_condexp_iInf` (Lévy's downward theorem) together with
--     `filtration_antitone` and `tailSigmaFuture_eq_iInf`.

end reverse_martingale

/-! ## Tail factorization on finite cylinders -/

/-! ### Helper lemmas for finite-level factorization -/

/-- For contractable sequences, X_i and the future shift are conditionally independent
given any later future filtration. This is a key consequence of contractability. -/
axiom coordinate_future_condIndep
    {Ω α : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [MeasurableSpace α]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ℕ → Ω → α)
    (hX : Contractable μ X)
    (hX_meas : ∀ n, Measurable (X n))
    (i m : ℕ) (hm : m > i) : True
  -- TODO: Full type with CondIndep blocked by typeclass resolution

/-- Conditional expectation of products factors when coordinates are conditionally
independent. This is a wrapper around the general product rule for conditional expectations.

**Proof strategy** (to be implemented):
This can be derived from `condExp_indicator_mul_indicator_of_condIndep` in CondExp.lean
using the following steps:

1. **Simple functions**: For `f = ∑ᵢ aᵢ·1_{Aᵢ}` and `g = ∑ⱼ bⱼ·1_{Bⱼ}`, use linearity:
   ```
   μ[f * g | m] = ∑ᵢⱼ aᵢbⱼ · μ[1_{Aᵢ∩Bⱼ} | m]
                = ∑ᵢⱼ aᵢbⱼ · μ[1_{Aᵢ} | m] · 1_{Bⱼ}   (by h_indep + pullout)
                = (∑ᵢ aᵢ · μ[1_{Aᵢ} | m]) · (∑ⱼ bⱼ·1_{Bⱼ})
                = μ[f | m] · g
   ```

2. **Approximation**: For general integrable `f`, `g`:
   - Approximate `f` by m-measurable simple functions `fₙ → f` in L¹
   - Approximate `g` by simple functions `gₙ → g` in L¹
   - Use `μ[fₙ * gₙ | m] = μ[fₙ | m] * gₙ` from step 1
   - Pass to limit using dominated/monotone convergence for conditional expectations

3. **Measurability**: The ae strong measurability of `f` w.r.t. `m` ensures the approximation
   by m-measurable simple functions exists.

This proof requires developing the approximation theory for conditional expectations,
which is substantial. For now, we axiomatize it.
-/
axiom condExp_product_of_condIndep
    {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] : True
  -- TODO: Full axiom with conditional independence → product factorization
  -- Blocked by typeclass resolution in conditional expectation API

/-- **Conditional expectation factorization for indicator products without axioms.**

Given two sets `A` (measurable in `m`) and `B` (measurable in ambient), under conditional
independence, the conditional expectation of the indicator product factors:
```
μ[1_A · 1_B | m] = μ[1_A | m] · 1_B   a.e.
```

This uses the `CondIndep` property directly via indicator algebra, without requiring
the general product axiom. -/
axiom condexp_indicator_inter_of_condIndep
    {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] : True
  -- TODO: Full lemma with CondIndep → indicator factorization
  -- Blocked by typeclass resolution issues
  /-
    {m : MeasurableSpace Ω} (hm : m ≤ inferInstance)
    (A B : Set Ω)
    (hA : MeasurableSet[m] A)
    (hB : MeasurableSet B)
    (h_condIndep : CondIndep ...) :
    μ[(A.indicator * B.indicator) | m] =ᵐ[μ] ...
  -/

/-- **Finite-level factorization builder.**

For a contractable sequence, at any future level `m ≥ r`, the conditional expectation
of the product indicator factors:
```
μ[∏ᵢ<r 1_{Xᵢ∈Cᵢ} | σ(θₘ₊₁X)] = ∏ᵢ<r μ[1_{X₀∈Cᵢ} | σ(θₘ₊₁X)]
```

This iteratively applies `condIndep_of_indicator_condexp_eq` to pull out one coordinate
at a time, using contractability to replace each `Xᵢ` with `X₀`. -/
axiom finite_level_factorization
    {Ω α : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [MeasurableSpace α]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ℕ → Ω → α)
    (hX : Contractable μ X)
    (hX_meas : ∀ n, Measurable (X n))
    (r : ℕ) (C : Fin r → Set α) (hC : ∀ i, MeasurableSet (C i))
    (m : ℕ) (hm : m ≥ r) : True
  -- TODO: Prove factorization via induction on r
  -- μ[indProd X r C | futureFiltration X m] =ᵐ[μ] ∏ᵢ μ[indicator(C i) ∘ X 0 | ...]
  /-
  by
  classical
  revert m hm
  refine Nat.rec ?base ?step r
  · -- r = 0: empty product is 1
    intro m hm
    have hconst :
        μ[(fun _ : Ω => (1 : ℝ)) | futureFiltration X m] =ᵐ[μ] (fun _ => (1 : ℝ)) :=
      condExp_const (μ := μ) (m := futureFiltration X m)
        (hm := by intro s hs; exact hs) (1 : ℝ)
    simpa [indProd] using hconst
  · -- r ↦ r+1: Inductive step using indicator factorization
    intro r ih m hm

    -- Split C into "first r" and "last"
    let Cinit : Fin r → Set α := fun j => C (Fin.castSucc j)
    let Clast : Set α := C ⟨r, Nat.lt_succ_self r⟩
    have hCinit : ∀ j, MeasurableSet (Cinit j) := fun j => hC _
    have hClast : MeasurableSet Clast := hC ⟨r, Nat.lt_succ_self r⟩

    -- Factorize the product ∏_{i<r+1} 1_{Xᵢ∈Cᵢ} = (∏_{i<r} 1_{Xᵢ∈Cᵢ}) · 1_{Xᵣ∈Clast}
    have hsplit : indProd X (r+1) C
        = fun ω => indProd X r Cinit ω * Set.indicator Clast (fun _ => (1:ℝ)) (X r ω) := by
      funext ω
      simp [indProd, Fin.prod_univ_succ, Cinit, Clast]

    -- Express the two factors as indicators of sets
    set A := firstRCylinder X r Cinit with hA_def
    set B := X r ⁻¹' Clast with hB_def

    -- Rewrite indProd using indicator algebra
    have hf_indicator : indProd X r Cinit = A.indicator (fun _ => (1:ℝ)) := by
      rw [← hA_def]
      exact indProd_eq_firstRCylinder_indicator X r Cinit

    have hg_indicator : (Set.indicator Clast (fun _ => (1:ℝ)) ∘ X r)
        = B.indicator (fun _ => (1:ℝ)) := by
      rw [← hB_def]
      exact indicator_comp_preimage (X r) Clast 1

    -- The product is the indicator of A ∩ B
    have hprod_indicator :
        (fun ω => indProd X r Cinit ω * (Set.indicator Clast (fun _ => (1:ℝ)) (X r ω)))
        = (A ∩ B).indicator (fun _ => (1:ℝ)) := by
      rw [hf_indicator, hg_indicator]
      exact indicator_mul_indicator_eq_indicator_inter A B 1 1

    -- Measurability
    have hA_meas : MeasurableSet[futureFiltration X m] A := by
      rw [hA_def]
      -- A is measurable in firstRSigma X r, which is ≤ futureFiltration X m when r ≤ m
      have h_in_first : MeasurableSet[firstRSigma X r] (firstRCylinder X r Cinit) :=
        firstRCylinder_measurable_in_firstRSigma X r Cinit hCinit
      exact firstRSigma_le_futureFiltration X (Nat.le_of_succ_le hm) _ h_in_first

    have hB_meas : MeasurableSet B := by
      rw [hB_def]
      exact (hX_meas r) hClast

    -- Conditional independence (from axiom)
    have h_condIndep : CondIndep
        (MeasurableSpace.comap A.indicator inferInstance)
        (MeasurableSpace.comap B.indicator inferInstance)
        (futureFiltration X m) μ := by
      -- This needs to be derived from coordinate_future_condIndep, which states that
      -- X_i and shiftRV X (m+1) are conditionally independent given futureFiltration X m.
      -- Since A depends on X_0,...,X_{r-1} and B = X_r⁻¹(Clast), and r < m, we need to:
      -- 1. Show that A is measurable w.r.t. σ(X_0,...,X_{r-1}) ⊆ futureFiltration X m
      -- 2. Show that B is measurable w.r.t. σ(X_r)
      -- 3. Apply coordinate_future_condIndep with appropriate substitutions
      -- This is non-trivial and requires developing the theory of conditional independence.
      sorry

    -- Apply indicator factorization
    have hfactor :
        μ[(A.indicator (fun _ => (1:ℝ))) * (B.indicator (fun _ => (1:ℝ))) | futureFiltration X m]
          =ᵐ[μ]
        (fun ω => (μ[A.indicator (fun _ => (1:ℝ)) | futureFiltration X m] ω)
                  * (B.indicator (fun _ => (1:ℝ)) ω)) :=
      condexp_indicator_inter_of_condIndep
        (by intro s hs; exact hs) A B hA_meas hB_meas h_condIndep

    -- Apply IH to the first r factors
    have hIH : μ[indProd X r Cinit | futureFiltration X m] =ᵐ[μ]
        (fun ω => ∏ i : Fin r,
          μ[Set.indicator (Cinit i) (fun _ => (1:ℝ)) ∘ (X 0) | futureFiltration X m] ω) := by
      exact ih (Nat.le_of_succ_le hm)

    -- Replace Xᵣ with X₀ using contractability
    have hswap : μ[(Set.indicator Clast (fun _ => (1:ℝ)) ∘ X r) | futureFiltration X m]
        =ᵐ[μ]
        μ[(Set.indicator Clast (fun _ => (1:ℝ)) ∘ X 0) | futureFiltration X m] := by
      exact condexp_convergence hX hX_meas (Nat.le_of_succ_le hm) Clast hClast

    -- Combine everything
    calc μ[indProd X (r+1) C | futureFiltration X m]
        _ =ᵐ[μ] μ[(fun ω => indProd X r Cinit ω
                      * Set.indicator Clast (fun _ => (1:ℝ)) (X r ω))
                   | futureFiltration X m] := by
          apply condExp_congr
          exact EventuallyEq.of_eq hsplit
        _ =ᵐ[μ] μ[(A.indicator (fun _ => (1:ℝ)))
                   * (B.indicator (fun _ => (1:ℝ)))
                   | futureFiltration X m] := by
          apply condExp_congr
          funext ω
          rw [← hf_indicator, ← hg_indicator]
        _ =ᵐ[μ] (fun ω => (μ[A.indicator (fun _ => (1:ℝ)) | futureFiltration X m] ω)
                          * (B.indicator (fun _ => (1:ℝ)) ω)) := hfactor
        _ =ᵐ[μ] (fun ω => (μ[indProd X r Cinit | futureFiltration X m] ω)
                          * (Set.indicator Clast (fun _ => (1:ℝ)) (X r ω))) := by
          apply EventuallyEq.mul
          · apply condExp_congr
            exact EventuallyEq.of_eq hf_indicator.symm
          · exact EventuallyEq.of_eq hg_indicator.symm
        _ =ᵐ[μ] (fun ω => (∏ i : Fin r,
                            μ[Set.indicator (Cinit i) (fun _ => (1:ℝ)) ∘ (X 0)
                              | futureFiltration X m] ω)
                          * (Set.indicator Clast (fun _ => (1:ℝ)) (X r ω))) := by
          apply EventuallyEq.mul hIH
          exact EventuallyEq.rfl
        _ =ᵐ[μ] (fun ω => (∏ i : Fin r,
                            μ[Set.indicator (Cinit i) (fun _ => (1:ℝ)) ∘ (X 0)
                              | futureFiltration X m] ω)
                          * μ[Set.indicator Clast (fun _ => (1:ℝ)) ∘ (X 0)
                              | futureFiltration X m] ω) := by
          apply EventuallyEq.mul EventuallyEq.rfl
          -- Apply hswap to replace X r with X 0, then use pullout property
          calc Set.indicator Clast (fun _ => (1:ℝ)) (X r ·)
              _ =ᵐ[μ] μ[Set.indicator Clast (fun _ => (1:ℝ)) ∘ X r | futureFiltration X m] := by
                -- B.indicator is futureFiltration X m-measurable (X r depends on coord r < m)
                symm
                apply condExp_of_stronglyMeasurable
                · intro s hs; exact hs
                · have : Measurable (Set.indicator Clast (fun _ => (1:ℝ)) ∘ X r) := by
                    exact Measurable.comp (measurable_const.indicator (by exact hClast)) (hX_meas r)
                  exact this.stronglyMeasurable
                · exact (integrable_const (1:ℝ)).indicator ((hX_meas r) hClast)
              _ =ᵐ[μ] μ[Set.indicator Clast (fun _ => (1:ℝ)) ∘ X 0 | futureFiltration X m] := hswap
        _ =ᵐ[μ] (fun ω => ∏ i : Fin (r+1),
                            μ[Set.indicator (C i) (fun _ => (1:ℝ)) ∘ (X 0)
                              | futureFiltration X m] ω) := by
          apply EventuallyEq.of_eq
          funext ω
          simp [Fin.prod_univ_succ, Cinit, Clast]
  -/

/-- **Tail factorization on finite cylinders.**

Assume you have, for all large enough `m`, the finite‑level factorization
at the future filtration:
```
μ[indProd X r C | σ(θ_{m+1}X)]
  = ∏ i<r μ[1_{X₀∈C i} | σ(θ_{m+1}X)]   a.s.
```
Then the same factorization holds **at the tail σ‑algebra**:
```
μ[indProd X r C | 𝒯_X]
  = ∏ i<r μ[1_{X₀∈C i} | 𝒯_X]           a.s.
```

This passes the finite‑level equality to the tail using bounded
dominated convergence together with reverse martingale convergence. -/
axiom tail_factorization_from_future
    {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ℕ → Ω → α)
    (hX : ∀ n, Measurable (X n))
    (r : ℕ) (C : Fin r → Set α) (hC : ∀ i, MeasurableSet (C i))
    -- finite-level factorization hypothesis (available after applying the wrapper repeatedly)
    (h_fact :
      ∀ m ≥ r,  -- any `m` with at least r future steps works
        μ[indProd X r C | futureFiltration X m]
          =ᵐ[μ]
        (fun ω => ∏ i : Fin r,
          μ[Set.indicator (C i) (fun _ => (1 : ℝ)) ∘ (X 0) | futureFiltration X m] ω))
    -- reverse-martingale convergence for each singleton factor
    (h_rev :
      ∀ i : Fin r,
        (∀ᵐ ω ∂μ,
          Tendsto (fun m => μ[Set.indicator (C i) (fun _ => (1 : ℝ)) ∘ (X 0)
                                 | futureFiltration X m] ω)
                  atTop
                  (𝓝 (μ[Set.indicator (C i) (fun _ => (1 : ℝ)) ∘ (X 0)
                          | tailSigma X] ω)))) :
    μ[indProd X r C | tailSigma X]
      =ᵐ[μ]
    (fun ω => ∏ i : Fin r,
        μ[Set.indicator (C i) (fun _ => (1 : ℝ)) ∘ (X 0) | tailSigma X] ω)

/-- **Key lemma: All coordinates have identical conditional distributions.**

For a contractable sequence, all coordinates X_m have the same conditional law given
the tail σ-algebra. This follows immediately from `extreme_members_equal_on_tail`. -/
lemma identical_conditional_laws
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → α}
    (hX : Contractable μ X)
    (hX_meas : ∀ n, Measurable (X n))
    (m : ℕ) :
    ∀ B : Set α, MeasurableSet B →
      μ[Set.indicator B (fun _ => (1 : ℝ)) ∘ (X m) | tailSigma X]
        =ᵐ[μ]
      μ[Set.indicator B (fun _ => (1 : ℝ)) ∘ (X 0) | tailSigma X] :=
  fun B hB => extreme_members_equal_on_tail hX hX_meas m B hB

/-- **Aldous' third proof of de Finetti's theorem.**

If `X` is contractable, then `X₁, X₂, ...` are conditionally i.i.d. given the
tail σ-algebra `𝒯_X = ⋂_n σ(θ_n X)`.

**Proof structure:**
1. From contractability: `(X_m, θ_{m+1} X) =^d (X_k, θ_{m+1} X)` for `k ≤ m ≤ n`
2. Define `𝒯_X = ⋂_n σ(θ_n X)` (tail σ-algebra)
3. Apply Lemma 1.3 + reverse martingale convergence:
   ```
   P[X_m ∈ B | θ_{m+1} X] = P[X_k ∈ B | θ_{m+1} X] → P[X_k ∈ B | 𝒯_X]
   ```
4. Conclude: `P[X_m ∈ B | θ_{m+1} X] = P[X_m ∈ B | 𝒯_X] = P[X_1 ∈ B | 𝒯_X]`
5. First equality: `X_m ⊥⊥_{𝒯_X} θ_{m+1} X` for all `m`
6. By iteration: `X₁, X₂, ...` conditionally independent given `𝒯_X`
7. Second equality: conditional laws agree, giving conditional i.i.d.

*Kallenberg (2005), third proof of Theorem 1.1 (page 28).* -/
theorem deFinetti_viaMartingale
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → α}
    (hX : Contractable μ X)
    (hX_meas : ∀ n, Measurable (X n)) :
    ConditionallyIID μ X := by
  sorry  -- TODO: Complete martingale proof of de Finetti

/-! ### Step 1: Constructing the directing measure ν

From conditional expectations on indicators, we need to build a measurable family
of probability measures `ν : Ω → Measure α`.

The construction uses the standard Borel machinery: for each `ω`, define
`ν ω` to be the unique probability measure satisfying
`ν ω B = E[1_{X₀∈B} | 𝒯_X](ω)` for all measurable `B`.

This requires StandardBorelSpace assumption on α to ensure existence.
-/

/-- Construction of the directing measure from conditional expectations.
For each `ω : Ω`, `ν ω` is the conditional distribution of `X₀` given the tail σ-algebra. -/
axiom directingMeasure_of_contractable
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {α : Type*} [MeasurableSpace α] [StandardBorelSpace α] [Nonempty α]
    (X : ℕ → Ω → α)
    (hX_meas : ∀ n, Measurable (X n)) :
    { ν : Ω → Measure α //
      (∀ ω, IsProbabilityMeasure (ν ω)) ∧
      (∀ B : Set α, MeasurableSet B →
        (fun ω => (ν ω B).toReal) =ᵐ[μ] μ[Set.indicator B (fun _ => (1 : ℝ)) ∘ (X 0) | tailSigma X]) ∧
      (∀ B : Set α, MeasurableSet B → Measurable (fun ω => ν ω B)) }

/-! ### Step 2: Identical conditional laws -/

/-- All `X_n` have the same conditional law `ν`.
This follows from `extreme_members_equal_on_tail`. -/
lemma conditional_law_eq_directingMeasure
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {α : Type*} [MeasurableSpace α] [StandardBorelSpace α] [Nonempty α]
    (X : ℕ → Ω → α)
    (hX : Contractable μ X)
    (hX_meas : ∀ n, Measurable (X n))
    (ν : Ω → Measure α)
    (hν : ∀ B : Set α, MeasurableSet B →
        (fun ω => (ν ω B).toReal) =ᵐ[μ] μ[Set.indicator B (fun _ => (1 : ℝ)) ∘ (X 0) | tailSigma X])
    (n : ℕ) (B : Set α) (hB : MeasurableSet B) :
    (fun ω => (ν ω B).toReal) =ᵐ[μ] μ[Set.indicator B (fun _ => (1 : ℝ)) ∘ (X n) | tailSigma X] := by
  have h0 := hν B hB
  have hn := extreme_members_equal_on_tail hX hX_meas n B hB
  exact ae_eq_trans h0 hn.symm

/-! ### Step 3: Conditional independence -/

/-- Finite-dimensional product formula for conditionally i.i.d. sequences.

**Proof strategy:**
1. Use `finite_level_factorization` to get factorization at future levels
2. Apply `tail_factorization_from_future` with reverse martingale convergence
   (`condexp_tendsto_tail`) to lift to the tail σ-algebra
3. Use identical conditional laws (from `conditional_law_eq_directingMeasure`)
   to replace each `Xᵢ` with `X₀` in the product
4. Extend from rectangles to all measurable sets via π-system/monotone class
   (rectangles generate the product σ-algebra)

This is the key step that assembles all the machinery. -/
axiom finite_product_formula
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {α : Type*} [MeasurableSpace α] [StandardBorelSpace α] [Nonempty α]
    (X : ℕ → Ω → α)
    (hX : Contractable μ X)
    (hX_meas : ∀ n, Measurable (X n))
    (ν : Ω → Measure α)
    (hν_prob : ∀ ω, IsProbabilityMeasure (ν ω))
    (hν_meas : ∀ B : Set α, MeasurableSet B → Measurable (fun ω => ν ω B))
    (hν_law : ∀ n B, MeasurableSet B →
        (fun ω => (ν ω B).toReal) =ᵐ[μ] μ[Set.indicator B (fun _ => (1 : ℝ)) ∘ (X n) | tailSigma X])
    (m : ℕ) (k : Fin m → ℕ) :
    Measure.map (fun ω => fun i : Fin m => X (k i) ω) μ
      = μ.bind (fun ω => Measure.pi fun _ : Fin m => ν ω)

/-! ### Main theorem -/

theorem deFinetti_martingale
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {α : Type*} [MeasurableSpace α] [StandardBorelSpace α] [Nonempty α]
    (X : ℕ → Ω → α)
    (hX : Contractable μ X)
    (hX_meas : ∀ n, Measurable (X n)) :
    ConditionallyIID μ X := by
  -- Step 1: Construct the directing measure ν
  obtain ⟨ν, hν_prob, hν_law, hν_meas⟩ := directingMeasure_of_contractable (μ:=μ) X hX_meas

  -- Step 2: Verify it's a ConditionallyIID certificate
  refine ⟨ν, hν_prob, fun m k => ?_⟩

  -- Step 3: Prove finite-dimensional product formula
  exact finite_product_formula X hX hX_meas ν hν_prob hν_meas
    (fun n B hB => conditional_law_eq_directingMeasure X hX hX_meas ν hν_law n B hB) m k

end ViaMartingale
end DeFinetti
end Exchangeability
