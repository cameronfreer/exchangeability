/-
Copyright (c) 2025 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.Probability.ConditionalExpectation
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Probability.Martingale.Basic
import Exchangeability.Contractability
import Exchangeability.ConditionallyIID
import Exchangeability.Probability.CondExp
import Exchangeability.Probability.Martingale

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

-- Note: condExp_congr_ae is available from mathlib
-- (Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic)

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

/-- **Axiom ELIMINATED:** Conditional expectation convergence from contractability.

This axiom has been eliminated! See `condexp_convergence` at line ~1530 for the full proof
using the CE bridge lemma from CondExp.lean.

The forward declaration is no longer needed as nothing references it before the proof. -/

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
when the base measure is finite.

Note: While this could be stated for general sigma-finite measures, we only need the finite
case for de Finetti's theorem (which works with probability measures). The general sigma-finite
case requires manual construction of spanning sets and is a mathlib gap. -/
lemma sigmaFinite_trim_tailSigma {Ω α : Type*} {m₀ : MeasurableSpace Ω} [MeasurableSpace α]
    {μ : @Measure Ω m₀} [IsFiniteMeasure μ]
    (X : ℕ → Ω → α) (hX : ∀ n, Measurable (X n)) :
    SigmaFinite (μ.trim (tailSigma_le X hX)) := by
  classical
  -- Use the infrastructure from CondExp.lean
  exact Exchangeability.Probability.sigmaFinite_trim μ (tailSigma_le X hX)

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

/-! ### Note on removed lemma

**REMOVED:** `firstRSigma_le_futureFiltration` lemma removed as mathematically incorrect.

**Why incorrect:**
- `firstRSigma X r` is generated by X₀, ..., X_{r-1}
- `futureFiltration X m` is generated by X_{m+1}, X_{m+2}, ...
- When r ≤ m, these have non-overlapping index sets, so σ-algebra inclusion cannot hold

**Impact:**
- Was only referenced in commented-out proof sketch for `finite_level_factorization` (line 1674)
- That proof sketch needs redesign to use correct σ-algebra relationships
- No active code depends on this lemma

**Replacement:**
When the proof sketch is uncommented, the measurability argument needs to use the fact that
for r+1 ≤ m, the past coordinates X₀,...,X_r and the future filtration at m are independent,
not that one σ-algebra is contained in the other. -/

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
    (h : ∀ (r : ℕ) (B : Set α) (_hB : MeasurableSet B)
        (C : Fin r → Set α) (_hC : ∀ i, MeasurableSet (C i)),
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

/-! ### Conditional expectation convergence from contractability

This proves the forward-declared axiom from line 477. -/

/-- **Conditional expectation convergence (formerly Axiom 1):** For k ≤ m, all coordinates look
the same when conditioned on the future filtration at level m.

This is the key convergence result: for k ≤ m and measurable set B,
```
P[X_m ∈ B | θ_{m+1} X] = P[X_k ∈ B | θ_{m+1} X]
```

**Proof:** Uses the CE bridge lemma from CondExp.lean with the measure equality from
contractability. The key insight is that deleting coordinates doesn't change the joint distribution
with the future, which implies conditional expectation equality by the bridge lemma. -/
lemma condexp_convergence
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → α} (hX : Contractable μ X)
    (hX_meas : ∀ n, Measurable (X n))
    (k m : ℕ) (hk : k ≤ m)
    (B : Set α) (hB : MeasurableSet B) :
    μ[Set.indicator B (fun _ => (1 : ℝ)) ∘ (X m) | futureFiltration X m]
      =ᵐ[μ]
    μ[Set.indicator B (fun _ => (1 : ℝ)) ∘ (X k) | futureFiltration X m] := by
  -- Use the CE bridge lemma with Y = X m, Y' = X k, Z = shiftRV X (m+1)
  -- The key is that futureFiltration X m = σ(shiftRV X (m+1)) by definition

  -- First, get the measure equality from contractability
  have hmeas_eq : Measure.map (fun ω => (X m ω, shiftRV X (m + 1) ω)) μ
                = Measure.map (fun ω => (X k ω, shiftRV X (m + 1) ω)) μ := by
    -- Use measure_ext_of_future_rectangles to convert rectangle agreement to full equality
    apply measure_ext_of_future_rectangles
    -- Get rectangle agreement from contractability
    exact agree_on_future_rectangles_of_contractable hX hX_meas k m hk

  -- Apply the CE bridge lemma
  have h := Exchangeability.Probability.condexp_indicator_eq_of_pair_law_eq
    (X m) (X k) (shiftRV X (m + 1))
    (hX_meas m) (hX_meas k) (measurable_shiftRV hX_meas)
    hmeas_eq hB

  -- Simplify: futureFiltration X m = MeasurableSpace.comap (shiftRV X (m + 1)) inferInstance
  simpa [futureFiltration] using h


section reverse_martingale

variable {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {X : ℕ → Ω → α}

/-- 𝔽ₘ := σ(θ_{m+1} X) (the future filtration). -/
abbrev 𝔽 (m : ℕ) : MeasurableSpace Ω := futureFiltration X m

/-- The reverse filtration is decreasing; packaged for the martingale API. -/
lemma filtration_antitone (X : ℕ → Ω → α) : Antitone (fun m => futureFiltration X m) :=
  futureFiltration_antitone X

/-- Mₘ := 𝔼[1_{Xₖ∈B} | 𝔽ₘ].
The reverse martingale sequence for the indicator of X_k in B.

Uses `condExpWith` from CondExp.lean to manage typeclass instances properly. -/
noncomputable
def M (hX_meas : ∀ n, Measurable (X n)) (k : ℕ) (B : Set α) (_hB : MeasurableSet B) :
    ℕ → Ω → ℝ :=
  fun m => Exchangeability.Probability.condExpWith μ (futureFiltration X m)
    (futureFiltration_le X m hX_meas)
    (B.indicator (fun _ => (1 : ℝ)) ∘ X k)

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

/-! ### Kallenberg Lemma 1.3 - Contraction implies conditional independence

**Strategy: Finite approximation (Option A) - IN PROGRESS**

We prove conditional independence by working with finite future approximations.
The full proof requires martingale convergence theory for the limit step. -/

/-- **Finite future σ-algebra.**

Approximates the infinite future σ(X_{m+1}, X_{m+2}, ...) by finite truncation. -/
def finFutureSigma (X : ℕ → Ω → α) (m k : ℕ) : MeasurableSpace Ω :=
  MeasurableSpace.comap (fun ω => fun i : Fin k => X (m + 1 + i.val) ω) inferInstance

lemma finFutureSigma_le_ambient
    (X : ℕ → Ω → α) (m k : ℕ) (hX : ∀ n, Measurable (X n)) :
    finFutureSigma X m k ≤ (inferInstance : MeasurableSpace Ω) := by
  intro s hs
  obtain ⟨t, ht, rfl⟩ := hs
  exact (measurable_pi_lambda _ (fun i => hX (m + 1 + i.val))) ht

lemma finFutureSigma_le_futureFiltration
    (X : ℕ → Ω → α) (m k : ℕ) :
    finFutureSigma X m k ≤ futureFiltration X m := by
  intro s hs
  obtain ⟨t, ht, rfl⟩ := hs
  -- s = (fun ω => fun i : Fin k => X (m + 1 + i.val) ω) ⁻¹' t
  -- Need to show this is in futureFiltration X m

  -- The finite projection factors through the infinite one:
  -- (fun ω => fun i => X (m + 1 + i.val) ω) = proj ∘ (shiftRV X (m+1))
  -- where proj : (ℕ → α) → (Fin k → α) takes first k coordinates

  let proj : (ℕ → α) → (Fin k → α) := fun f i => f i.val

  have h_factor : (fun ω => fun i : Fin k => X (m + 1 + i.val) ω) = proj ∘ (shiftRV X (m + 1)) := by
    ext ω i
    simp only [Function.comp_apply, proj, shiftRV]

  -- Since proj is measurable, proj ⁻¹' t is measurable in (ℕ → α)
  have h_proj_meas : Measurable proj := measurable_pi_lambda _ (fun i => measurable_pi_apply i.val)
  have h_proj_t_meas : MeasurableSet (proj ⁻¹' t) := h_proj_meas ht

  -- Provide witness for comap: s ∈ futureFiltration means ∃ t', s = (shiftRV X (m+1)) ⁻¹' t'
  refine ⟨proj ⁻¹' t, h_proj_t_meas, ?_⟩

  -- Show s = (shiftRV X (m+1)) ⁻¹' (proj ⁻¹' t)
  rw [← Set.preimage_comp, ← h_factor]

/-! **Helper lemma: Distributional property from contractability (finite version).**

This lemma extracts the key property needed for conditional independence from contractability.
For finite future approximations, it shows that the measure of cylinder sets factorizes
appropriately. -/

/-- **Cylinder set measure formula from contractability (finite approximation).**

For contractable sequences with r < m, the measure of joint cylinder events involving
the first r coordinates, coordinate r, and k future coordinates can be expressed using
contractability properties.

This provides the distributional foundation for proving conditional independence in the
finite approximation setting. -/
lemma contractable_finite_cylinder_measure
    {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ℕ → Ω → α)
    (hX : Contractable μ X)
    (hX_meas : ∀ n, Measurable (X n))
    {r m k : ℕ} (hrm : r < m)
    (A : Fin r → Set α) (hA : ∀ i, MeasurableSet (A i))
    (B : Set α) (hB : MeasurableSet B)
    (C : Fin k → Set α) (hC : ∀ i, MeasurableSet (C i)) :
    -- The joint measure equals the measure for the standard cylinder
    μ ({ω | (∀ i, X i.val ω ∈ A i) ∧ X r ω ∈ B ∧ (∀ j, X (m + 1 + j.val) ω ∈ C j)})
      = μ ({ω | (∀ i : Fin r, X i.val ω ∈ A i) ∧ X r ω ∈ B ∧ (∀ j : Fin k, X (r + 1 + j.val) ω ∈ C j)}) := by
  -- Strategy: The indices (0,...,r-1, r, m+1,...,m+k) form a strictly increasing sequence.
  -- By contractability, this has the same distribution as (0,...,r-1, r, r+1,...,r+k).

  -- Define the index function: Fin (r + 1 + k) → ℕ
  -- Maps i to: i if i ≤ r, and m + i - r if i > r
  let idx : Fin (r + 1 + k) → ℕ := fun i =>
    if h : i.val < r + 1 then i.val else m + 1 + (i.val - r - 1)

  -- Show idx is strictly monotone
  have idx_mono : StrictMono idx := by
    intro i j hij
    simp only [idx]
    split_ifs with hi hj hj
    · -- Both i, j ≤ r: use i < j directly
      exact hij
    · -- i ≤ r < j: show i < m + 1 + (j - r - 1)
      have : j.val ≥ r + 1 := Nat.le_of_not_lt hj
      calc i.val
        _ < r + 1 := hi
        _ ≤ m + 1 := Nat.add_le_add_right (Nat.le_of_lt hrm) 1
        _ ≤ m + 1 + (j.val - r - 1) := Nat.le_add_right _ _
    · -- i ≤ r but not j < r + 1: contradiction
      omega
    · -- Both i, j > r: use the fact that j.val - r - 1 > i.val - r - 1
      have hi' : i.val ≥ r + 1 := Nat.le_of_not_lt hi
      have hj' : j.val ≥ r + 1 := Nat.le_of_not_lt hj
      calc m + 1 + (i.val - r - 1)
        _ < m + 1 + (j.val - r - 1) := Nat.add_lt_add_left (Nat.sub_lt_sub_right hi' hij) _

  -- Apply contractability: subsequence via idx has same distribution as 0,...,r+k
  have contract := hX (r + 1 + k) idx idx_mono

  -- Define the product set corresponding to our cylinder conditions
  let S_idx : Set (Fin (r + 1 + k) → α) :=
    {f | (∀ i : Fin r, f ⟨i.val, by omega⟩ ∈ A i) ∧ f ⟨r, by omega⟩ ∈ B ∧
         (∀ j : Fin k, f ⟨r + 1 + j.val, by omega⟩ ∈ C j)}

  let S_std : Set (Fin (r + 1 + k) → α) :=
    {f | (∀ i : Fin r, f ⟨i.val, by omega⟩ ∈ A i) ∧ f ⟨r, by omega⟩ ∈ B ∧
         (∀ j : Fin k, f ⟨r + 1 + j.val, by omega⟩ ∈ C j)}

  -- Note: S_idx = S_std, so they define the same set
  have h_sets_eq : S_idx = S_std := rfl

  -- Key: Show that the LHS and RHS sets are preimages under the respective mappings

  -- The LHS: {ω | X_0,...,X_{r-1} ∈ A, X_r ∈ B, X_{m+1},...,X_{m+k} ∈ C}
  -- is exactly the preimage of S_idx under (fun ω i => X (idx i) ω)
  have lhs_eq : {ω | (∀ i, X i.val ω ∈ A i) ∧ X r ω ∈ B ∧ (∀ j, X (m + 1 + j.val) ω ∈ C j)}
      = (fun ω => fun i => X (idx i) ω) ⁻¹' S_idx := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_preimage, S_idx]
    constructor
    · intro ⟨hA, hB, hC⟩
      refine ⟨?_, ?_, ?_⟩
      · intro i
        -- For i < r: idx(i) = i, so X(idx i) ω = X i ω ∈ A i
        have hi : idx ⟨i.val, by omega⟩ = i.val := by
          simp only [idx]; split_ifs <;> omega
        rw [hi]
        exact hA i
      · -- For i = r: idx(r) = r, so X(idx r) ω = X r ω ∈ B
        have : idx ⟨r, by omega⟩ = r := by
          simp only [idx]; split_ifs <;> omega
        rw [this]
        exact hB
      · intro j
        -- For i = r+1+j: idx(r+1+j) = m+1+j
        have : idx ⟨r + 1 + j.val, by omega⟩ = m + 1 + j.val := by
          simp only [idx]
          split_ifs with h
          · omega
          · have : r + 1 + j.val - r - 1 = j.val := by omega
            rw [this]
        rw [this]
        exact hC j
    · intro ⟨hA, hB, hC⟩
      refine ⟨?_, ?_, ?_⟩
      · intro i
        have : idx ⟨i.val, by omega⟩ = i.val := by
          simp only [idx]; split_ifs <;> omega
        rw [← this]
        exact hA ⟨i.val, by omega⟩
      · have : idx ⟨r, by omega⟩ = r := by
          simp only [idx]; split_ifs <;> omega
        rw [← this]
        exact hB
      · intro j
        have idx_val : idx ⟨r + 1 + j.val, by omega⟩ = m + 1 + j.val := by
          simp only [idx]
          split_ifs with h
          · omega
          · have : r + 1 + j.val - r - 1 = j.val := by omega
            rw [this]
        rw [← idx_val]
        exact hC j

  -- The RHS is the preimage of S_std under (fun ω i => X i.val ω)
  have rhs_eq : {ω | (∀ i, X i.val ω ∈ A i) ∧ X r ω ∈ B ∧ (∀ j, X (r + 1 + j.val) ω ∈ C j)}
      = (fun ω => fun i => X i.val ω) ⁻¹' S_std := by
    ext ω; simp [S_std]

  -- Apply contractability: the pushforward measures are equal
  rw [lhs_eq, rhs_eq, h_sets_eq]

  -- contract says the two pushforward measures are equal:
  -- Measure.map (fun ω i => X (idx i) ω) μ = Measure.map (fun ω i => X i.val ω) μ
  --
  -- Goal is: μ ((fun ω i => X (idx i) ω) ⁻¹' S_std) = μ ((fun ω i => X i.val ω) ⁻¹' S_std)
  --
  -- Since the measures are equal, they assign equal measure to preimages

  -- First prove S_std is measurable
  have hS_meas : MeasurableSet S_std := by
    -- Use intersection decomposition approach
    -- S_std = (⋂ i : Fin r, preimage at i) ∩ (preimage at r) ∩ (⋂ j : Fin k, preimage at r+1+j)
    have h_decomp : S_std =
        (⋂ i : Fin r, {f | f ⟨i.val, by omega⟩ ∈ A i}) ∩
        {f | f ⟨r, by omega⟩ ∈ B} ∩
        (⋂ j : Fin k, {f | f ⟨r + 1 + j.val, by omega⟩ ∈ C j}) := by
      ext f
      simp only [S_std, Set.mem_iInter, Set.mem_inter_iff, Set.mem_setOf]
      tauto

    rw [h_decomp]
    apply MeasurableSet.inter
    · apply MeasurableSet.inter
      · apply MeasurableSet.iInter
        intro i
        exact measurable_pi_apply (Fin.mk i.val (by omega)) (hA i)
      · exact measurable_pi_apply (Fin.mk r (by omega)) hB
    · apply MeasurableSet.iInter
      intro j
      exact measurable_pi_apply (Fin.mk (r + 1 + j.val) (by omega)) (hC j)

  -- Prove the functions are measurable
  have h_meas_idx : Measurable (fun ω (i : Fin (r + 1 + k)) => X (idx i) ω) :=
    measurable_pi_lambda _ (fun i => hX_meas (idx i))
  have h_meas_std : Measurable (fun ω (i : Fin (r + 1 + k)) => X (↑i) ω) :=
    measurable_pi_lambda _ (fun i => hX_meas (↑i))

  calc μ ((fun ω (i : Fin (r + 1 + k)) => X (idx i) ω) ⁻¹' S_std)
      = Measure.map (fun ω i => X (idx i) ω) μ S_std := by
        rw [Measure.map_apply h_meas_idx hS_meas]
    _ = Measure.map (fun ω (i : Fin (r + 1 + k)) => X (↑i) ω) μ S_std := by
        rw [contract]
    _ = μ ((fun ω (i : Fin (r + 1 + k)) => X (↑i) ω) ⁻¹' S_std) := by
        rw [Measure.map_apply h_meas_std hS_meas]

/-- Contractability implies equality of the joint law of
`(X₀,…,X_{r-1}, X_r, X_{m+1}, …, X_{m+k})` and
`(X₀,…,X_{r-1}, X_r, X_{r+1}, …, X_{r+k})`. -/
lemma contractable_triple_pushforward
    {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ℕ → Ω → α)
    (hX : Contractable μ X)
    (hX_meas : ∀ n, Measurable (X n))
    {r m k : ℕ} (hrm : r < m) :
  let Z_r : Ω → (Fin r → α) := fun ω i => X i.val ω
  let Y_future : Ω → (Fin k → α) := fun ω j => X (m + 1 + j.val) ω
  let Y_tail   : Ω → (Fin k → α) := fun ω j => X (r + 1 + j.val) ω
  Measure.map (fun ω => (Z_r ω, X r ω, Y_future ω)) μ
    = Measure.map (fun ω => (Z_r ω, X r ω, Y_tail ω)) μ := by
  classical
  intro Z_r Y_future Y_tail
  -- Define cylinder rectangles generating the product σ-algebra.
  let Rectangles :
      Set (Set ((Fin r → α) × α × (Fin k → α))) :=
    {S | ∃ (A : Fin r → Set α) (hA : ∀ i, MeasurableSet (A i))
          (B : Set α) (hB : MeasurableSet B)
          (C : Fin k → Set α) (hC : ∀ j, MeasurableSet (C j)),
        S = (Set.univ.pi A) ×ˢ B ×ˢ (Set.univ.pi C)}

  -- Rectangles form a π-system.
  have h_pi : IsPiSystem Rectangles := by
    intro S₁ hS₁ S₂ hS₂ h_ne
    rcases hS₁ with ⟨A₁, hA₁, B₁, hB₁, C₁, hC₁, rfl⟩
    rcases hS₂ with ⟨A₂, hA₂, B₂, hB₂, C₂, hC₂, rfl⟩
    refine ⟨fun i => A₁ i ∩ A₂ i, ?_, B₁ ∩ B₂, hB₁.inter hB₂,
            fun j => C₁ j ∩ C₂ j, ?_, ?_⟩
    · intro i; exact (hA₁ i).inter (hA₂ i)
    · intro j; exact (hC₁ j).inter (hC₂ j)
    · ext f; simp [Set.mem_univ_pi, Set.mem_inter_iff, Set.preimage, Set.mem_setOf_eq]

  -- Equality on rectangles using the finite cylinder measure lemma.
  have h_agree :
      ∀ {S} (hS : S ∈ Rectangles),
        Measure.map (fun ω => (Z_r ω, X r ω, Y_future ω)) μ S
          = Measure.map (fun ω => (Z_r ω, X r ω, Y_tail ω)) μ S := by
    intro S hS
    rcases hS with ⟨A, hA, B, hB, C, hC, rfl⟩
    -- Convert preimage of rectangle into the cylinder event.
    have h_pre_future :
        (fun ω => (Z_r ω, X r ω, Y_future ω)) ⁻¹'
          ((Set.univ.pi A) ×ˢ B ×ˢ (Set.univ.pi C))
          =
        {ω | (∀ i : Fin r, X i.val ω ∈ A i) ∧ X r ω ∈ B ∧
              (∀ j : Fin k, X (m + 1 + j.val) ω ∈ C j)} := by
      ext ω; simp [Z_r, Y_future, Set.mem_univ_pi, Set.mem_setOf_eq]
    have h_pre_tail :
        (fun ω => (Z_r ω, X r ω, Y_tail ω)) ⁻¹'
          ((Set.univ.pi A) ×ˢ B ×ˢ (Set.univ.pi C))
          =
        {ω | (∀ i : Fin r, X i.val ω ∈ A i) ∧ X r ω ∈ B ∧
              (∀ j : Fin k, X (r + 1 + j.val) ω ∈ C j)} := by
      ext ω; simp [Z_r, Y_tail, Set.mem_univ_pi, Set.mem_setOf_eq]
    -- Apply the finite cylinder equality.
    have :=
      contractable_finite_cylinder_measure
        (X := X) (μ := μ) (hX := hX) (hX_meas := hX_meas)
        (hrm := hrm) (A := A) (hA := hA) (B := B) (hB := hB)
        (C := C) (hC := hC)
    simpa [Measure.map_apply,
      h_pre_future, h_pre_tail,
      Set.mem_univ_pi, Set.mem_setOf_eq,
      measurable_pi_lambda, hA, hB, hC]
      using this

  -- Covering family: constant sequence of `Set.univ`.
  let Bseq : ℕ → Set ((Fin r → α) × α × (Fin k → α)) := fun _ => Set.univ
  have hBseq_union : ⋃ n, Bseq n = Set.univ := by simp [Bseq]
  have hBseq_mem : ∀ n, Bseq n ∈ Rectangles := by
    intro n
    refine ⟨fun _ => Set.univ, fun _ => MeasurableSet.univ,
      Set.univ, MeasurableSet.univ, fun _ => Set.univ, fun _ => MeasurableSet.univ, ?_⟩
    simp [Bseq]
  have hBseq_finite : ∀ n,
      (Measure.map (fun ω => (Z_r ω, X r ω, Y_future ω)) μ) (Bseq n) ≠ ∞ := by
    intro n
    simpa [Bseq] using
      (measure_ne_top _
        (Set.univ : Set ((Fin r → α) × α × (Fin k → α))))
  have hBseq_finite' : ∀ n,
      (Measure.map (fun ω => (Z_r ω, X r ω, Y_tail ω)) μ) (Bseq n) ≠ ∞ := by
    intro n
    simpa [Bseq] using
      (measure_ne_top _
        (Set.univ : Set ((Fin r → α) × α × (Fin k → α))))

  -- Apply the measure extension lemma on the π-system.
  refine Measure.ext_of_generateFrom_of_iUnion
    Rectangles Bseq ?_ h_pi hBseq_union hBseq_mem hBseq_finite h_agree
    ?_ hBseq_finite' ?_ ?_
  · -- Rectangles generate the product σ-algebra.
    ext s; constructor
    · intro hs
      rcases hs with ⟨A, hA, B, hB, C, hC, rfl⟩
      refine MeasurableSet.prod ?_ ?_
      · exact MeasurableSet.prod (MeasurableSet.univ_pi hA) hB
      · exact MeasurableSet.univ_pi hC
    · intro hs
      -- Any measurable set in the product σ-algebra is in the generated σ-algebra.
      refine MeasurableSet.generateFrom ?_
      intro s hs
      rcases hs with ⟨A, hA, B, hB, C, hC, rfl⟩
      apply MeasurableSet.prod
      · exact MeasurableSet.prod (MeasurableSet.univ_pi hA) hB
      · exact MeasurableSet.univ_pi hC
  · -- The identity on Rectangles is measurable.
    intro s hs
    rcases hs with ⟨A, hA, B, hB, C, hC, rfl⟩
    refine (MeasurableSet.prod ?_ ?_)
    · exact MeasurableSet.prod (MeasurableSet.univ_pi hA) hB
    · exact MeasurableSet.univ_pi hC
  · -- The measures agree on Rectangles (already shown).
    intro s hs
    exact h_agree hs
/-- **Correct conditional independence from contractability (Kallenberg Lemma 1.3).**

For contractable X and r < m, the past block σ(X₀,...,X_{r-1}) and the single coordinate
σ(X_r) are conditionally independent given the far future σ(θ_{m+1} X).

**Mathematical statement:**
```
σ(X₀,...,X_{r-1}) ⊥⊥_{σ(θ_{m+1} X)} σ(X_r)
```

**Why this is correct:**
By contractability, deleting coordinate r doesn't change the joint distribution:
```
(X₀,...,X_{r-1}, θ_{m+1} X) =ᵈ (X₀,...,X_{r-1}, X_r, θ_{m+1} X)
```
with σ(θ_{m+1} X) ⊆ σ(X_r, θ_{m+1} X).

By Kallenberg's Lemma 1.3: if (U, η) =ᵈ (U, ζ) and σ(η) ⊆ σ(ζ), then U ⊥⊥_η ζ.
Taking U = (X₀,...,X_{r-1}), η = θ_{m+1} X, ζ = (X_r, θ_{m+1} X) gives the result.

**This replaces the old broken `coordinate_future_condIndep` which incorrectly claimed
Y ⊥⊥_{σ(Y)} Y.** -/
lemma block_coord_condIndep
    {Ω α : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [MeasurableSpace α]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ℕ → Ω → α)
    (hX : Contractable μ X)
    (hX_meas : ∀ n, Measurable (X n))
    {r m : ℕ} (hrm : r < m) :
  ProbabilityTheory.CondIndep
    (futureFiltration X m)                        -- conditioning: σ(θ_{m+1} X)
    (firstRSigma X r)                             -- past block: σ(X₀,...,X_{r-1})
    (MeasurableSpace.comap (X r) inferInstance)   -- single coord: σ(X_r)
    (futureFiltration_le X m hX_meas)             -- witness: σ(θ_{m+1} X) ≤ ambient
    μ := by
  -- Strategy: Use condIndep_of_indicator_condexp_eq to show projection property
  -- For any H ∈ σ(X_r), we need to show:
  --   μ[H.indicator | firstRSigma X r ⊔ futureFiltration X m] =ᵐ μ[H.indicator | futureFiltration X m]
  -- This follows from contractability: when r < m, coordinate X_r is conditionally
  -- independent of (X₀,...,X_{r-1}) given the future θ_{m+1} X.

  apply Exchangeability.Probability.condIndep_of_indicator_condexp_eq
  · -- hmF: firstRSigma X r ≤ ambient
    exact firstRSigma_le_ambient X r hX_meas
  · -- hmH: σ(X_r) ≤ ambient (hmG already provided in goal)
    intro s hs
    obtain ⟨t, ht, rfl⟩ := hs
    exact (hX_meas r) ht
  -- Show projection property: for all H ∈ σ(X_r),
  -- μ[H.indicator | firstRSigma X r ⊔ futureFiltration X m] =ᵐ μ[H.indicator | futureFiltration X m]
  intro H hH
  -- H is measurable in σ(X_r), so H = (X r)⁻¹(B) for some measurable B
  obtain ⟨B, hB, rfl⟩ := hH
  -- The indicator function is (indicator B ∘ X r)

  -- Prove projection property: μ[1_B ∘ X_r | firstR ⊔ future] =ᵐ μ[1_B ∘ X_r | future]
  --
  -- **Strategy:** Work with finite approximations first, then pass to limit.
  -- For each k, show the property holds for finFutureSigma X m k, then let k → ∞.

  -- Step 1: Finite approximation - show CI given k future coordinates
  have finite_approx : ∀ (k : ℕ),
      -- For finite future, the projection property holds
      ∀ (E : Set Ω), MeasurableSet[firstRSigma X r ⊔ finFutureSigma X m k] E →
        ∫ ω in E, Set.indicator B (fun _ => (1 : ℝ)) (X r ω) ∂μ
          = ∫ ω in E, (Exchangeability.Probability.condExpWith μ
              (finFutureSigma X m k) (finFutureSigma_le_ambient X m k hX_meas)
              (Set.indicator B (fun _ => (1 : ℝ)) ∘ X r)) ω ∂μ := by
    intro k E hE

    -- **Strategy:** Prove integral equality for all E measurable in firstRSigma ⊔ finFutureSigma
    -- Goal: ∫_E indicator B (X r ω) dμ = ∫_E μ[indicator B ∘ X r | finFuture_k] ω dμ

    -- **Step 1a: Define π-system of cylinder generators**
    -- A cylinder generator is a set of form:
    --   {ω | ∀i<r, X_i ω ∈ A_i} ∩ {ω | ∀j<k, X_{m+1+j} ω ∈ C_j}
    -- These generate firstRSigma ⊔ finFutureSigma and form a π-system (closed under ∩)

    -- **Step 1b: Prove integral equality for cylinder generators**
    -- For E = {∀i X_i ∈ A_i} ∩ {∀j X_{m+1+j} ∈ C_j}:
    --   LHS = ∫_E indicator B (X r) dμ
    --       = μ(E ∩ {X_r ∈ B})
    --       = μ({∀i X_i ∈ A_i, X_r ∈ B, ∀j X_{m+1+j} ∈ C_j})
    --
    -- By contractable_finite_cylinder_measure:
    --   = μ({∀i X_i ∈ A_i, X_r ∈ B, ∀j X_{r+1+j} ∈ C_j})  [reindexing via contractability]
    --
    -- The RHS involves μ[indicator B ∘ X r | finFuture_k] which by definition
    -- satisfies the conditional expectation property. The key is that the factorization
    -- from contractability implies the projection property.

    -- **Step 1c: Extend to all measurable sets via monotone class theorem**
    -- The collection of sets E for which the integral equality holds forms a
    -- monotone class (closed under monotone limits). By monotone class theorem,
    -- since it contains the π-system of cylinders and is a monotone class,
    -- it contains the generated σ-algebra.

    -- **Proof strategy (Dynkin's π-λ theorem):**
    --
    -- Define GoodSets = {E measurable | ∫_E indicator B (X r) dμ = ∫_E μ[indicator B ∘ X r | finFuture_k] dμ}
    --
    -- **Part A (60-90 min): Show cylinder π-system ⊆ GoodSets**
    -- For E_cyl = {ω | ∀i X_i ∈ A_i} ∩ {ω | ∀j X_{m+1+j} ∈ C_j}:
    --   LHS = ∫_{E_cyl} indicator B (X r) dμ
    --       = μ(E_cyl ∩ {X_r ∈ B})
    --       = μ({∀i X_i ∈ A_i, X_r ∈ B, ∀j X_{m+1+j} ∈ C_j})
    --
    -- Apply contractable_finite_cylinder_measure (hrm : r < m):
    --       = μ({∀i X_i ∈ A_i, X_r ∈ B, ∀j X_{r+1+j} ∈ C_j})  [reindexing]
    --
    --   RHS = ∫_{E_cyl} μ[indicator B ∘ X r | finFuture_k] dμ
    --
    -- Show LHS = RHS using conditional expectation characterization
    --
    -- **Part B (30 min): Show GoodSets is a monotone class**
    -- Monotone limits: If E_n ∈ GoodSets and E_n ↗, then ⋃ E_n ∈ GoodSets
    --   Use monotone convergence theorem for integrals
    -- Decreasing limits: If E_n ∈ GoodSets and E_n ↘, then ⋂ E_n ∈ GoodSets
    --   Use dominated convergence theorem for integrals
    --
    -- **Part C (30 min): Apply Dynkin's π-λ theorem**
    -- The cylinder π-system generates σ(firstRSigma ⊔ finFutureSigma)
    -- GoodSets contains π-system and is a monotone class
    -- By Dynkin: GoodSets contains the generated σ-algebra
    -- Therefore E ∈ GoodSets for all measurable E

    -- Given: E measurable in firstRSigma X r ⊔ finFutureSigma X m k
    -- Goal: ∫_E indicator B (X r) dμ = ∫_E μ[indicator B ∘ X r | finFuture_k] dμ

    -- Use Dynkin's π-λ theorem: prove for all measurable E via monotone class argument

    -- Define GoodSets = collection of sets E for which the integral equality holds
    let GoodSets : Set (Set Ω) := {E |
      MeasurableSet[firstRSigma X r ⊔ finFutureSigma X m k] E ∧
      ∫ ω in E, Set.indicator B (fun _ => (1 : ℝ)) (X r ω) ∂μ =
      ∫ ω in E, (Exchangeability.Probability.condExpWith μ
          (finFutureSigma X m k) (finFutureSigma_le_ambient X m k hX_meas)
          (Set.indicator B (fun _ => (1 : ℝ)) ∘ X r)) ω ∂μ}

    -- We need to show E ∈ GoodSets

    -- Strategy: Show GoodSets is a monotone class containing the cylinder π-system
    -- Then by Dynkin's π-λ theorem, GoodSets contains all measurable sets

    -- **Part A (60-90 min): Cylinder π-system ⊆ GoodSets**
    --
    -- Goal: For any cylinder E_cyl = {∀i X_i ∈ A_i} ∩ {∀j X_{m+1+j} ∈ C_j},
    --       show E_cyl ∈ GoodSets
    --
    -- Proof outline:
    --
    -- 1. Define representative cylinder:
    --    E_cyl = {ω | ∀i<r, X_i ω ∈ A_i} ∩ {ω | ∀j<k, X_{m+1+j} ω ∈ C_j}
    --
    -- 2. Show E_cyl is measurable in firstRSigma ⊔ finFutureSigma ✓
    --    (product of measurable sets)
    --
    -- 3. LHS computation:
    --    ∫_{E_cyl} indicator B (X r) dμ
    --      = μ(E_cyl ∩ {X_r ∈ B})
    --      = μ({∀i X_i ∈ A_i, X_r ∈ B, ∀j X_{m+1+j} ∈ C_j})
    --
    -- 4. Apply contractable_finite_cylinder_measure (key step):
    --    μ({∀i X_i ∈ A_i, X_r ∈ B, ∀j X_{m+1+j} ∈ C_j})
    --      = μ({∀i X_i ∈ A_i, X_r ∈ B, ∀j X_{r+1+j} ∈ C_j})  ... (*)
    --
    -- 5. RHS computation - need to show:
    --    ∫_{E_cyl} μ[indicator B ∘ X r | finFuture_k] dμ = (*) above
    --
    --    Challenge: Relate the CE integral to the reindexed measure.
    --
    --    Possible approaches:
    --    a) Use setIntegral_condExp to convert RHS to ∫_{E_cyl} indicator B (X r) dμ
    --       on a different cylinder (requires showing E_cyl is in finFutureSigma - FALSE)
    --
    --    b) Use Fubini/product measure structure to factor the integ ral
    --       ∫_{E_first} (∫_{E_future} ...)
    --
    --    c) Use ae_eq_condExp_of_forall_setIntegral_eq (uniqueness of CE)
    --       to show indicator B (X r) has the right integral property
    --
    --    d) Use condexp_indicator_eq_of_pair_law_eq (CE bridge lemma from CondExp.lean)
    --       with the distributional equality from contractability
    --
    -- Missing infrastructure: Need lemma connecting cylinder measure equality
    -- to conditional expectation integral equality. This is non-trivial and may
    -- require developing product measure / Fubini machinery for this setting.
    --
    -- **Part B (30 min): GoodSets is a monotone class**
    --
    -- For increasing sequence: E_n ↗ E with E_n ∈ GoodSets
    --   Need: E ∈ GoodSets
    --   Strategy: Use monotone convergence theorem (MCT) for both integrals:
    --     ∫_E indicator = lim ∫_{E_n} indicator  (MCT)
    --     ∫_E μ[...] = lim ∫_{E_n} μ[...]        (MCT)
    --   Since ∫_{E_n} indicator = ∫_{E_n} μ[...] for all n, limits are equal.
    --
    -- For decreasing sequence: E_n ↘ E with E_n ∈ GoodSets
    --   Strategy: Use dominated convergence theorem (DCT) with dominating function = 1
    --   (similar argument)
    --
    -- **Part C (30 min): Apply Dynkin's π-λ theorem**
    --
    -- 1. Show cylinder sets form a π-system (closed under finite intersections)
    -- 2. Show GoodSets is a λ-system (Dynkin system):
    --    - Contains Ω ✓
    --    - Closed under complements (use integral property)
    --    - Closed under disjoint increasing unions (Part B)
    -- 3. Apply mathlib's Dynkin π-λ theorem from MeasureTheory.PiSystem
    --    Since cylinders form a π-system generating firstRSigma ⊔ finFutureSigma,
    --    and GoodSets is a λ-system containing the cylinders,
    --    GoodSets contains all measurable sets.
    --
    -- Key issue: Part A requires infrastructure that may not exist yet.
    -- The mathematical idea is clear but the formalization is non-trivial.

    -- Attempt to implement Part A with explicit infrastructure gaps marked

    -- For any given k, we need to show E ∈ GoodSets
    -- Start with cylinder sets and extend via Dynkin

    -- **Cylinder case: mostfundamental case**
    -- For E_cyl = {∀i<r, X_i ∈ A_i} ∩ {∀j<k, X_{m+1+j} ∈ C_j}, show:
    -- ∫_{E_cyl} indicator B (X r) dμ = ∫_{E_cyl} μ[indicator B ∘ X r | finFuture_k] dμ

    -- Step 1: LHS computation
    have lhs_computation : ∀ (A : Fin r → Set α) (hA : ∀ i, MeasurableSet (A i))
        (C : Fin k → Set α) (hC : ∀ i, MeasurableSet (C i)),
      let E_cyl := {ω | (∀ i, X i.val ω ∈ A i) ∧ (∀ j, X (m + 1 + j.val) ω ∈ C j)}
      ∫ ω in E_cyl, Set.indicator B (fun _ => (1 : ℝ)) (X r ω) ∂μ
        = (μ ({ω | (∀ i, X i.val ω ∈ A i) ∧ X r ω ∈ B ∧ (∀ j, X (m + 1 + j.val) ω ∈ C j)})).toReal := by
      intro A hA C hC
      -- Goal: ∫ ω in E_cyl, indicator B (X r ω) dμ = μ(E_target).toReal
      let E_target := {ω | (∀ i, X i.val ω ∈ A i) ∧ X r ω ∈ B ∧ (∀ j, X (m + 1 + j.val) ω ∈ C j)}

      -- The indicator function of B composed with X r is the indicator of X r⁻¹' B
      have h_indicator_eq : (fun ω => Set.indicator B (fun _ => (1:ℝ)) (X r ω))
          = Set.indicator (X r ⁻¹' B) (fun _ => (1:ℝ)) := by
        ext ω
        simp only [Set.indicator, Set.mem_preimage]
        by_cases h : X r ω ∈ B <;> simp [h]

      -- Rewrite the integral using this
      rw [h_indicator_eq]

      -- We now have: ∫ ω in E_cyl, Set.indicator (X r⁻¹' B) (fun _ => 1) ω ∂μ = (μ E_target).toReal
      have hXrB_meas : MeasurableSet (X r ⁻¹' B) := hX_meas r hB

      -- Use calc chain to build equality step by step
      show ∫ ω in {ω | (∀ i, X i.val ω ∈ A i) ∧ (∀ j, X (m + 1 + j.val) ω ∈ C j)},
            Set.indicator (X r ⁻¹' B) (fun _ => (1:ℝ)) ω ∂μ
        = (μ ({ω | (∀ i, X i.val ω ∈ A i) ∧ X r ω ∈ B ∧ (∀ j, X (m + 1 + j.val) ω ∈ C j)})).toReal

      let E_cyl' := {ω | (∀ i, X i.val ω ∈ A i) ∧ (∀ j, X (m + 1 + j.val) ω ∈ C j)}
      let E_target' := {ω | (∀ i, X i.val ω ∈ A i) ∧ X r ω ∈ B ∧ (∀ j, X (m + 1 + j.val) ω ∈ C j)}

      -- Measurability of the relevant sets
      have hE_past_meas :
          MeasurableSet {ω | ∀ i, X i.val ω ∈ A i} :=
        firstRCylinder_measurable_ambient X r A hX_meas hA
      have hE_future_meas :
          MeasurableSet {ω | ∀ j : Fin k, X (m + 1 + j.val) ω ∈ C j} := by
        classical
        have h_eq :
            {ω | ∀ j : Fin k, X (m + 1 + j.val) ω ∈ C j}
              = ⋂ j : Fin k, (fun ω => X (m + 1 + j.val) ω) ⁻¹' C j := by
          ext ω
          simp [Set.mem_setOf_eq, Set.mem_iInter]
        simpa [h_eq] using
          (MeasurableSet.iInter fun j : Fin k =>
            (hX_meas (m + 1 + j.val)) (hC j))
      have hE_cyl'_meas :
          MeasurableSet E_cyl' := by
        classical
        have h_eq :
            E_cyl' =
              ({ω | ∀ i, X i.val ω ∈ A i}
                ∩ {ω | ∀ j : Fin k, X (m + 1 + j.val) ω ∈ C j}) := by
          rfl
        simpa [h_eq] using hE_past_meas.inter hE_future_meas
      have h_inter_meas :
          MeasurableSet (E_cyl' ∩ (X r ⁻¹' B)) :=
        hE_cyl'_meas.inter hXrB_meas
      have h_integrable_const : Integrable (fun _ : Ω => (1 : ℝ)) μ :=
        integrable_const (1 : ℝ)

      have h_indicator_swap :
          Set.indicator E_cyl'
            (fun ω => Set.indicator (X r ⁻¹' B) (fun _ => (1 : ℝ)) ω)
          = Set.indicator (E_cyl' ∩ (X r ⁻¹' B)) (fun _ => (1 : ℝ)) := by
        classical
        ext ω
        by_cases hω₁ : ω ∈ E_cyl'
        · by_cases hω₂ : ω ∈ X r ⁻¹' B <;> simp [Set.indicator, hω₁, hω₂]
        · simp [Set.indicator, hω₁]

      have h_first :
          ∫ ω in E_cyl', Set.indicator (X r ⁻¹' B) (fun _ => (1 : ℝ)) ω ∂ μ
            = ∫ ω,
                Set.indicator (E_cyl' ∩ (X r ⁻¹' B))
                  (fun _ => (1 : ℝ)) ω ∂ μ := by
        classical
        have :
            ∫ ω in E_cyl', Set.indicator (X r ⁻¹' B) (fun _ => (1 : ℝ)) ω ∂ μ
              = ∫ ω,
                  Set.indicator E_cyl'
                    (fun ω => Set.indicator (X r ⁻¹' B) (fun _ => (1 : ℝ)) ω) ω ∂ μ := by
          simp [MeasureTheory.integral_indicator, hE_cyl'_meas, h_integrable_const]
        simpa [this, h_indicator_swap]

      have h_second :
          ∫ ω in E_cyl' ∩ (X r ⁻¹' B), (fun _ => (1 : ℝ)) ω ∂ μ
            = ∫ ω,
                Set.indicator (E_cyl' ∩ (X r ⁻¹' B))
                  (fun _ => (1 : ℝ)) ω ∂ μ := by
        classical
        simp [MeasureTheory.integral_indicator, h_inter_meas, h_integrable_const]

      have h_measure_eq :
          ∫ ω in E_cyl' ∩ (X r ⁻¹' B), (fun _ => (1 : ℝ)) ω ∂ μ
            = (μ (E_cyl' ∩ (X r ⁻¹' B))).toReal := by
        classical
        have :=
          MeasureTheory.integral_const
            (μ := μ.restrict (E_cyl' ∩ (X r ⁻¹' B))) (1 : ℝ)
        simpa [measure_restrict_univ] using this

      calc ∫ ω in E_cyl', Set.indicator (X r ⁻¹' B) (fun _ => (1:ℝ)) ω ∂μ
          = ∫ ω in E_cyl' ∩ (X r ⁻¹' B), (fun _ => (1:ℝ)) ω ∂μ := by
              exact setIntegral_indicator hXrB_meas
        _ = (μ (E_cyl' ∩ (X r ⁻¹' B))).toReal := by
              rw [setIntegral_const]
              simp [Measure.real]
        _ = (μ E_target').toReal := by
              have h_set_eq : E_cyl' ∩ (X r ⁻¹' B) = E_target' := by
                ext ω
                simp only [Set.mem_inter_iff, Set.mem_preimage, E_cyl', E_target', Set.mem_setOf_eq]
                tauto
              rw [h_set_eq]

    -- Step 2: Apply contractability
    have contractability_step : ∀ (A : Fin r → Set α) (hA : ∀ i, MeasurableSet (A i))
        (C : Fin k → Set α) (hC : ∀ i, MeasurableSet (C i)),
      μ ({ω | (∀ i, X i.val ω ∈ A i) ∧ X r ω ∈ B ∧ (∀ j, X (m + 1 + j.val) ω ∈ C j)})
        = μ ({ω | (∀ i, X i.val ω ∈ A i) ∧ X r ω ∈ B ∧ (∀ j, X (r + 1 + j.val) ω ∈ C j)}) := by
      intro A hA C hC
      -- This is exactly what contractable_finite_cylinder_measure provides
      exact contractable_finite_cylinder_measure X hX hX_meas hrm A hA B hB C hC

    -- Step 3: RHS computation - CRITICAL INFRASTRUCTURE GAP
    -- Integrating CE over cylinder E_past ∩ E_future (where E_future ∈ finFutureSigma)
    -- should equal reindexed cylinder measure via Fubini/disintegration
    --
    -- Similar to kernel_integral_product_factorization in ViaKoopman.lean,
    -- this requires infrastructure not currently available in mathlib
    have rhs_computation : ∀ (A : Fin r → Set α) (hA : ∀ i, MeasurableSet (A i))
        (C : Fin k → Set α) (hC : ∀ i, MeasurableSet (C i)),
      let E_cyl := {ω | (∀ i, X i.val ω ∈ A i) ∧ (∀ j, X (m + 1 + j.val) ω ∈ C j)}
      ∫ ω in E_cyl, (Exchangeability.Probability.condExpWith μ
          (finFutureSigma X m k) (finFutureSigma_le_ambient X m k hX_meas)
          (Set.indicator B (fun _ => (1 : ℝ)) ∘ X r)) ω ∂μ
        = (μ ({ω | (∀ i, X i.val ω ∈ A i) ∧ X r ω ∈ B ∧ (∀ j, X (r + 1 + j.val) ω ∈ C j)})).toReal := by
      intro A hA C hC
      classical
      -- Notation for past/future cylinders
      set f : Ω → ℝ :=
        Set.indicator B (fun _ => (1 : ℝ)) ∘ X r with hf_def
      set g : Ω → ℝ :=
        Exchangeability.Probability.condExpWith μ
          (finFutureSigma X m k) (finFutureSigma_le_ambient X m k hX_meas) f with hg_def
      set E_past : Set Ω := {ω | ∀ i : Fin r, X i.val ω ∈ A i} with hEp_def
      set E_future : Set Ω := {ω | ∀ j : Fin k, X (m + 1 + j.val) ω ∈ C j} with hEf_def
      set E_target := {ω | ∀ i : Fin r, X i.val ω ∈ A i ∧ X r ω ∈ B
                          ∧ ∀ j : Fin k, X (r + 1 + j.val) ω ∈ C j}
      have hE_future_meas :
          MeasurableSet[finFutureSigma X m k] E_future := by
        classical
        let futureMap := fun ω => fun j : Fin k => X (m + 1 + j.val) ω
        have h_preimage :
            E_future = futureMap ⁻¹' finCylinder (α:=α) k C := by
          ext ω
          simp [hEf_def, futureMap, finCylinder, cylinder]
        simpa [h_preimage, finFutureSigma]
          using (⟨_, finCylinder_measurable hC, rfl⟩ :
            MeasurableSet[finFutureSigma X m k] (futureMap ⁻¹' finCylinder (α:=α) k C))
      have hf_int : Integrable f μ := by
        classical
        have : Integrable (fun _ : Ω => (1 : ℝ)) μ := integrable_const (1 : ℝ)
        simpa [hf_def] using
          this.indicator (μ := μ) (s := X r ⁻¹' B) ((hX_meas r) hB)
      have hE_past_meas : MeasurableSet E_past := by
        simpa [hEp_def] using
          firstRCylinder_measurable_ambient X r A hX_meas hA
      have hg_meas :
          AEStronglyMeasurable[finFutureSigma X m k] g μ := by
        classical
        simp [hg_def, Exchangeability.Probability.condExpWith]
          using stronglyMeasurable_condexp.aestronglyMeasurable
            (μ := μ) (m := finFutureSigma X m k) (f := f)
      have hg_int : Integrable g μ := by
        classical
        simpa [hg_def, Exchangeability.Probability.condExpWith]
          using ProbabilityTheory.integrable_condexp
            (μ := μ)
            (m := finFutureSigma X m k)
            (hm := finFutureSigma_le_ambient X m k hX_meas)
            (f := f)
      -- Rewrite the integral using indicators for the past/future events
      have h_integral_rewrite :
          ∫ ω in {ω | (∀ i, X i.val ω ∈ A i) ∧ (∀ j, X (m + 1 + j.val) ω ∈ C j)}, g ω ∂μ
            = ∫ ω, Set.indicator E_past (fun _ => (1 : ℝ)) ω
                * Set.indicator E_future (fun _ => (1 : ℝ)) ω * g ω ∂μ := by
        classical
        have h_indicator_eq :
            Set.indicator (E_past ∩ E_future) g
              = fun ω => Set.indicator E_past (fun _ => (1 : ℝ)) ω
                  * Set.indicator E_future (fun _ => (1 : ℝ)) ω * g ω := by
          ext ω
          by_cases hp : ω ∈ E_past
          · by_cases hf : ω ∈ E_future
            · simp [hp, hf, Set.indicator_of_mem]
            · simp [hp, hf, Set.indicator_of_not_mem, hEp_def, hEf_def]
          · simp [hp, Set.indicator_of_not_mem, hEp_def]
        simp [hEp_def, hEf_def, h_indicator_eq, MeasureTheory.integral_indicator, hg_int]
      -- After rewriting, the integrand involves the past indicator, the future indicator,
      -- and the conditional expectation.
      -- Pull out the future-measurable indicator from the conditional expectation
      have h_indicator_meas :
          AEStronglyMeasurable[finFutureSigma X m k]
            (Set.indicator E_future (fun _ => (1 : ℝ))) μ := by
        classical
        have : MeasurableSet[finFutureSigma X m k] E_future := hE_future_meas
        simpa [hEf_def] using
          (Measurable.indicator measurable_const this).aestronglyMeasurable
      have h_indicator_mul_f :
          Integrable (fun ω => Set.indicator E_future (fun _ => (1 : ℝ)) ω * f ω) μ := by
        classical
        have : (fun ω => Set.indicator E_future (fun _ => (1 : ℝ)) ω * f ω)
              = Set.indicator E_future (fun ω => f ω) := by
          funext ω
          by_cases hω : ω ∈ E_future
          · simp [hω, hf_def, hEf_def]
          · simp [hω, hf_def, hEf_def]
        simpa [this] using hf_int.indicator (μ := μ) (s := E_future) hE_future_meas
      have h_condexp_pullout :
          (fun ω =>
              Set.indicator E_future (fun _ => (1 : ℝ)) ω * g ω)
            =ᵐ[μ]
          Exchangeability.Probability.condExpWith μ
            (finFutureSigma X m k) (finFutureSigma_le_ambient X m k hX_meas)
            (fun ω => Set.indicator E_future (fun _ => (1 : ℝ)) ω * f ω) := by
        classical
        have h_ce :
            μ[(fun ω => Set.indicator E_future (fun _ => (1 : ℝ)) ω * f ω)
                | finFutureSigma X m k]
              =ᵐ[μ]
            (fun ω =>
                Set.indicator E_future (fun _ => (1 : ℝ)) ω *
                  μ[f | finFutureSigma X m k] ω) := by
          have hg_condexp :
              Integrable f μ := hf_int
          have h_prod_int :
              Integrable (fun ω =>
                  Set.indicator E_future (fun _ => (1 : ℝ)) ω * f ω) μ :=
            h_indicator_mul_f
          exact MeasureTheory.condExp_mul_of_aestronglyMeasurable_left
            (μ := μ) (m := finFutureSigma X m k)
            h_indicator_meas
            h_prod_int
            hg_condexp
        have h_ce' :
            (fun ω =>
                Set.indicator E_future (fun _ => (1 : ℝ)) ω *
                  μ[f | finFutureSigma X m k] ω)
              =ᵐ[μ]
            (fun ω =>
                Set.indicator E_future (fun _ => (1 : ℝ)) ω * g ω) := by
          classical
          have : μ[f | finFutureSigma X m k]
              =ᵐ[μ]
            Exchangeability.Probability.condExpWith μ
              (finFutureSigma X m k) (finFutureSigma_le_ambient X m k hX_meas) f := by
            simpa [Exchangeability.Probability.condExpWith]
          exact this.mul_left (Set.indicator E_future (fun _ => (1 : ℝ)))
        have h_combined := h_ce.trans h_ce'
        -- Unfold condExpWith to obtain the desired identity
        refine h_combined.symm.trans ?_
        simpa [Exchangeability.Probability.condExpWith]
      -- Replace the integrand using the conditional expectation pull-out
      have h_integral_pullout :
          ∫ ω, Set.indicator E_past (fun _ => (1 : ℝ)) ω
                * Set.indicator E_future (fun _ => (1 : ℝ)) ω * g ω ∂μ
            =
          ∫ ω, Set.indicator E_past (fun _ => (1 : ℝ)) ω *
            Exchangeability.Probability.condExpWith μ
              (finFutureSigma X m k) (finFutureSigma_le_ambient X m k hX_meas)
              (fun ω => Set.indicator E_future (fun _ => (1 : ℝ)) ω * f ω) ω ∂μ := by
        classical
        refine integral_congr_ae ?_
        filter_upwards [h_condexp_pullout] with ω hω
        simpa [mul_comm, mul_left_comm, mul_assoc]
      -- Step 3: Contractability on triples (past block, current coordinate, finite future)
      -- Introduce the joint maps that capture the needed coordinates.
      set Z_r : Ω → (Fin r → α) := fun ω i => X i.val ω
      set Y_future : Ω → (Fin k → α) := fun ω j => X (m + 1 + j.val) ω
      set Y_tail : Ω → (Fin k → α) := fun ω j => X (r + 1 + j.val) ω
      set triple_future := fun ω => (Z_r ω, X r ω, Y_future ω)
      set triple_tail := fun ω => (Z_r ω, X r ω, Y_tail ω)
      -- Measurability of the building blocks
      have hZ_meas : Measurable Z_r := by
        classical
        apply measurable_pi_lambda
        intro i
        simpa [Z_r] using hX_meas i.val
      have hY_future_meas : Measurable Y_future := by
        classical
        apply measurable_pi_lambda
        intro j
        simpa [Y_future] using hX_meas (m + 1 + j.val)
      have hY_tail_meas : Measurable Y_tail := by
        classical
        apply measurable_pi_lambda
        intro j
        simpa [Y_tail] using hX_meas (r + 1 + j.val)
      have h_triple_future :
          Measurable triple_future := by
        classical
        -- View the triple as `(Z_r, (X_r, Y_future))`
        have h_pair : Measurable (fun ω => (X r ω, Y_future ω)) :=
          (hX_meas r).prodMk hY_future_meas
        simpa [triple_future] using hZ_meas.prodMk h_pair
      have h_triple_tail :
          Measurable triple_tail := by
        classical
        have h_pair : Measurable (fun ω => (X r ω, Y_tail ω)) :=
          (hX_meas r).prodMk hY_tail_meas
        simpa [triple_tail] using hZ_meas.prodMk h_pair
      -- TODO: Use contractability to prove `Measure.map triple_future μ = Measure.map triple_tail μ`.
      -- TODO: Rewrite the integral using these pushforward measures.
      -- TODO: Apply the tower property to push `Set.indicator E_past` through the conditional expectation.
      -- TODO: Invoke contractability to replace the integrand with the probability of the target set.
      -- TODO: Translate the resulting integral into `(μ E_target).toReal`.
      sorry

    -- Combine steps 1-3 to show cylinders are in GoodSets
    have cylinders_in_goodsets : ∀ (A : Fin r → Set α) (hA : ∀ i, MeasurableSet (A i))
        (C : Fin k → Set α) (hC : ∀ i, MeasurableSet (C i)),
      let E_cyl := {ω | (∀ i, X i.val ω ∈ A i) ∧ (∀ j, X (m + 1 + j.val) ω ∈ C j)}
      E_cyl ∈ GoodSets := by
      intro A hA C hC
      -- Explicitly bind E_cyl from the let in the type
      show MeasurableSet[firstRSigma X r ⊔ finFutureSigma X m k]
        {ω | (∀ i, X i.val ω ∈ A i) ∧ (∀ j, X (m + 1 + j.val) ω ∈ C j)} ∧ _
      constructor
      · -- Measurability of E_cyl in firstRSigma X r ⊔ finFutureSigma X m k
        -- E_cyl = E_past ∩ E_future where:
        -- E_past = {∀ i, X i ∈ A i} = firstRCylinder X r A
        -- E_future = {∀ j, X (m+1+j) ∈ C j}

        -- Define the components
        let E_past := firstRCylinder X r A
        let E_future : Set Ω := {ω | ∀ j : Fin k, X (m + 1 + j.val) ω ∈ C j}

        -- Show the set equals E_past ∩ E_future
        show MeasurableSet[firstRSigma X r ⊔ finFutureSigma X m k] (E_past ∩ E_future)

        have : {ω | (∀ i, X i.val ω ∈ A i) ∧ (∀ j, X (m + 1 + j.val) ω ∈ C j)} = E_past ∩ E_future := by
          ext ω
          simp [E_past, E_future, firstRCylinder]

        -- E_past is measurable in firstRSigma X r
        have hE_past : MeasurableSet[firstRSigma X r] E_past :=
          firstRCylinder_measurable_in_firstRSigma X r A hA

        -- E_future is measurable in finFutureSigma X m k
        -- finFutureSigma is comap of (fun ω j => X (m+1+j) ω), so E_future is preimage
        have hE_future : MeasurableSet[finFutureSigma X m k] E_future := by
          -- E_future = preimage of finite cylinder under the future map
          -- The future map is: fun ω => fun i : Fin k => X (m + 1 + i.val) ω
          let futureMap := fun ω => fun i : Fin k => X (m + 1 + i.val) ω

          -- E_future = futureMap ⁻¹' (finCylinder k C)
          have h_preimage : E_future = futureMap ⁻¹' (finCylinder (α:=α) k C) := by
            ext ω
            simp [E_future, futureMap, finCylinder]

          rw [h_preimage]
          -- finFutureSigma is the comap of futureMap
          -- A set is measurable in a comap iff it's a preimage of a measurable set
          unfold finFutureSigma
          exact ⟨_, finCylinder_measurable hC, rfl⟩

        -- Intersection is measurable in the sup
        -- Lift each set to the sup using le_sup_left/right, then apply MeasurableSet.inter
        have hE_past_sup : MeasurableSet[firstRSigma X r ⊔ finFutureSigma X m k] E_past :=
          @le_sup_left _ _ (firstRSigma X r) (finFutureSigma X m k) _ hE_past
        have hE_future_sup : MeasurableSet[firstRSigma X r ⊔ finFutureSigma X m k] E_future :=
          @le_sup_right _ _ (firstRSigma X r) (finFutureSigma X m k) _ hE_future
        exact MeasurableSet.inter hE_past_sup hE_future_sup
      · -- Integral equality
        rw [lhs_computation A hA C hC, rhs_computation A hA C hC]
        rw [contractability_step A hA C hC]

    -- Part B: Monotone class properties
    --
    -- Show GoodSets is closed under monotone limits
    have goodsets_closed_under_monotone_union : ∀ (E_seq : ℕ → Set Ω),
        (∀ n, E_seq n ∈ GoodSets) →
        Monotone E_seq →
        (⋃ n, E_seq n) ∈ GoodSets := by
      intro E_seq hE_in hMono
      constructor
      · -- Measurability of union: countable union of measurable sets is measurable
        apply MeasurableSet.iUnion
        intro n
        exact (hE_in n).1
      · -- Integral equality for union
        -- Use measure continuity from below for indicator functions
        -- For indicator B (X r): integral over set = measure of preimage ∩ set
        -- Similarly for conditional expectation
        -- Since equality holds for all E_n, it holds for the limit

        -- Extract the functions we're integrating
        classical
        set f := fun ω => Set.indicator (X r ⁻¹' B) (fun _ => (1 : ℝ)) ω with hf_def
        set g := fun ω => Exchangeability.Probability.condExpWith μ
          (finFutureSigma X m k) (finFutureSigma_le_ambient X m k hX_meas)
          (Set.indicator B (fun _ => (1 : ℝ)) ∘ X r) ω with hg_def

        -- For each n, we have ∫_{E_n} f = ∫_{E_n} g
        have h_eq_n : ∀ n, ∫ ω in E_seq n, f ω ∂μ = ∫ ω in E_seq n, g ω ∂μ := by
          intro n
          exact (hE_in n).2

        -- Need to show: ∫_{⋃ E_n} f = ∫_{⋃ E_n} g
        -- Use monotone convergence for integrals over increasing sets

        -- f is integrable (bounded indicator function)
        have hf_int : IntegrableOn f (⋃ n, E_seq n) μ := by
          apply Integrable.integrableOn
          exact (integrable_const (1 : ℝ)).indicator (hX_meas r hB)

        -- g is integrable (conditional expectation)
        have hg_int : IntegrableOn g (⋃ n, E_seq n) μ := by
          apply Integrable.integrableOn
          exact integrable_condExp

        -- Measurability of sets (lift from sup to ambient)
        have hE_meas : ∀ n, MeasurableSet (E_seq n) := by
          intro n
          have h_sup_le : firstRSigma X r ⊔ finFutureSigma X m k ≤ (inferInstance : MeasurableSpace Ω) := by
            apply sup_le
            · exact firstRSigma_le_ambient X r hX_meas
            · exact finFutureSigma_le_ambient X m k hX_meas
          exact h_sup_le (E_seq n) (hE_in n).1

        -- Apply tendsto_setIntegral_of_monotone
        have hf_lim := tendsto_setIntegral_of_monotone hE_meas hMono hf_int
        have hg_lim := tendsto_setIntegral_of_monotone hE_meas hMono hg_int

        -- The sequences are equal for all n
        have : Tendsto (fun n => ∫ ω in E_seq n, f ω ∂μ) atTop (nhds (∫ ω in ⋃ n, E_seq n, g ω ∂μ)) := by
          rw [tendsto_congr' (Eventually.of_forall h_eq_n)]
          exact hg_lim

        exact tendsto_nhds_unique hf_lim this

    have goodsets_closed_under_monotone_inter : ∀ (E_seq : ℕ → Set Ω),
        (∀ n, E_seq n ∈ GoodSets) →
        Antitone E_seq →
        (⋂ n, E_seq n) ∈ GoodSets := by
      intro E_seq hE_in hAnti
      constructor
      · -- Measurability of intersection: countable intersection of measurable sets is measurable
        apply MeasurableSet.iInter
        intro n
        exact (hE_in n).1
      · -- Integral equality for intersection
        -- Use measure continuity from above for indicator functions
        -- For decreasing sequences with finite measure

        -- Need to show: ∫_{⋂ E_n} indicator = ∫_{⋂ E_n} condexp
        -- Use dominated convergence for integrals over decreasing sets

        -- f is integrable on E_seq 0 (bounded indicator function)
        have hf_int : ∃ i, IntegrableOn f (E_seq i) μ := by
          use 0
          apply Integrable.integrableOn
          exact (integrable_const (1 : ℝ)).indicator (hX_meas r hB)

        -- g is integrable on E_seq 0 (conditional expectation)
        have hg_int : ∃ i, IntegrableOn g (E_seq i) μ := by
          use 0
          apply Integrable.integrableOn
          exact integrable_condExp

        -- Measurability of sets (lift from sup to ambient)
        have hE_meas : ∀ n, MeasurableSet (E_seq n) := by
          intro n
          have h_sup_le : firstRSigma X r ⊔ finFutureSigma X m k ≤ (inferInstance : MeasurableSpace Ω) := by
            apply sup_le
            · exact firstRSigma_le_ambient X r hX_meas
            · exact finFutureSigma_le_ambient X m k hX_meas
          exact h_sup_le (E_seq n) (hE_in n).1

        -- Apply tendsto_setIntegral_of_antitone
        have hf_lim := tendsto_setIntegral_of_antitone hE_meas hAnti hf_int
        have hg_lim := tendsto_setIntegral_of_antitone hE_meas hAnti hg_int

        -- The sequences are equal for all n
        have : Tendsto (fun n => ∫ ω in E_seq n, f ω ∂μ) atTop (nhds (∫ ω in ⋂ n, E_seq n, g ω ∂μ)) := by
          rw [tendsto_congr' (Eventually.of_forall h_eq_n)]
          exact hg_lim

        exact tendsto_nhds_unique hf_lim this

    -- Part C: Apply Dynkin's π-λ theorem
    --
    -- Goal: Show E ∈ GoodSets for any E measurable in firstRSigma X r ⊔ finFutureSigma X m k
    --
    -- Strategy (standard Dynkin argument):
    -- 1. **π-system**: Show cylinders form a π-system (closed under ∩)
    --    - Cylinder = E_past ∩ E_future where E_past ∈ firstRSigma, E_future ∈ finFutureSigma
    --    - Intersection of cylinders is a cylinder
    --    - Use cylinders_in_goodsets to show π-system ⊆ GoodSets
    --
    -- 2. **λ-system**: Show GoodSets is a Dynkin system:
    --    - Contains Ω: ∫_Ω f = ∫_Ω μ[f|m] by tower property
    --    - Closed under complements: use integral decomposition
    --    - Closed under disjoint increasing unions: Part B (goodsets_closed_under_monotone_union)
    --
    -- 3. **Application**: Apply mathlib's Dynkin π-λ theorem
    --    - Lemma: `MeasureTheory.generateFrom_eq_iInf` or `isPiSystem.generateFrom_eq`
    --    - Since π-system ⊆ λ-system, generated σ-algebra ⊆ λ-system
    --    - Cylinders generate firstRSigma X r ⊔ finFutureSigma X m k
    --    - Therefore E ∈ GoodSets

    -- Define the π-system of cylinder sets
    let CylinderSets : Set (Set Ω) := {E |
      ∃ (A : Fin r → Set α) (hA : ∀ i, MeasurableSet (A i))
        (C : Fin k → Set α) (hC : ∀ i, MeasurableSet (C i)),
      E = {ω | (∀ i, X i.val ω ∈ A i) ∧ (∀ j, X (m + 1 + j.val) ω ∈ C j)}}

    -- Step 1: Show CylinderSets is a π-system
    have cylinder_is_pi : IsPiSystem CylinderSets := by
      intro E₁ hE₁ E₂ hE₂ hnonempty
      simp only [CylinderSets, Set.mem_setOf_eq] at hE₁ hE₂ ⊢
      obtain ⟨A₁, hA₁, C₁, hC₁, rfl⟩ := hE₁
      obtain ⟨A₂, hA₂, C₂, hC₂, rfl⟩ := hE₂
      -- Intersection: {∀i X_i ∈ A₁_i ∩ A₂_i} ∩ {∀j X_{m+1+j} ∈ C₁_j ∩ C₂_j}
      use fun i => A₁ i ∩ A₂ i, fun i => (hA₁ i).inter (hA₂ i)
      use fun j => C₁ j ∩ C₂ j, fun j => (hC₁ j).inter (hC₂ j)
      ext ω
      simp only [Set.mem_inter_iff, Set.mem_setOf_eq]
      constructor
      · intro ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩
        constructor
        · intro i; exact ⟨h1 i, h3 i⟩
        · intro j; exact ⟨h2 j, h4 j⟩
      · intro ⟨h1, h2⟩
        constructor
        · constructor
          · intro i; exact (h1 i).1
          · intro j; exact (h2 j).1
        · constructor
          · intro i; exact (h1 i).2
          · intro j; exact (h2 j).2

    -- Step 2: Show CylinderSets ⊆ GoodSets
    have cylinders_in_good : CylinderSets ⊆ GoodSets := by
      intro E hE
      simp only [CylinderSets, Set.mem_setOf_eq] at hE
      obtain ⟨A, hA, C, hC, rfl⟩ := hE
      exact cylinders_in_goodsets A hA C hC

    -- Step 3: Show cylinders generate the σ-algebra
    have h_gen : firstRSigma X r ⊔ finFutureSigma X m k = MeasurableSpace.generateFrom CylinderSets := by
      apply le_antisymm
      · -- (⊆) Show sup ≤ generateFrom CylinderSets
        -- Need to show both components ≤ generateFrom CylinderSets
        apply sup_le
        · -- firstRSigma X r ≤ generateFrom CylinderSets
          -- Strategy: Use comap_generateFrom + generateFrom_pi to reduce to showing
          -- preimages of rectangles are cylinders

          -- Product σ-algebra is generated by rectangles
          have h_pi : (inferInstance : MeasurableSpace (Fin r → α)) =
              MeasurableSpace.generateFrom (Set.univ.pi '' (Set.univ.pi fun i => {s : Set α | MeasurableSet s})) := by
            haveI : Finite (Fin r) := inferInstance
            exact generateFrom_pi.symm

          -- Comap of generated σ-algebra = σ-algebra generated by preimages
          have h_comap : firstRSigma X r =
              MeasurableSpace.generateFrom (Set.preimage (firstRMap X r) '' (Set.univ.pi '' (Set.univ.pi fun i => {s : Set α | MeasurableSet s}))) := by
            rw [firstRSigma, h_pi, MeasurableSpace.comap_generateFrom]

          -- Now show generators are ≤ generateFrom CylinderSets
          rw [h_comap]
          apply MeasurableSpace.generateFrom_le
          intro E' hE'
          -- E' is a preimage of a rectangle
          simp only [Set.mem_image, Set.mem_pi, Set.mem_univ, Set.mem_setOf_eq, true_and] at hE'
          obtain ⟨rect, ⟨t, ht, rfl⟩, rfl⟩ := hE'
          -- rect = univ.pi t where each t i is measurable
          -- E' = (firstRMap X r)⁻¹' (univ.pi t) = {ω | ∀ i, X i ω ∈ t i}

          -- Show this is a cylinder: use A := t, C := fun _ => univ
          apply MeasurableSpace.measurableSet_generateFrom
          use t, (fun i => ht i trivial)
          use (fun (_ : Fin k) => Set.univ), (fun _ => MeasurableSet.univ)
          ext ω
          simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_and, Set.mem_setOf_eq]
          constructor
          · intro h
            constructor
            · intro i
              exact h i (Set.mem_univ i)
            · intro j
              trivial
          · intro ⟨h, _⟩ i _
            exact h i
        · -- finFutureSigma X m k ≤ generateFrom CylinderSets
          -- Same strategy as firstRSigma case:
          -- 1. Product σ-algebra = generateFrom rectangles
          -- 2. Comap of generated σ-algebra = σ-algebra generated by preimages
          -- 3. Show each preimage is a cylinder

          -- Product σ-algebra is generated by rectangles
          have h_pi : (inferInstance : MeasurableSpace (Fin k → α)) =
              MeasurableSpace.generateFrom (Set.univ.pi '' (Set.univ.pi fun i => {s : Set α | MeasurableSet s})) := by
            haveI : Finite (Fin k) := inferInstance
            exact generateFrom_pi.symm

          -- Comap of generated σ-algebra = σ-algebra generated by preimages
          have h_comap : finFutureSigma X m k =
              MeasurableSpace.generateFrom (Set.preimage (fun ω => fun i : Fin k => X (m + 1 + i.val) ω) ''
                (Set.univ.pi '' (Set.univ.pi fun i => {s : Set α | MeasurableSet s}))) := by
            rw [finFutureSigma, h_pi, MeasurableSpace.comap_generateFrom]

          -- Now show generators are ≤ generateFrom CylinderSets
          rw [h_comap]
          apply MeasurableSpace.generateFrom_le
          intro E' hE'
          -- E' is a preimage of a rectangle
          simp only [Set.mem_image, Set.mem_pi, Set.mem_univ, Set.mem_setOf_eq, true_and] at hE'
          obtain ⟨rect, ⟨c, hc, rfl⟩, rfl⟩ := hE'
          -- Show this is a cylinder: use A := fun _ => univ, C := c
          apply MeasurableSpace.measurableSet_generateFrom
          use (fun (_ : Fin r) => Set.univ), (fun _ => MeasurableSet.univ)
          use c, (fun j => hc j trivial)
          ext ω
          simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_and, Set.mem_setOf_eq]
          constructor
          · intro h
            constructor
            · intro i
              trivial
            · intro j
              exact h j (Set.mem_univ j)
          · intro ⟨_, h⟩ j _
            exact h j
      · -- (⊇) Show generateFrom CylinderSets ≤ sup
        apply MeasurableSpace.generateFrom_le
        intro E hE
        -- E is a cylinder, so E = {ω | ∀i X_i ω ∈ A_i ∧ ∀j X_{m+1+j} ω ∈ C_j}
        simp only [CylinderSets, Set.mem_setOf_eq] at hE
        obtain ⟨A, hA, C, hC, rfl⟩ := hE
        -- Need to show this is measurable in sup
        -- E = E_past ∩ E_future where E_past ∈ firstRSigma, E_future ∈ finFutureSigma

        -- Define the two components
        let E_past : Set Ω := {ω | ∀ i, X i.val ω ∈ A i}
        let E_future : Set Ω := {ω | ∀ j, X (m + 1 + j.val) ω ∈ C j}

        -- Show E equals E_past ∩ E_future
        have hE_eq : {ω | (∀ i, X i.val ω ∈ A i) ∧ (∀ j, X (m + 1 + j.val) ω ∈ C j)}
            = E_past ∩ E_future := by
          ext ω
          simp [E_past, E_future, Set.mem_inter_iff, Set.mem_setOf_eq]

        rw [hE_eq]

        -- Show E_past is measurable in the sup
        have hE_past_in_first : MeasurableSet[firstRSigma X r] E_past := by
          simp only [firstRSigma]
          -- E_past = (firstRMap X r)⁻¹({f | ∀ i, f i ∈ A i})
          let S := Set.univ.pi A
          have hS_meas : MeasurableSet S := MeasurableSet.univ_pi hA
          have hE_past_def : E_past = (firstRMap X r) ⁻¹' S := by
            ext ω
            simp only [E_past, S, firstRMap, Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_setOf]
          rw [hE_past_def]
          -- Witness that E_past is in the comap σ-algebra
          exact ⟨S, hS_meas, rfl⟩
        -- Lift to sup: If E is measurable in m₁ and m₁ ≤ m₁ ⊔ m₂, then E is measurable in sup
        have hE_past_sup : MeasurableSet[firstRSigma X r ⊔ finFutureSigma X m k] E_past :=
          @le_sup_left _ _ (firstRSigma X r) (finFutureSigma X m k) _ hE_past_in_first

        -- Show E_future is measurable in the sup
        have hE_future_in_fin : MeasurableSet[finFutureSigma X m k] E_future := by
          simp only [finFutureSigma]
          -- E_future = (futureMap)⁻¹({g | ∀ j, g j ∈ C j})
          let T := Set.univ.pi C
          have hT_meas : MeasurableSet T := MeasurableSet.univ_pi hC
          have hE_future_def : E_future = (fun ω => fun j : Fin k => X (m + 1 + j.val) ω) ⁻¹' T := by
            ext ω
            simp only [E_future, T, Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_setOf]
          rw [hE_future_def]
          -- Witness that E_future is in the comap σ-algebra
          exact ⟨T, hT_meas, rfl⟩
        -- Lift to sup: If F is measurable in m₂ and m₂ ≤ m₁ ⊔ m₂, then F is measurable in sup
        have hE_future_sup : MeasurableSet[firstRSigma X r ⊔ finFutureSigma X m k] E_future :=
          @le_sup_right _ _ (firstRSigma X r) (finFutureSigma X m k) _ hE_future_in_fin

        -- Intersection of measurable sets in the sup
        exact MeasurableSet.inter hE_past_sup hE_future_sup

    -- Step 4: Apply Dynkin's π-λ theorem (induction_on_inter)
    -- Predicate: E belongs to GoodSets
    refine MeasurableSpace.induction_on_inter h_gen cylinder_is_pi ?_ ?_ ?_ ?_ E hE

    · -- Base case: empty set
      simp [setIntegral_empty]

    · -- Basic case: cylinders
      intro t ht
      exact (cylinders_in_good ht).2

    · -- Complement case
      intro t htm ht_in_good
      -- Goal: Show ∫_{tᶜ} indicator = ∫_{tᶜ} condexp
      -- Have IH: ∫_t indicator = ∫_t condexp

      classical
      set f := fun ω => Set.indicator B (fun _ => (1 : ℝ)) (X r ω) with hf_def
      set g :=
          fun ω =>
            Exchangeability.Probability.condExpWith μ
              (finFutureSigma X m k) (finFutureSigma_le_ambient X m k hX_meas)
              (Set.indicator B (fun _ => (1 : ℝ)) ∘ X r) ω with hg_def
      have htm_ambient :
          MeasurableSet t :=
        (sup_le (firstRSigma_le_ambient X r hX_meas)
            (finFutureSigma_le_ambient X m k hX_meas)) _ htm
      -- Integrability of indicator (bounded by 1)
      have hf_int_raw :
          Integrable (fun ω => Set.indicator B (fun _ => (1 : ℝ)) (X r ω)) μ := by
        apply Integrable.indicator
        · exact integrable_const (1 : ℝ)
        · exact (hX_meas r) hB
      have hf_int : Integrable f μ := by
        simpa [hf_def] using hf_int_raw
      -- Integrability of conditional expectation
      -- Conditional expectation is always integrable (mathlib: integrable_condexp)
      have hh_int : Integrable (fun ω => Exchangeability.Probability.condExpWith μ
          (finFutureSigma X m k) (finFutureSigma_le_ambient X m k hX_meas)
          (Set.indicator B (fun _ => (1 : ℝ)) ∘ X r) ω) μ := by
        -- condExpWith unfolds to μ[f | m], and conditional expectation is always integrable
        simp only [Exchangeability.Probability.condExpWith]
        exact integrable_condExp

      -- Lift measurability of t from sub-σ-algebra to ambient
      have htm_ambient : MeasurableSet t := by
        have h_sup_le : firstRSigma X r ⊔ finFutureSigma X m k ≤ (inferInstance : MeasurableSpace Ω) := by
          apply sup_le
          · exact firstRSigma_le_ambient X r hX_meas
          · exact finFutureSigma_le_ambient X m k hX_meas
        exact h_sup_le t htm

      -- Apply setIntegral_compl decomposition: ∫_{tᶜ} f = ∫_Ω f - ∫_t f
      have h_decomp_g : ∫ ω in tᶜ, Set.indicator B (fun _ => (1 : ℝ)) (X r ω) ∂μ =
          ∫ ω, Set.indicator B (fun _ => (1 : ℝ)) (X r ω) ∂μ -
          ∫ ω in t, Set.indicator B (fun _ => (1 : ℝ)) (X r ω) ∂μ := by
        -- Use integral_add_compl: ∫_t f + ∫_{tᶜ} f = ∫_Ω f, then rearrange
        have h := integral_add_compl htm_ambient hg_int
        linarith

      have h_decomp_h : ∫ ω in tᶜ, (Exchangeability.Probability.condExpWith μ
          (finFutureSigma X m k) (finFutureSigma_le_ambient X m k hX_meas)
          (Set.indicator B (fun _ => (1 : ℝ)) ∘ X r)) ω ∂μ =
          ∫ ω, (Exchangeability.Probability.condExpWith μ
            (finFutureSigma X m k) (finFutureSigma_le_ambient X m k hX_meas)
            (Set.indicator B (fun _ => (1 : ℝ)) ∘ X r)) ω ∂μ -
          ∫ ω in t, (Exchangeability.Probability.condExpWith μ
            (finFutureSigma X m k) (finFutureSigma_le_ambient X m k hX_meas)
            (Set.indicator B (fun _ => (1 : ℝ)) ∘ X r)) ω ∂μ := by
        -- Same as h_decomp_g: use integral_add_compl and rearrange
        have h_eq := integral_add_compl htm_ambient hh_int
        linarith

      -- Tower property: ∫_Ω g = ∫_Ω E[g|m]
      have h_tower : ∫ ω, Set.indicator B (fun _ => (1 : ℝ)) (X r ω) ∂μ =
          ∫ ω, (Exchangeability.Probability.condExpWith μ
            (finFutureSigma X m k) (finFutureSigma_le_ambient X m k hX_meas)
            (Set.indicator B (fun _ => (1 : ℝ)) ∘ X r)) ω ∂μ := by
        -- Tower property: ∫ f dμ = ∫ μ[f|m] dμ
        -- Write the integrand as a composition so integral_condexp applies directly
        set f : Ω → ℝ := (Set.indicator B (fun _ => (1 : ℝ)) ∘ X r) with hf
        -- integral_condexp says ∫ μ[f|m] = ∫ f; we flip it with .symm to match the goal
        simpa [hf, Exchangeability.Probability.condExpWith] using
          (integral_condExp
            (μ := μ)
            (m := finFutureSigma X m k)
            (hm := finFutureSigma_le_ambient X m k hX_meas)
            (f := f)).symm

      -- Conclude using decomposition + tower + IH
      have h_result :
          ∫ ω in tᶜ, f ω ∂μ = ∫ ω in tᶜ, g ω ∂μ := by
        calc
          ∫ ω in tᶜ, f ω ∂μ
              = ∫ ω, f ω ∂μ - ∫ ω in t, f ω ∂μ := h_decomp_f
          _ = ∫ ω, g ω ∂μ - ∫ ω in t, f ω ∂μ := by
                have h := congrArg (fun x => x - ∫ ω in t, f ω ∂μ) h_tower
                simpa using h
          _ = ∫ ω, g ω ∂μ - ∫ ω in t, g ω ∂μ := by
                simpa [hf_def, hg_def] using ht_in_good
          _ = ∫ ω in tᶜ, g ω ∂μ := h_decomp_g.symm
      simpa [hf_def, hg_def] using h_result

    · -- Disjoint union case
      intro f hf_disj hf_meas hf_in_good
      -- Convert pairwise disjoint union to monotone union of partial sums
      -- Define partial sums: E_n = ⋃_{i<n} f i
      let E_partial := fun n => ⋃ i : Fin n, f i
      -- E_partial is monotone and ⋃_n E_partial n = ⋃_i f i
      have hE_partial_mono : Monotone E_partial := by
        intro m n hmn
        intro ω hω
        simp only [E_partial, Set.mem_iUnion] at hω ⊢
        obtain ⟨i, hω⟩ := hω
        exact ⟨Fin.castLE hmn i, hω⟩
      have hE_partial_eq : ⋃ n, E_partial n = ⋃ i, f i := by
        ext ω
        simp only [Set.mem_iUnion, E_partial]
        constructor
        · intro ⟨n, i, h⟩; exact ⟨i, h⟩
        · intro ⟨i, h⟩; exact ⟨i.succ, ⟨i, Nat.lt_succ_self i⟩, h⟩
      -- Each partial sum is in GoodSets
      have hE_partial_in : ∀ n, E_partial n ∈ GoodSets := by
        intro n
        constructor
        · -- Measurability
          apply MeasurableSet.iUnion
          intro i
          exact hf_meas i
        · -- Integral equality
          -- Use additivity of integrals over finite disjoint unions
          classical
          set g := fun ω => Set.indicator (X r ⁻¹' B) (fun _ => (1 : ℝ)) ω with hg_def
          set h := fun ω =>
            Exchangeability.Probability.condExpWith μ
            (finFutureSigma X m k) (finFutureSigma_le_ambient X m k hX_meas)
            (Set.indicator B (fun _ => (1 : ℝ)) ∘ X r)) ω
          -- For each i : Fin n, we have ∫_{f i.val} g = ∫_{f i.val} h by hypothesis
          have h_eq_i : ∀ i : Fin n, ∫ ω in f i.val, g ω ∂μ = ∫ ω in f i.val, h ω ∂μ := by
            intro i
            exact hf_in_good i.val
          -- Need: ∫_{E_partial n} g = ∫_{E_partial n} h
          -- Use integral_iUnion_fintype for both sides

          -- Apply additivity of setIntegrals over finite disjoint unions
          -- For finite n, ⋃ i : Fin n, f i is a finite union
          -- Use: ∫_{⋃ i, s i} f = ∑ i, ∫_{s i} f when sets are pairwise disjoint

          -- First establish pairwise disjoint on Fin n
          have hf_disj_fin : ∀ (i j : Fin n), i ≠ j → Disjoint (f i.val) (f j.val) := by
            intro i j hij
            have : (i : ℕ) ≠ (j : ℕ) := by
              intro h
              exact hij (Fin.ext h)
            exact hf_disj this

          -- Show E_partial n as finite union
          have hE_partial_n_eq : E_partial n = ⋃ i : Fin n, f i.val := rfl

          -- Apply setIntegral over finite disjoint union using integral_iUnion_fintype

          -- Define the restricted function for clearer types
          let f_fin : Fin n → Set Ω := fun i => f i.val

          -- Lift measurability from sub-σ-algebra to ambient
          have hf_meas_ambient : ∀ i : Fin n, MeasurableSet (f_fin i) := by
            intro i
            -- Show that sup ≤ ambient
            have h_sup_le : firstRSigma X r ⊔ finFutureSigma X m k ≤ (inferInstance : MeasurableSpace Ω) := by
              apply sup_le
              · exact firstRSigma_le_ambient X r hX_meas
              · exact finFutureSigma_le_ambient X m k hX_meas
            -- Lift measurability using ≤
            exact h_sup_le (f_fin i) (hf_meas i.val)

          -- Convert pairwise disjoint to Pairwise form
          have hf_disj_pairwise : Pairwise (Function.onFun Disjoint f_fin) := by
            intro i j hij
            exact hf_disj_fin i j hij

          -- Prove integrability of g on each f_fin i
          -- g is indicator of B under X r, which is integrable (bounded by 1)
          have hg_int : ∀ i : Fin n, IntegrableOn g (f_fin i) μ := by
            intro i
            refine Integrable.integrableOn ?_
            -- Indicator of constant 1 on measurable set B is integrable
            exact (integrable_const (1 : ℝ)).indicator ((hX_meas r) hB)

          -- Prove integrability of h on each f_fin i
          have hh_int : ∀ i : Fin n, IntegrableOn h (f_fin i) μ := by
            intro i
            -- h is a conditional expectation, which is integrable
            apply Integrable.integrableOn
            simp only [h, Exchangeability.Probability.condExpWith]
            exact integrable_condExp

          -- Rewrite E_partial using f_fin
          have hE_partial_n_eq' : E_partial n = ⋃ i : Fin n, f_fin i := by simp [f_fin, hE_partial_n_eq]

          -- Apply integral_iUnion_fintype for g
          have hg_sum : ∫ ω in E_partial n, g ω ∂μ = ∑ i, ∫ ω in f_fin i, g ω ∂μ := by
            rw [hE_partial_n_eq']
            exact integral_iUnion_fintype hf_meas_ambient hf_disj_pairwise hg_int

          -- Apply integral_iUnion_fintype for h
          have hh_sum : ∫ ω in E_partial n, h ω ∂μ = ∑ i, ∫ ω in f_fin i, h ω ∂μ := by
            rw [hE_partial_n_eq']
            exact integral_iUnion_fintype hf_meas_ambient hf_disj_pairwise hh_int

          -- Conclude using term-by-term equality
          rw [hg_sum, hh_sum]
          congr 1
          funext i
          exact h_eq_i i
      -- Apply monotone union closure
      rw [← hE_partial_eq]
      exact (goodsets_closed_under_monotone_union E_partial hE_partial_in hE_partial_mono).2

  -- **Step 2: Pass to limit as k → ∞ using martingale convergence**
  --
  -- Goal: Show that
  --   μ[indicator B ∘ X r | firstRSigma ⊔ futureFiltration]
  --     =ᵐ μ[indicator B ∘ X r | futureFiltration]
  --
  -- Strategy:
  -- 1. Observe that finFutureSigma X m k ↗ futureFiltration X m as k → ∞
  --    (finite future approximates infinite future)
  --
  -- 2. By finite_approx, for each k:
  --    μ[indicator B ∘ X r | firstRSigma ⊔ finFutureSigma_k] =ᵐ μ[indicator B ∘ X r | finFutureSigma_k]
  --
  -- 3. Apply Lévy's downward theorem (reverse martingale convergence):
  --    As the σ-algebras increase, the conditional expectations converge a.e.
  --    - LHS converges to μ[indicator B ∘ X r | firstRSigma ⊔ futureFiltration]
  --    - RHS converges to μ[indicator B ∘ X r | futureFiltration]
  --
  -- 4. Since they're equal at each finite k and converge, their limits are equal a.e.
  --
  -- Technical requirements:
  -- - Show {finFutureSigma X m k} forms an increasing filtration
  -- - Apply martingale convergence theorem from mathlib
  -- - Use dominated convergence for integrable functions (indicator is L¹)

  sorry -- TODO (2-3 hours): Implement Lévy's downward theorem application

/-- **Product formula for conditional expectations under conditional independence.**

Given two sets `A` (measurable in `mF`) and `B` (measurable in `mH`), under conditional
independence given `m`, the conditional expectation of the intersection indicator factors:
```
μ[1_{A∩B} | m] = μ[1_A | m] · μ[1_B | m]   a.e.
```

Now proven using `condexp_indicator_inter_bridge` from CondExp.lean, eliminating the
previous `: True` axiom stub. -/
lemma condexp_indicator_inter_of_condIndep
    {Ω : Type*} {m₀ : MeasurableSpace Ω} [StandardBorelSpace Ω]
    {μ : @Measure Ω m₀} [IsProbabilityMeasure μ]
    {m mF mH : MeasurableSpace Ω}
    (hm : m ≤ m₀) (hmF : mF ≤ m₀) (hmH : mH ≤ m₀)
    (hCI : ProbabilityTheory.CondIndep m mF mH hm μ)
    {A B : Set Ω} (hA : MeasurableSet[mF] A) (hB : MeasurableSet[mH] B) :
    μ[(A ∩ B).indicator (fun _ => (1 : ℝ)) | m]
      =ᵐ[μ]
    (μ[A.indicator (fun _ => (1 : ℝ)) | m] *
     μ[B.indicator (fun _ => (1 : ℝ)) | m]) :=
  Exchangeability.Probability.condexp_indicator_inter_bridge hm hmF hmH hCI hA hB

/-- **Finite-level factorization builder (formerly Axiom 3).**

For a contractable sequence, at any future level `m ≥ r`, the conditional expectation
of the product indicator factors:
```
μ[∏ᵢ<r 1_{Xᵢ∈Cᵢ} | σ(θₘ₊₁X)] = ∏ᵢ<r μ[1_{X₀∈Cᵢ} | σ(θₘ₊₁X)]
```

This iteratively applies conditional independence to pull out one coordinate at a time,
using contractability to replace each `Xᵢ` with `X₀`. -/
lemma finite_level_factorization
    {Ω α : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [MeasurableSpace α]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ℕ → Ω → α)
    (hX : Contractable μ X)
    (hX_meas : ∀ n, Measurable (X n))
    (r : ℕ) (C : Fin r → Set α) (hC : ∀ i, MeasurableSet (C i))
    (m : ℕ) (hm : m ≥ r) :
    μ[indProd X r C | futureFiltration X m]
      =ᵐ[μ]
    (fun ω => ∏ i : Fin r,
      μ[Set.indicator (C i) (fun _ => (1:ℝ)) ∘ (X 0) | futureFiltration X m] ω) := by
  classical
  induction r with
  | zero =>
    -- r = 0: empty product is 1
    -- Both indProd X 0 C and the RHS product are constant 1
    have h_ind : indProd X 0 C = fun _ => 1 := by
      funext ω; simp [indProd]
    have h_rhs : (fun ω => ∏ i : Fin 0,
        μ[Set.indicator (C i) (fun _ => (1:ℝ)) ∘ (X 0) | futureFiltration X m] ω) = fun _ => 1 := by
      funext ω; simp
    -- μ[indProd X 0 C | F] = μ[1 | F] = 1 = RHS (all definitional)
    conv_lhs => rw [h_ind]
    rw [condExp_const (futureFiltration_le X m hX_meas), h_rhs]
  | succ r ih =>
    -- r ↦ r+1: Inductive step using indicator factorization
    -- Must have r+1 ≤ m, which gives r < m for conditional independence
    have hrm : r < m := Nat.lt_of_succ_le hm

    -- Split C into "first r" and "last"
    let Cinit : Fin r → Set α := fun j => C (Fin.castSucc j)
    let Clast : Set α := C ⟨r, Nat.lt_succ_self r⟩
    have hCinit : ∀ j, MeasurableSet (Cinit j) := fun j => hC _
    have hClast : MeasurableSet Clast := hC ⟨r, Nat.lt_succ_self r⟩

    -- Factorize the product ∏_{i<r+1} 1_{Xᵢ∈Cᵢ} = (∏_{i<r} 1_{Xᵢ∈Cᵢ}) · 1_{Xᵣ∈Clast}
    have hsplit : indProd X (r+1) C
        = fun ω => indProd X r Cinit ω * Set.indicator Clast (fun _ => (1:ℝ)) (X r ω) := by
      funext ω
      simp only [indProd, Cinit, Clast]
      -- Split the product using Fin.prod_univ_castSucc
      rw [Fin.prod_univ_castSucc]
      rfl

    -- Express the two factors as indicators of sets
    set A := firstRCylinder X r Cinit with hA_def
    set B := X r ⁻¹' Clast with hB_def

    -- Rewrite indProd using indicator algebra
    have hf_indicator : indProd X r Cinit = A.indicator (fun _ => (1:ℝ)) :=
      indProd_eq_firstRCylinder_indicator X r Cinit

    have hg_indicator : (Set.indicator Clast (fun _ => (1:ℝ)) ∘ X r)
        = B.indicator (fun _ => (1:ℝ)) :=
      indicator_comp_preimage (X r) Clast 1

    -- The product is the indicator of A ∩ B
    have hprod_indicator :
        (fun ω => indProd X r Cinit ω * (Set.indicator Clast (fun _ => (1:ℝ)) (X r ω)))
        = (A ∩ B).indicator (fun _ => (1:ℝ)) := by
      ext ω
      have hg' : Set.indicator Clast (fun _ => (1:ℝ)) (X r ω) = B.indicator (fun _ => (1:ℝ)) ω := by
        have := congr_fun hg_indicator ω
        simp only [Function.comp_apply] at this
        exact this
      rw [congr_fun hf_indicator ω, hg']
      have := congr_fun (indicator_mul_indicator_eq_indicator_inter A B 1 1) ω
      simp only [Pi.mul_apply] at this
      convert this using 1
      ring

    -- Measurability of A in firstRSigma X r
    have hA_meas_firstR : MeasurableSet[firstRSigma X r] A := by
      rw [hA_def]
      exact firstRCylinder_measurable_in_firstRSigma X r Cinit hCinit

    -- Measurability of B in σ(X r)
    have hB_meas_Xr : MeasurableSet[MeasurableSpace.comap (X r) inferInstance] B := by
      rw [hB_def]
      -- B = X r ⁻¹' Clast, which is measurable in σ(X r) by definition of comap
      exact ⟨Clast, hClast, rfl⟩

    -- Conditional independence from block_coord_condIndep
    have h_condIndep : ProbabilityTheory.CondIndep
        (futureFiltration X m)
        (firstRSigma X r)
        (MeasurableSpace.comap (X r) inferInstance)
        (futureFiltration_le X m hX_meas)
        μ := by
      exact block_coord_condIndep X hX hX_meas hrm

    -- Apply indicator factorization using the CI
    have hfactor :
        μ[(A.indicator (fun _ => (1:ℝ))) * (B.indicator (fun _ => (1:ℝ))) | futureFiltration X m]
          =ᵐ[μ]
        (fun ω => (μ[A.indicator (fun _ => (1:ℝ)) | futureFiltration X m] ω)
                  * (μ[B.indicator (fun _ => (1:ℝ)) | futureFiltration X m] ω)) := by
      -- Convert product of indicators to indicator of intersection
      have h_inter : (A.indicator (fun _ => (1:ℝ))) * (B.indicator (fun _ => (1:ℝ)))
                   = (A ∩ B).indicator (fun _ => (1:ℝ)) := by
        ext ω
        simp only [Pi.mul_apply]
        have := congr_fun (indicator_mul_indicator_eq_indicator_inter A B 1 1) ω
        simpa using this
      -- Apply standard CI product formula
      calc μ[(A.indicator (fun _ => (1:ℝ))) * (B.indicator (fun _ => (1:ℝ))) | futureFiltration X m]
          _ =ᵐ[μ] μ[(A ∩ B).indicator (fun _ => (1:ℝ)) | futureFiltration X m] := by
            exact condExp_congr_ae (EventuallyEq.of_eq h_inter)
          _ =ᵐ[μ] (μ[A.indicator (fun _ => (1:ℝ)) | futureFiltration X m] *
                   μ[B.indicator (fun _ => (1:ℝ)) | futureFiltration X m]) := by
            exact condexp_indicator_inter_of_condIndep
              (futureFiltration_le X m hX_meas)
              (firstRSigma_le_ambient X r hX_meas)
              (fun s hs => by obtain ⟨t, ht, rfl⟩ := hs; exact (hX_meas r) ht)
              h_condIndep
              hA_meas_firstR
              hB_meas_Xr

    -- Apply IH to the first r factors
    have hIH : μ[indProd X r Cinit | futureFiltration X m] =ᵐ[μ]
        (fun ω => ∏ i : Fin r,
          μ[Set.indicator (Cinit i) (fun _ => (1:ℝ)) ∘ (X 0) | futureFiltration X m] ω) := by
      exact ih Cinit hCinit (Nat.le_of_succ_le hm)

    -- Replace Xᵣ with X₀ using contractability
    have hswap : μ[(Set.indicator Clast (fun _ => (1:ℝ)) ∘ X r) | futureFiltration X m]
        =ᵐ[μ]
        μ[(Set.indicator Clast (fun _ => (1:ℝ)) ∘ X 0) | futureFiltration X m] := by
      -- condexp_convergence swaps X_m with X_k, so swap X_m with X_r, then with X_0
      have h1 := condexp_convergence hX hX_meas r m (Nat.le_of_lt hrm) Clast hClast
      have h2 := condexp_convergence hX hX_meas 0 m (Nat.zero_le m) Clast hClast
      exact h1.symm.trans h2

    -- Combine everything
    calc μ[indProd X (r+1) C | futureFiltration X m]
        _ =ᵐ[μ] μ[(fun ω => indProd X r Cinit ω
                      * Set.indicator Clast (fun _ => (1:ℝ)) (X r ω))
                   | futureFiltration X m] := by
          refine condExp_congr_ae (EventuallyEq.of_eq hsplit)
        _ =ᵐ[μ] μ[(A.indicator (fun _ => (1:ℝ)))
                   * (B.indicator (fun _ => (1:ℝ)))
                   | futureFiltration X m] := by
          refine condExp_congr_ae (EventuallyEq.of_eq ?_)
          funext ω
          rw [← hf_indicator, ← hg_indicator]
          rfl
        _ =ᵐ[μ] (fun ω => (μ[A.indicator (fun _ => (1:ℝ)) | futureFiltration X m] ω)
                          * (μ[B.indicator (fun _ => (1:ℝ)) | futureFiltration X m] ω)) := hfactor
        _ =ᵐ[μ] (fun ω => (μ[indProd X r Cinit | futureFiltration X m] ω)
                          * (μ[Set.indicator Clast (fun _ => (1:ℝ)) ∘ X r | futureFiltration X m] ω)) := by
          apply EventuallyEq.mul
          · refine condExp_congr_ae (EventuallyEq.of_eq hf_indicator.symm)
          · refine condExp_congr_ae (EventuallyEq.of_eq hg_indicator.symm)
        _ =ᵐ[μ] (fun ω => (∏ i : Fin r,
                            μ[Set.indicator (Cinit i) (fun _ => (1:ℝ)) ∘ (X 0)
                              | futureFiltration X m] ω)
                          * (μ[Set.indicator Clast (fun _ => (1:ℝ)) ∘ X r | futureFiltration X m] ω)) := by
          apply EventuallyEq.mul hIH
          exact EventuallyEq.rfl
        _ =ᵐ[μ] (fun ω => (∏ i : Fin r,
                            μ[Set.indicator (Cinit i) (fun _ => (1:ℝ)) ∘ (X 0)
                              | futureFiltration X m] ω)
                          * μ[Set.indicator Clast (fun _ => (1:ℝ)) ∘ (X 0)
                              | futureFiltration X m] ω) := by
          apply EventuallyEq.mul EventuallyEq.rfl
          exact hswap
        _ =ᵐ[μ] (fun ω => ∏ i : Fin (r+1),
                            μ[Set.indicator (C i) (fun _ => (1:ℝ)) ∘ (X 0)
                              | futureFiltration X m] ω) := by
          apply EventuallyEq.of_eq
          funext ω
          -- Reverse of hsplit: combine products using Fin.prod_univ_castSucc
          symm
          rw [Fin.prod_univ_castSucc]
          simp only [Cinit, Clast, Fin.last]

/-- **Tail factorization on finite cylinders (formerly Axiom 4).**

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
lemma tail_factorization_from_future
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
        μ[Set.indicator (C i) (fun _ => (1 : ℝ)) ∘ (X 0) | tailSigma X] ω) := by
  classical
  -- Strategy: Use reverse martingale convergence for the LHS
  -- The future filtration decreases to the tail σ-algebra, so reverse martingale
  -- convergence gives: μ[f | futureFiltration X m] → μ[f | tailSigma X] ae
  
  -- LHS reverse martingale convergence for the product
  have h_lhs_conv : ∀ᵐ ω ∂μ,
      Tendsto (fun m => μ[indProd X r C | futureFiltration X m] ω)
              atTop
              (𝓝 (μ[indProd X r C | tailSigma X] ω)) := by
    -- Apply reverse martingale convergence (from mathlib or Martingale.lean)
    -- tailSigma X = ⨅ m, futureFiltration X m
    sorry  -- TODO: Apply condexp_tendsto_tail or similar
  
  -- RHS convergence: product of convergent sequences
  have h_rhs_conv : ∀ᵐ ω ∂μ,
      Tendsto (fun m => ∏ i : Fin r,
                  μ[Set.indicator (C i) (fun _ => (1 : ℝ)) ∘ (X 0) | futureFiltration X m] ω)
              atTop
              (𝓝 (∏ i : Fin r,
                  μ[Set.indicator (C i) (fun _ => (1 : ℝ)) ∘ (X 0) | tailSigma X] ω)) := by
    -- Product of tendsto gives tendsto of product (finitely many factors)
    have h_ae := ae_all_iff.mpr h_rev
    filter_upwards [h_ae] with ω hω
    exact tendsto_finset_prod _ (fun i _ => hω i)
  
  -- Both LHS and RHS converge, and they're equal at each finite level for large m
  -- Therefore their limits are equal
  have h_eq_ae : ∀ᵐ ω ∂μ,
      μ[indProd X r C | tailSigma X] ω
        = (∏ i : Fin r,
            μ[Set.indicator (C i) (fun _ => (1 : ℝ)) ∘ (X 0) | tailSigma X] ω) := by
    -- Combine the three ae sets
    have h_fact_large : ∀ᵐ ω ∂μ, ∀ m ≥ r,
        μ[indProd X r C | futureFiltration X m] ω
          = (∏ i : Fin r,
              μ[Set.indicator (C i) (fun _ => (1 : ℝ)) ∘ (X 0) | futureFiltration X m] ω) := by
      -- Convert the ae hypothesis h_fact to a pointwise statement
      sorry  -- TODO: Use ae_all_iff or similar to convert sequence of ae to ae sequence
    
    filter_upwards [h_lhs_conv, h_rhs_conv, h_fact_large] with ω hlhs hrhs hfact
    -- At ω, both sequences converge and are eventually equal, so limits are equal
    exact tendsto_nhds_unique hlhs (hrhs.congr' (eventually_atTop.mpr ⟨r, hfact⟩))
  
  exact h_eq_ae

/-! ### Directing measure construction

From conditional expectations on indicators, we need to build a measurable family
of probability measures `ν : Ω → Measure α`.

The construction uses the standard Borel machinery: for each `ω`, define
`ν ω` to be the unique probability measure satisfying
`ν ω B = E[1_{X₀∈B} | 𝒯_X](ω)` for all measurable `B`.

This requires StandardBorelSpace assumption on α to ensure existence.
-/

/-- Construction of the directing measure from conditional expectations (formerly Axiom 5).
For each `ω : Ω`, `ν ω` is the conditional distribution of `X₀` given the tail σ-algebra.

This uses mathlib's `condExpKernel` to construct a regular conditional probability kernel.
The kernel `condExpKernel μ (tailSigma X)` gives the conditional distribution on the entire
path space; composing with the projection `X 0` gives the desired marginal on α. -/
noncomputable def directingMeasure_of_contractable
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {α : Type*} [MeasurableSpace α] [StandardBorelSpace α] [Nonempty α]
    (X : ℕ → Ω → α)
    (hX_meas : ∀ n, Measurable (X n)) :
    { ν : Ω → Measure α //
      (∀ ω, IsProbabilityMeasure (ν ω)) ∧
      (∀ B : Set α, MeasurableSet B →
        (fun ω => (ν ω B).toReal) =ᵐ[μ] μ[Set.indicator B (fun _ => (1 : ℝ)) ∘ (X 0) | tailSigma X]) ∧
      (∀ B : Set α, MeasurableSet B → Measurable (fun ω => ν ω B)) } := by
  classical
  -- **Construction strategy:**
  -- 1. Use condExpKernel μ (tailSigma X) to get a kernel κ : Ω → Measure Ω
  -- 2. Define ν ω := (κ ω).map (X 0) (pushforward along X 0)
  -- 3. Prove probability: κ ω is a probability measure, X 0 is measurable
  -- 4. Prove CE property: Use condExp_ae_eq_integral_condExpKernel and integral_map
  -- 5. Prove measurability: Use Kernel.measurable_coe composed with map
  
  -- Need StandardBorelSpace Ω for condExpKernel to exist
  -- This should be added as a hypothesis or derived from StandardBorelSpace α
  sorry  -- TODO: Complete kernel construction using ProbabilityTheory.condExpKernel

/-! ### Conditional law equality -/

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

/-! ### Finite-dimensional product formula -/

/-- Finite-dimensional product formula for conditionally i.i.d. sequences (formerly Axiom 6).

**Proof strategy:**
1. Use `finite_level_factorization` to get factorization at future levels
2. Apply `tail_factorization_from_future` with reverse martingale convergence
   (`condexp_tendsto_tail`) to lift to the tail σ-algebra
3. Use identical conditional laws (from `conditional_law_eq_directingMeasure`)
   to replace each `Xᵢ` with `X₀` in the product
4. Extend from rectangles to all measurable sets via π-system/monotone class
   (rectangles generate the product σ-algebra)

This is the key step that assembles all the machinery. -/
lemma finite_product_formula
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
      = μ.bind (fun ω => Measure.pi fun _ : Fin m => ν ω) := by
  classical
  -- **Proof outline:**
  -- 
  -- **Step 1:** Prove for rectangles using the factorization machinery
  -- For measurable sets C : Fin m → Set α, prove:
  --   μ {ω | ∀ i, X (k i) ω ∈ C i} = ∫ ω, ∏ i, (ν ω) (C i) ∂μ
  --
  -- Sub-steps:
  -- a) Apply finite_level_factorization at sufficiently large future level
  -- b) Apply tail_factorization_from_future with reverse martingale convergence
  -- c) Use tower property: integrate both sides to get the measure equality
  -- d) Use hν_law to replace CE[1_{X_n ∈ C}|tail] with (ν ω) C
  --
  -- **Step 2:** Extend from rectangles to full σ-algebra
  -- Use π-λ theorem (monotone class): rectangles form a π-system that generates
  -- the product σ-algebra, and equality of measures on a generating π-system
  -- implies equality of measures.
  
  sorry  -- TODO: Apply finite_level_factorization + tail_factorization_from_future + π-λ theorem

/-!
## Notes

The main de Finetti theorem using this machinery is in `TheoremViaMartingale.lean`.
This file provides the proof infrastructure (helper lemmas and constructions).
-/

end ViaMartingale
end DeFinetti
end Exchangeability
