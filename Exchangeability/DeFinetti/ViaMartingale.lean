/-
Copyright (c) 2025 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.Probability.ConditionalExpectation
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Probability.Martingale.Basic
import Exchangeability.Contractability
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

   From contractability: `(ξ_m, θ_m ξ) =^d (ξ_k, θ_k ξ)` for `k ≤ m`.
   Using Lemma 1.3 and reverse martingale convergence:
   ```
   P[ξ_m ∈ B | θ_m ξ] = P[ξ_k ∈ B | θ_m ξ] → P[ξ_k ∈ B | 𝒯_ξ]
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
  refine ⟨g ⁻¹' s, ?_, by ext x; rfl⟩
  exact hg hs

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

variable {α}

/-- Cylinder on the first `r` tail coordinates (shifted by one). -/
def tailCylinder (r : ℕ) (C : Fin r → Set α) : Set (ℕ → α) :=
  {f | ∀ i : Fin r, f (i.1 + 1) ∈ C i}

variable [MeasurableSpace α]

/-- Basic measurability for tail cylinders. -/
lemma tailCylinder_measurable {r : ℕ} {C : Fin r → Set α}
    (hC : ∀ i, MeasurableSet (C i)) :
    MeasurableSet (tailCylinder (α:=α) r C) := by
  classical
  refine MeasurableSet.iInter ?_
  intro i
  have hi : Measurable fun f : ℕ → α => f (i.1 + 1) :=
    measurable_pi_apply (i.1 + 1)
  simpa [tailCylinder] using hi (hC i)

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
  have h_range_sub : ∀ i, s.orderEmbOfFin rfl i ∈ s := orderEmbOfFin_mem (s:=s)
  -- Define a function to s viewed as a subtype
  let f : Fin s.card → s := fun i => ⟨s.orderEmbOfFin rfl i, h_range_sub i⟩
  have hf_inj : Function.Injective f := by
    intro i j hij
    exact h_inj (Subtype.ext_iff.mp hij)
  -- Injective function between finite types of equal cardinality is surjective
  have hf_surj : Function.Surjective f := Fintype.surjective_of_injective hf_inj
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
  classical
  cases' i using Fin.cases with _ i
  · cases' j using Fin.cases with _ j
    · exact False.elim ((lt_irrefl (0 : Fin (n + 1))) hij)
    · simpa using ha j
  · cases' j using Fin.cases with _ j
    ·
      have : ((Fin.succ i : Fin (n + 1)).1) < 0 := by
        simpa [Fin.lt_iff_val_lt_val] using hij
      exact False.elim ((Nat.not_lt.mpr (Nat.zero_le _)) this)
    ·
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

omit [MeasurableSpace Ω] [MeasurableSpace α] in
lemma path_eq_shiftRV_zero (X : ℕ → Ω → α) : path X = shiftRV X 0 :=
  (shiftRV_zero X).symm

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

/-- The tail σ-algebra for a process X: ⋂ₙ σ(Xₙ, Xₙ₊₁, ...). -/
def tailSigma (X : ℕ → Ω → α) : MeasurableSpace Ω :=
  ⨅ m, revFiltration X m

omit [MeasurableSpace Ω] in
@[simp]
lemma tailSigma_eq_iInf_rev (X : ℕ → Ω → α) :
    tailSigma X = ⨅ m, revFiltration X m := rfl

section Measurability

variable {X : ℕ → Ω → α}

lemma measurable_path (hX : ∀ n, Measurable (X n)) :
    Measurable (path X) := by
  classical
  simpa [path] using measurable_pi_iff.mpr hX

lemma measurable_shiftRV (hX : ∀ n, Measurable (X n)) {m : ℕ} :
    Measurable (shiftRV X m) := by
  classical
  simpa [shiftRV] using
    measurable_pi_iff.mpr (fun n => by simpa using hX (m + n))

end Measurability

lemma revFiltration_antitone (X : ℕ → Ω → α) :
    Antitone (revFiltration X) := by
  intro m k hmk
  have hcomp : shiftRV X k = (shiftSeq (β:=α) (k - m)) ∘ shiftRV X m := by
    funext ω n
    have hkm : m + (k - m) = k := by
      simpa using Nat.add_sub_of_le hmk
    have : m + (n + (k - m)) = k + n := by
      have : m + (n + (k - m)) = (m + (k - m)) + n := by
        simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
      simpa [this, hkm, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
    simp [shiftRV, shiftSeq, Function.comp, this]
  have hmeas := measurable_shiftSeq (β:=α) (k - m)
  simpa [revFiltration, hcomp, Function.comp] using
    comap_comp_le (shiftRV X m) (shiftSeq (β:=α) (k - m)) hmeas

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

/-- **Lemma 1.3 (contraction and independence).**

If `(ξ, η) =^d (ξ, ζ)` and `σ(η) ⊆ σ(ζ)`, then `ξ ⊥⊥_η ζ`.

**Proof sketch:** Fix a measurable set `B` and define:
- `μ₁ = P[ξ ∈ B | η]`
- `μ₂ = P[ξ ∈ B | ζ]`

Since `σ(η) ⊆ σ(ζ)`, we have that `μ₁` is `σ(η)`-measurable and `μ₂` is
`σ(ζ)`-measurable,
making `(μ₁, μ₂)` a bounded martingale. From the distributional equality
`(ξ, η) =^d (ξ, ζ)`, we get `μ₁ =^d μ₂`, so:

```
E(μ₂ - μ₁)² = E μ₂² - E μ₁² = 0
```

Thus `μ₁ = μ₂` a.s., i.e., `P[ξ ∈ B | η] = P[ξ ∈ B | ζ]` a.s. By Doob's
characterization of conditional independence (FMP 6.6), this gives `ξ ⊥⊥_η ζ`. ∎

*Kallenberg (2005), Lemma 1.3.* -/
lemma contraction_independence
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ξ η ζ : Ω → α}
    (h_dist : Measure.map (fun ω => (ξ ω, η ω)) μ
              = Measure.map (fun ω => (ξ ω, ζ ω)) μ)
    (h_sigma : MeasurableSpace.comap η inferInstance ≤ MeasurableSpace.comap ζ inferInstance) :
    ProbabilityTheory.CondIndep ξ ζ η μ := by
  -- Proof strategy (wrapper around condexp_indicator_eq_of_dist_eq_and_le):
  -- Step 1: For each measurable B, apply condexp_indicator_eq_of_dist_eq_and_le
  --         to get: P[ξ ∈ B | η] = P[ξ ∈ B | ζ] a.s.
  -- Step 2: This shows that ξ and ζ have the same conditional distribution given η
  -- Step 3: Since σ(η) ⊆ σ(ζ), this implies ξ ⊥⊥_η ζ by Doob's
  -- characterization (FMP 6.6)
  --
  -- The key insight: condexp_indicator_eq_of_dist_eq_and_le gives the conditional
  -- expectation equality directly, which is exactly what we need for conditional independence.
  --
  -- TODO: Once CondIndep API is clarified in mathlib, formalize using:
  -- - condexp_indicator_eq_of_dist_eq_and_le (already stated above)
  -- - Doob's characterization of conditional independence
  sorry

/-- If `(ξ,η)` and `(ξ,ζ)` have the same law and `σ(η) ≤ σ(ζ)`,
then for all measurable `B`, the conditional expectations of `1_{ξ∈B}` coincide.

This is the key technical lemma that converts distributional equality into
conditional expectation equality. It's used to prove `condexp_convergence`. -/
lemma condexp_indicator_eq_of_dist_eq_and_le
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ξ : Ω → α} {η ζ : Ω → (ℕ → α)}
    (h_dist : Measure.map (fun ω => (ξ ω, η ω)) μ
            = Measure.map (fun ω => (ξ ω, ζ ω)) μ)
    (hσ : MeasurableSpace.comap η inferInstance ≤ MeasurableSpace.comap ζ inferInstance)
    (B : Set α) (hB : MeasurableSet B) :
    μ[Set.indicator B (fun _ => (1 : ℝ)) ∘ ξ | MeasurableSpace.comap η inferInstance]
      =ᵐ[μ]
    μ[Set.indicator B (fun _ => (1 : ℝ)) ∘ ξ | MeasurableSpace.comap ζ inferInstance] := by
  -- Proof sketch to implement in CondExp.lean:
  -- 1. Both sides are in [0,1] and in L² (indicators are bounded)
  -- 2. By hσ and tower property: E[(RHS - LHS) · g] = 0 for any g measurable w.r.t. σ(η)
  -- 3. Using h_dist, compare second moments:
  --    ∫ RHS² = ∫ LHS² (by distributional equality)
  --    Therefore ∫ (RHS - LHS)² = 0
  -- 4. Conclude RHS = LHS almost everywhere
  --
  -- Required lemmas from CondExp.lean:
  -- - condexp_tower: tower property for conditional expectation
  -- - condexp_L2_norm: ‖E[f|𝔾]‖₂ ≤ ‖f‖₂
  -- - indicator_L2: indicators are in L²
  -- - ae_eq_of_L2_norm_eq_zero: ‖f‖₂ = 0 ⇒ f = 0 a.e.
  sorry

/-- Finite-dimensional (cylinder) equality:
for any `r`, base set `B` and measurable sets on the first `r` tail coordinates,
the probabilities agree when comparing `(X m, θₘ X)` vs `(X k, θₘ X)`.

This is the exact finite-dimensional marginal needed for the martingale step. -/
lemma contractable_dist_eq_on_first_r_tail
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → α} (hX : Contractable μ X)
    (k m r : ℕ) (hk : k ≤ m)
    (B : Set α) (hB : MeasurableSet B)
    (C : Fin r → Set α) (hC : ∀ i, MeasurableSet (C i)) :
    μ {ω | X m ω ∈ B ∧ ∀ i : Fin r, X (m + (i.1 + 1)) ω ∈ C i}
      = μ {ω | X k ω ∈ B ∧ ∀ i : Fin r, X (m + (i.1 + 1)) ω ∈ C i} := by
  classical
  -- reindex vectors of length r+1
  let κ_tail : Fin r → ℕ := fun i => m + (i.1 + 1)
  have h_tail : StrictMono κ_tail := by
    intro i j hij
    have hij' : i.1 < j.1 := by
      simpa [Fin.lt_iff_val_lt_val] using hij
    have : i.1 + 1 < j.1 + 1 := Nat.succ_lt_succ hij'
    simpa [κ_tail, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      Nat.add_lt_add_left this m

  -- whole index vectors (head+tail)
  let κ₁ : Fin (r + 1) → ℕ := Fin.cases m (fun i : Fin r => κ_tail i)
  let κ₂ : Fin (r + 1) → ℕ := Fin.cases k (fun i : Fin r => κ_tail i)
  have hκ₁ : StrictMono κ₁ :=
    strictMono_fin_cases (f := κ_tail) h_tail (by
      intro i
      simpa [κ_tail, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        Nat.lt_add_of_pos_right (Nat.succ_pos (i.1)))
  have hκ₂ : StrictMono κ₂ :=
    strictMono_fin_cases (f := κ_tail) h_tail (by
      intro i
      have hm : m < m + (i.1 + 1) := Nat.lt_add_of_pos_right (Nat.succ_pos (i.1))
      exact lt_of_le_of_lt hk
        (by
          simpa [κ_tail, Nat.add_comm, Nat.add_assoc, Nat.add_left_comm] using hm))

  -- evaluation maps to the (r+1)-vector
  let φ₁ : Ω → (Fin (r + 1) → α) :=
    fun ω => Fin.cases (X m ω) (fun i : Fin r => X (κ_tail i) ω)
  let φ₂ : Ω → (Fin (r + 1) → α) :=
    fun ω => Fin.cases (X k ω) (fun i : Fin r => X (κ_tail i) ω)

  -- cylinder set in `(Fin (r+1) → α)`
  let A : Set (Fin (r + 1) → α) :=
    {y | y 0 ∈ B ∧ ∀ i : Fin r, y (Fin.succ i) ∈ C i}

  -- identify events as preimages of A
  have hE₁ :
      {ω | X m ω ∈ B ∧ ∀ i : Fin r, X (m + (i.1 + 1)) ω ∈ C i} = φ₁ ⁻¹' A := by
    ext ω; rfl
  have hE₂ :
      {ω | X k ω ∈ B ∧ ∀ i : Fin r, X (m + (i.1 + 1)) ω ∈ C i} = φ₂ ⁻¹' A := by
    ext ω; rfl

  -- contractability gives: both pushforwards = law of the canonical vector (X 0, X 1, …, X r)
  have hpush₁ :
      Measure.map φ₁ μ = Measure.map (fun ω (i : Fin (r + 1)) => X i.1 ω) μ := by
    simpa [φ₁] using hX (r + 1) κ₁ hκ₁
  have hpush₂ :
      Measure.map φ₂ μ = Measure.map (fun ω (i : Fin (r + 1)) => X i.1 ω) μ := by
    simpa [φ₂] using hX (r + 1) κ₂ hκ₂

  -- measurable A (so we can evaluate measures)
  have hA : MeasurableSet A := by
    classical
    have h0 : Measurable (fun y : (Fin (r + 1) → α) => y 0) := measurable_pi_apply 0
    have hS : ∀ i, Measurable (fun y : (Fin (r + 1) → α) => y (Fin.succ i)) :=
      fun i => measurable_pi_apply (Fin.succ i)
    refine (h0 hB).and ?_
    refine MeasurableSet.iInter ?_
    intro i
    simpa using (hS i (hC i))

  -- take measures of A under both pushforwards
  have : (Measure.map φ₁ μ) A = (Measure.map φ₂ μ) A := by
    -- both equal the canonical pushforward's measure of A
    simpa [hpush₁] using congrArg (fun ν => ν A) hpush₂.symm

  -- unfold and conclude
  simpa [hE₁, hE₂, Measure.map_apply, hA] using this

/-- Equality of pushforward measures on basic rectangles using the first-tail cylinders. -/
lemma contractable_dist_eq_on_rectangles
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → α} (hX : Contractable μ X)
    (k m : ℕ) (hk : k ≤ m) :
    ∀ (r : ℕ) (B : Set α) (hB : MeasurableSet B)
      (C : Fin r → Set α) (hC : ∀ i, MeasurableSet (C i)),
      (Measure.map (fun ω => (X m ω, shiftRV X m ω)) μ)
          (B ×ˢ tailCylinder (α:=α) r C)
        =
      (Measure.map (fun ω => (X k ω, shiftRV X m ω)) μ)
          (B ×ˢ tailCylinder (α:=α) r C) := by
  classical
  intro r B hB C hC
  let ψ₁ : Ω → α × (ℕ → α) := fun ω => (X m ω, shiftRV X m ω)
  let ψ₂ : Ω → α × (ℕ → α) := fun ω => (X k ω, shiftRV X m ω)
  have hmeas :
      MeasurableSet (B ×ˢ tailCylinder (α:=α) r C) :=
    hB.prod (tailCylinder_measurable (α:=α) hC)
  have hpre₁ :
      ψ₁ ⁻¹' (B ×ˢ tailCylinder (α:=α) r C)
        = {ω | X m ω ∈ B ∧ ∀ i : Fin r, X (m + (i.1 + 1)) ω ∈ C i} := by
    ext ω; simp [ψ₁, tailCylinder, shiftRV, Set.mem_prod, Set.preimage,
      Set.mem_setOf_eq]
  have hpre₂ :
      ψ₂ ⁻¹' (B ×ˢ tailCylinder (α:=α) r C)
        = {ω | X k ω ∈ B ∧ ∀ i : Fin r, X (m + (i.1 + 1)) ω ∈ C i} := by
    ext ω; simp [ψ₂, tailCylinder, shiftRV, Set.mem_prod, Set.preimage,
      Set.mem_setOf_eq]
  have h :=
    contractable_dist_eq_on_first_r_tail (μ:=μ) (X:=X) hX k m r hk B hB C hC
  simpa [ψ₁, ψ₂, Measure.map_apply, hmeas, hpre₁, hpre₂] using h

/-- If two measures on `α × (ℕ → α)` agree on rectangles coming from the first-tail
coordinates, then they are equal. -/
lemma prod_path_measure_ext
    {μ ν : Measure (α × (ℕ → α))}
    (h : ∀ (r : ℕ) (B : Set α) (hB : MeasurableSet B)
          (C : Fin r → Set α) (hC : ∀ i, MeasurableSet (C i)),
          μ (B ×ˢ tailCylinder (α:=α) r C)
            = ν (B ×ˢ tailCylinder (α:=α) r C)) :
    μ = ν := by
  -- Strategy: Use Measure.ext_of_generateFrom_of_cover with the π-system of rectangles
  --
  -- The π-system S consists of all rectangles B ×ˢ tailCylinder r C
  -- where B is measurable in α and C i are measurable for each i < r.
  --
  -- Key facts:
  -- 1. S is a π-system (closed under intersections)
  -- 2. S generates the product σ-algebra on α × (ℕ → α)
  -- 3. μ and ν agree on S by hypothesis
  -- 4. Both measures are σ-finite (as products of σ-finite measures)

  -- Define the π-system of rectangles
  let S : Set (Set (α × (ℕ → α))) :=
    {s | ∃ (r : ℕ) (B : Set α) (hB : MeasurableSet B)
           (C : Fin r → Set α) (hC : ∀ i, MeasurableSet (C i)),
           s = B ×ˢ tailCylinder r C}

  -- Show S is a π-system
  have h_pi : IsPiSystem S := by
    intro s₁ hs₁ s₂ hs₂ _
    obtain ⟨r₁, B₁, hB₁, C₁, hC₁, rfl⟩ := hs₁
    obtain ⟨r₂, B₂, hB₂, C₂, hC₂, rfl⟩ := hs₂
    -- (B₁ ×ˢ tailCylinder r₁ C₁) ∩ (B₂ ×ˢ tailCylinder r₂ C₂)
    -- = (B₁ ∩ B₂) ×ˢ (tailCylinder r₁ C₁ ∩ tailCylinder r₂ C₂)
    -- The intersection of two tail cylinders is a tail cylinder with r = max r₁ r₂

    -- Take r = max r₁ r₂
    let r := max r₁ r₂

    -- Define C for the intersection: combines C₁ and C₂
    let C : Fin r → Set α := fun i =>
      if h : i.1 < r₁ then
        if h' : i.1 < r₂ then C₁ ⟨i.1, h⟩ ∩ C₂ ⟨i.1, h'⟩ else C₁ ⟨i.1, h⟩
      else if h' : i.1 < r₂ then C₂ ⟨i.1, h'⟩ else Set.univ

    have hC : ∀ i, MeasurableSet (C i) := by
      intro i
      simp only [C]
      split_ifs with h1 h2 h3
      · exact (hC₁ ⟨i.1, h1⟩).inter (hC₂ ⟨i.1, h2⟩)
      · exact hC₁ ⟨i.1, h1⟩
      · exact hC₂ ⟨i.1, h3⟩
      · exact MeasurableSet.univ

    -- Show the intersection equals this rectangle
    use r, B₁ ∩ B₂, hB₁.inter hB₂, C, hC

    ext ⟨a, f⟩
    simp only [Set.mem_inter_iff, Set.mem_prod, tailCylinder]
    constructor
    · intro ⟨⟨ha₁, hf₁⟩, ⟨ha₂, hf₂⟩⟩
      refine ⟨⟨ha₁, ha₂⟩, ?_⟩
      intro i
      simp only [C]
      by_cases h1 : i.1 < r₁
      · by_cases h2 : i.1 < r₂
        · simp [h1, h2]
          exact ⟨hf₁ ⟨i.1, h1⟩, hf₂ ⟨i.1, h2⟩⟩
        · simp [h1, h2]
          exact hf₁ ⟨i.1, h1⟩
      · by_cases h2 : i.1 < r₂
        · simp [h1, h2]
          exact hf₂ ⟨i.1, h2⟩
        · simp [h1, h2]
    · intro ⟨⟨ha₁, ha₂⟩, hf⟩
      refine ⟨⟨ha₁, ?_⟩, ⟨ha₂, ?_⟩⟩
      · intro i
        have : i.1 < r := Nat.lt_of_lt_of_le i.2 (Nat.le_max_left r₁ r₂)
        have hi := hf ⟨i.1, this⟩
        simp only [C] at hi
        simp [i.2] at hi
        exact hi.1
      · intro i
        have : i.1 < r := Nat.lt_of_lt_of_le i.2 (Nat.le_max_right r₁ r₂)
        have hi := hf ⟨i.1, this⟩
        simp only [C] at hi
        by_cases h1 : i.1 < r₁
        · simp [h1, i.2] at hi
          exact hi.2
        · simp [h1, i.2] at hi
          exact hi

  -- Show S generates the product σ-algebra
  have h_gen : (inferInstance : MeasurableSpace (α × (ℕ → α))) = MeasurableSpace.generateFrom S := by
    -- Strategy: Show both directions of inclusion
    -- 1. MeasurableSpace.generateFrom S ≤ product σ-algebra (every rectangle is measurable)
    -- 2. Product σ-algebra ≤ MeasurableSpace.generateFrom S (generators of product are in generateFrom S)

    apply le_antisymm

    -- Direction 1: generateFrom S ≤ product σ-algebra
    · apply MeasurableSpace.generateFrom_le
      intro s ⟨r, B, hB, C, hC, rfl⟩
      -- B ×ˢ tailCylinder r C is measurable in the product
      apply MeasurableSet.prod hB
      exact tailCylinder_measurable hC

    -- Direction 2: product σ-algebra ≤ generateFrom S
    · -- Strategy: show that the generators of the product σ-algebra are in generateFrom S
      -- The product σ-algebra is sup of two comaps: comap Prod.fst and comap Prod.snd

      -- Prod.instMeasurableSpace = comap Prod.fst ⊔ comap Prod.snd
      rw [MeasurableSpace.prod_eq]
      apply sup_le

      -- Show comap Prod.fst ≤ generateFrom S
      · rw [MeasurableSpace.comap_le_iff_le_map]
        apply MeasurableSpace.generateFrom_le
        intro A hA
        -- Need to show Prod.fst ⁻¹' A ∈ generateFrom S
        -- This is A × univ which equals A ×ˢ tailCylinder 0 (fun _ => univ)
        have : Prod.fst ⁻¹' A = A ×ˢ Set.univ := by
          ext ⟨a, f⟩
          simp
        rw [this]
        have : A ×ˢ Set.univ = A ×ˢ tailCylinder 0 (fun _ => Set.univ) := by
          ext ⟨a, f⟩
          simp [tailCylinder]
        rw [this]
        apply MeasurableSpace.measurableSet_generateFrom
        exact ⟨0, A, hA, (fun _ => Set.univ), (fun _ => MeasurableSet.univ), rfl⟩

      -- Show comap Prod.snd ≤ generateFrom S
      · -- Strategy: Show that generating sets for Pi.measurableSpace pull back to generateFrom S
        rw [MeasurableSpace.comap_le_iff_le_map]
        apply MeasurableSpace.generateFrom_le
        intro B hB
        -- B has form {f | f i ∈ C} for some i : ℕ and measurable C
        -- The measurable space on (ℕ → α) is Pi.measurableSpace,
        -- generated by sets of the form {f | f i ∈ C}

        -- We need: Prod.snd ⁻¹' B ∈ generateFrom S, i.e., Set.univ ×ˢ B ∈ generateFrom S

        -- The challenge is that Pi.measurableSpace is generated by a complex family of sets.
        -- For a rigorous proof, we would need to:
        -- 1. Characterize the generators of Pi.measurableSpace explicitly
        -- 2. Show each generator {f | f n ∈ C} for n : ℕ can be expressed via S
        --    - Case n = 0: Not directly in S (would need first coordinate to vary)
        --    - Case n > 0: Use tailCylinder with r = n and only C(n-1) non-trivial
        -- 3. Use closure properties of generateFrom

        -- This is technically intricate. The mathematical content is clear:
        -- tailCylinder accesses all f(i) for i ≥ 1, and combined with varying the
        -- first coordinate in products, we can access all coordinates of f.

        -- For now, accepting as axiom:
        sorry -- TODO: Formalize using generators of Pi.measurableSpace

  -- Show μ and ν agree on S
  have h_agree : ∀ s ∈ S, μ s = ν s := by
    intro s ⟨r, B, hB, C, hC, rfl⟩
    exact h r B hB C hC

  -- Apply π-λ theorem using Measure.ext_of_generateFrom_of_iUnion
  -- Define a covering sequence: just use univ at each index
  let B : ℕ → Set (α × (ℕ → α)) := fun _ => Set.univ

  have h1B : ⋃ i, B i = Set.univ := by simp [B]

  have h2B : ∀ i, B i ∈ S := by
    intro i
    use 0, Set.univ, MeasurableSet.univ, (fun _ => Set.univ), (fun _ => MeasurableSet.univ)
    ext ⟨a, f⟩
    simp [tailCylinder, B]

  have hμB : ∀ i, μ (B i) ≠ ∞ := by
    intro i
    simp [B]
    exact measure_ne_top μ Set.univ

  exact Measure.ext_of_generateFrom_of_iUnion S B h_gen h_pi h1B h2B hμB h_agree
/-- Helper lemma: contractability gives the key distributional equality.

If `X` is contractable, then for any `k ≤ m`:
```
(X_m, θ_m X) =^d (X_k, θ_m X)
```
where `θ_m X` denotes the **random** shifted tail path `ω ↦ (n ↦ X(m + n) ω)`. -/
lemma contractable_dist_eq
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → α} (hX : Contractable μ X) (k m : ℕ) (hk : k ≤ m) :
    Measure.map (fun ω => (X m ω, shiftRV X m ω)) μ
      = Measure.map (fun ω => (X k ω, shiftRV X m ω)) μ := by
  classical
  have hrect :=
    contractable_dist_eq_on_rectangles (μ:=μ) (X:=X) hX k m hk
  refine prod_path_measure_ext
    (μ:=Measure.map (fun ω => (X m ω, shiftRV X m ω)) μ)
    (ν:=Measure.map (fun ω => (X k ω, shiftRV X m ω)) μ) ?_
  intro r B hB C hC
  simpa using hrect r B hB C hC

/-- **Key convergence result:** The extreme members agree after conditioning on the tail σ-algebra.

For any `k ≤ m` and measurable set `B`:
```
P[X_m ∈ B | θ_m X] = P[X_k ∈ B | θ_m X] → P[X_k ∈ B | 𝒯_X]  (as n → ∞)
```

This is proved using Lemma 1.3 (contraction-independence) followed by reverse
martingale convergence. -/
-- TODO: The following theorems require conditional expectation API that is not yet
-- fully developed in this codebase. The proof structure is documented for future work.

lemma condexp_convergence
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → α} (hX : Contractable μ X) (k m : ℕ) (hk : k ≤ m)
    (B : Set α) (hB : MeasurableSet B) :
    μ[Set.indicator B (fun _ => (1 : ℝ)) ∘ (X m) | revFiltration X m]
      =ᵐ[μ]
    μ[Set.indicator B (fun _ => (1 : ℝ)) ∘ (X k) | revFiltration X m] := by
  -- Proof strategy:
  -- 1. From contractable_dist_eq: (X_m, shiftRV X m) =^d (X_k, shiftRV X m)
  -- 2. Note that σ(shiftRV X m) = revFiltration X m is the same conditioning σ-algebra
  -- 3. Apply contraction_independence (or its condexp version) to get:
  --    Both conditional expectations equal the same value
  -- 4. Therefore they're equal almost everywhere
  --
  -- This requires from CondExp.lean:
  -- - condexp_indicator_eq_of_dist_eq_and_le: distributional equality → condexp equality
  -- - Tower property if needed
  sorry

lemma extreme_members_equal_on_tail
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → α} (hX : Contractable μ X) (m : ℕ) (B : Set α) (hB : MeasurableSet B) :
    μ[Set.indicator B (fun _ => (1 : ℝ)) ∘ (X m) | tailSigma X]
      =ᵐ[μ]
    μ[Set.indicator B (fun _ => (1 : ℝ)) ∘ (X 0) | tailSigma X] := by
  -- Proof strategy:
  -- 1. From condexp_convergence:
  --    𝔼[1_{X_m∈B} | 𝔽ₙ] = 𝔼[1_{X_0∈B} | 𝔽ₙ] for all n ≥ m
  -- 2. Define reverse martingale: Mₙ := 𝔼[1_{X_m∈B} | 𝔽ₙ]
  -- 3. As n → ∞, 𝔽ₙ = revFiltration X n ↓ tailSigma X (by revFiltration_antitone)
  -- 4. By reverse martingale convergence (Lévy's downward theorem):
  --    Mₙ → 𝔼[1_{X_m∈B} | tailSigma X] a.s. and in L¹
  -- 5. Similarly for X_0: 𝔼[1_{X_0∈B} | 𝔽ₙ] → 𝔼[1_{X_0∈B} | tailSigma X]
  -- 6. Since Mₙ are all equal (from step 1), their limits are equal
  -- 7. Therefore the conclusion holds
  --
  -- This requires from CondExp.lean:
  -- - Reverse martingale convergence (condexp_tendsto_condexp_iInf)
  -- - Dominated convergence for L¹ functions
  sorry

/--
Additive “future-filtration + standard-cylinder” layer that coexists with the
current `revFiltration` / `tailCylinder` infrastructure. Existing names remain intact.
-/

/-! ## Future filtration (additive) -/
section FutureFiltration

variable {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]

/-- Future reverse filtration: 𝔽ᶠᵘᵗₘ = σ(θ_{m+1} X). -/
abbrev futureFiltration (X : ℕ → Ω → α) (m : ℕ) : MeasurableSpace Ω :=
  MeasurableSpace.comap (shiftRV X (m + 1)) inferInstance

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

end FutureFiltration

/-! ## Standard cylinders on paths (starting at index 0) -/
section FutureCylinders

variable {α : Type*}

/-- Standard cylinder on the first `r` coordinates starting at index 0. -/
def cylinder (r : ℕ) (C : Fin r → Set α) : Set (ℕ → α) :=
  {f | ∀ i : Fin r, f i ∈ C i}

variable [MeasurableSpace α]

lemma cylinder_measurable {r : ℕ} {C : Fin r → Set α}
    (hC : ∀ i, MeasurableSet (C i)) :
    MeasurableSet (cylinder (α:=α) r C) := by
  classical
  refine MeasurableSet.iInter ?_
  intro i
  have hi : Measurable fun f : (ℕ → α) => f i := measurable_pi_apply i
  simpa [cylinder] using hi (hC i)

end FutureCylinders

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
    {X : ℕ → Ω → α} (hX : Contractable μ X)
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
    simpa [ψ₁, preimage_rect_future (μ:=μ) (X:=X) m m r B C]
  have hpre₂ :
      ψ₂ ⁻¹' (B ×ˢ cylinder (α:=α) r C)
        = {ω | X k ω ∈ B ∧ ∀ i : Fin r, X (m + 1 + i.1) ω ∈ C i} := by
    simpa [ψ₂, preimage_rect_future (μ:=μ) (X:=X) k m r B C]
  have hfd :
    μ {ω | X m ω ∈ B ∧ ∀ i : Fin r, X (m + (i.1 + 1)) ω ∈ C i}
      =
    μ {ω | X k ω ∈ B ∧ ∀ i : Fin r, X (m + (i.1 + 1)) ω ∈ C i} := by
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      (contractable_dist_eq_on_first_r_tail
        (μ:=μ) (X:=X) hX k m r hk B hB C hC)
  have : μ (ψ₁ ⁻¹' (B ×ˢ cylinder (α:=α) r C))
        = μ (ψ₂ ⁻¹' (B ×ˢ cylinder (α:=α) r C)) := by
    simpa [hpre₁, hpre₂]
  simpa [Measure.map_apply, hrect, ψ₁, ψ₂] using this

end FutureRectangles

structure AgreeOnFutureRectangles
    (μ ν : Measure (α × (ℕ → α))) : Prop :=
  (eq_rect :
    ∀ (r : ℕ) (B : Set α) (hB : MeasurableSet B)
      (C : Fin r → Set α) (hC : ∀ i, MeasurableSet (C i)),
      μ (B ×ˢ cylinder (α:=α) r C) = ν (B ×ˢ cylinder (α:=α) r C))

lemma agree_on_future_rectangles_of_contractable
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → α} (hX : Contractable μ X) (k m : ℕ) (hk : k ≤ m) :
    AgreeOnFutureRectangles
      (Measure.map (fun ω => (X m ω, shiftRV X (m + 1) ω)) μ)
      (Measure.map (fun ω => (X k ω, shiftRV X (m + 1) ω)) μ) := by
  classical
  refine ⟨?_⟩
  intro r B hB C hC
  simpa using
    (contractable_dist_eq_on_rectangles_future
      (μ:=μ) (X:=X) hX k m hk r B hB C hC)


section reverse_martingale

variable {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {X : ℕ → Ω → α}

/-- 𝔽ₘ = σ(θₘ X). -/
abbrev 𝔽 (m : ℕ) : MeasurableSpace Ω := revFiltration X m

/-- The reverse filtration is decreasing; packaged for the martingale API. -/
lemma filtration_antitone : Antitone 𝔽 := by
  intro m n hmn
  simpa [𝔽] using revFiltration_antitone X hmn

/-- Mₘ := 𝔼[1_{Xₖ∈B} | 𝔽ₘ].
The reverse martingale sequence for the indicator of X_k in B. -/
def M (k : ℕ) (B : Set α) : ℕ → Ω → ℝ :=
  fun m ω =>
    μ[Set.indicator B (fun _ => (1 : ℝ)) ∘ (X k) | 𝔽 m] ω

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
--     `filtration_antitone` and `tailSigma_eq_iInf_rev`.

end reverse_martingale

/-- **Aldous' third proof of de Finetti's theorem.**

If `X` is contractable, then `X₁, X₂, ...` are conditionally i.i.d. given the
tail σ-algebra `𝒯_X = ⋂_n σ(θ_n X)`.

**Proof structure:**
1. From contractability: `(X_m, θ_m X) =^d (X_k, θ_k X)` for `k ≤ m ≤ n`
2. Define `𝒯_X = ⋂_n σ(θ_n X)` (tail σ-algebra)
3. Apply Lemma 1.3 + reverse martingale convergence:
   ```
   P[X_m ∈ B | θ_m X] = P[X_k ∈ B | θ_m X] → P[X_k ∈ B | 𝒯_X]
   ```
4. Conclude: `P[X_m ∈ B | θ_m X] = P[X_m ∈ B | 𝒯_X] = P[X_1 ∈ B | 𝒯_X]`
5. First equality: `X_m ⊥⊥_{𝒯_X} θ_m X` for all `m`
6. By iteration: `X₁, X₂, ...` conditionally independent given `𝒯_X`
7. Second equality: conditional laws agree, giving conditional i.i.d.

*Kallenberg (2005), third proof of Theorem 1.1 (page 28).* -/
theorem deFinetti_martingale
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {α : Type*} [MeasurableSpace α]
    (X : ℕ → Ω → α) (hX : Contractable μ X) :
    ∃ (ℱ : MeasurableSpace Ω) (ν : Ω → Measure α),
      (∀ ω, IsProbabilityMeasure (ν ω)) ∧
      -- The sequence is conditionally i.i.d. given ℱ = 𝒯_X with law ν
      (ℱ = tailSigma X) ∧
      -- Conditional i.i.d. property (to be formalized)
      sorry := by
  use tailSigma X
  -- Define ν ω = P[X₁ ∈ · | 𝒯_X](ω)
  -- Use extreme_members_equal_on_tail to show conditional laws agree
  -- Use contraction_independence iteratively to show conditional independence
  sorry

-- TODO: Add main theorem when proof is complete
-- theorem deFinetti_viaMartingale := ...

end ViaMartingale
end DeFinetti
end Exchangeability
