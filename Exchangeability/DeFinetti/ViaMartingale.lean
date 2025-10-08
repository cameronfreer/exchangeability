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
  -- Possible approaches:
  -- 1. Split into cases 0 ∈ s and 0 ∉ s
  -- 2. Use a larger index set that includes both k and m explicitly
  -- 3. Use conditional probability / factorization

  /-
  -- Previous attempt (has type errors):
  let T : Set (Fin (n + 1) → α) :=
    {f | (if h0 : 0 ∈ s then f 0 ∈ B ∩ t 0 h0 else f 0 ∈ B) ∧
         ∀ i : Fin n, f (Fin.succ i) ∈ t0 (tail i) (htail_mem i)}
  have h_m_event : {ω | X m ω ∈ B ∧ zeroConstraint ω ∧ tailCondition ω} =
                   {ω | (fun ω i => X (k_map_m i) ω) ω ∈ T} := by
    ext ω
    simp only [Set.mem_setOf_eq, T, k_map_m, k_m, zeroConstraint, tailCondition]
    constructor <;> intro h
    · obtain ⟨hB, hzero, htail⟩ := h
      constructor
      · by_cases h0 : 0 ∈ s
        · simp [h0, Fin.cases]
          exact ⟨hB, by simpa [h0] using hzero⟩
        · simp [h0, Fin.cases]
          exact hB
      · intro i
        have hi_mem := htail_mem i
        simp [Fin.cases]
        exact htail (tail i) hi_mem
    · obtain ⟨hfirst, htail_cond⟩ := h
      refine ⟨?_, ?_, ?_⟩
      · by_cases h0 : 0 ∈ s
        · simp [h0, Fin.cases] at hfirst
          exact hfirst.1
        · simp [h0, Fin.cases] at hfirst
          exact hfirst
      · by_cases h0 : 0 ∈ s
        · simp [h0, Fin.cases] at hfirst
          simp [h0]
          exact hfirst.2
        · simp [h0]
      · intro i hi
        -- For i ∈ s0, orderEmbOfFin_surj gives us j with tail j = i
        obtain ⟨j, hj_eq⟩ := orderEmbOfFin_surj s0 i hi
        specialize htail_cond j
        simp [Fin.cases] at htail_cond
        -- htail_cond : X (m + tail j) ω ∈ t0 (tail j) (htail_mem j)
        -- Goal: X (m + i) ω ∈ t0 i hi
        -- hj_eq : tail j = i (since tail j is defined as orderEmbOfFin j)
        convert htail_cond using 3
        -- Need to show i = tail j
        exact hj_eq.symm

  have h_k_event : {ω | X k ω ∈ B ∧ zeroConstraint ω ∧ tailCondition ω} =
                   {ω | (fun ω i => X (k_map_k i) ω) ω ∈ T} := by
    ext ω
    simp only [Set.mem_setOf_eq, T, k_map_k, zeroConstraint, tailCondition]
    constructor <;> intro h
    · obtain ⟨hB, hzero, htail⟩ := h
      constructor
      · by_cases h0 : 0 ∈ s
        · simp [h0, Fin.cases]
          refine ⟨hB, ?_⟩
          simp [h0] at hzero
          exact hzero
        · simp [h0, Fin.cases]
          exact hB
      · intro i
        have hi_mem := htail_mem i
        simp [Fin.cases]
        exact htail (tail i) hi_mem
    · obtain ⟨hfirst, htail_cond⟩ := h
      refine ⟨?_, ?_, ?_⟩
      · by_cases h0 : 0 ∈ s
        · simp [h0, Fin.cases] at hfirst
          exact hfirst.1
        · simp [h0, Fin.cases] at hfirst
          exact hfirst
      · by_cases h0 : 0 ∈ s
        · simp [h0, Fin.cases] at hfirst
          simp [h0]
          exact hfirst.2
        · simp [h0]
      · intro i hi
        -- Same as above: use orderEmbOfFin_surj
        obtain ⟨j, hj_eq⟩ := orderEmbOfFin_surj s0 i hi
        specialize htail_cond j
        simp [Fin.cases] at htail_cond
        convert htail_cond using 3
        exact hj_eq.symm

  -- Apply contractability: both sides map to same distribution
  have h_contract_m := hX (n + 1) k_map_m hk_map_m_mono
  have h_contract_k := hX (n + 1) k_map_k hk_map_k_mono

  -- Rewrite using the event identifications
  rw [h_event_rewrite, h_event_rewrite_k, h_m_event, h_k_event]

  -- Both are preimages of T under measure-preserving maps
  sorry  -- Final step: use h_contract_m and h_contract_k to show measure equality

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
  -- Strategy: Use contractable_dist_eq_on_cylinders to show equality on cylinder sets,
  -- then extend to all measurable sets via the π-λ theorem.
  --
  -- 1. Cylinder sets of the form {(a, f) | a ∈ B, f(i) ∈ t_i for i ∈ s} generate
  --    the product σ-algebra on α × (ℕ → α)
  -- 2. By contractable_dist_eq_on_cylinders, both measures agree on all such cylinders
  -- 3. Apply Measure.ext_of_generateFrom_of_cover (π-λ theorem) to conclude equality
  --
  -- Required API:
  -- - MeasureTheory.generate_from_prod_cylinder: cylinders generate product σ-algebra
  -- - Measure.ext_of_generateFrom_of_cover: π-λ theorem for measures
  -- - Formalization of cylinder sets in the product space
  sorry

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
