/-
Copyright (c) 2025 exchangeability contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: exchangeability contributors
-/
import Mathlib.Probability.ConditionalExpectation
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Probability.Martingale.Basic
import Exchangeability.Contractability
import Exchangeability.Probability.CondExp

/-!
# Third proof of de Finetti via a martingale argument (Aldous)

This file contains Aldous's elegant martingale proof of de Finetti's theorem, as
presented in Kallenberg (2005), Section 1.2.

## Main results

* `contraction_independence`: If `(ξ, η) =^d (ξ, ζ)` and `σ(η) ⊆ σ(ζ)`, then
  `ξ ⊥⊥_η ζ` (Lemma 1.3 in Kallenberg).
  
  **Proof idea:** For any measurable set `B`, define
  `μ₁ = P[ξ ∈ B | η]` and `μ₂ = P[ξ ∈ B | ζ]`.
  Then `(μ₁, μ₂)` is a bounded martingale with `μ₁ =^d μ₂`, so
  `E(μ₂ - μ₁)² = Eμ₂² - Eμ₁² = 0`, implying `μ₁ = μ₂` a.s.
  By Doob's characterization (FMP 6.6), this gives conditional independence.

* `deFinetti_martingale`: If `ξ` is contractable, then the `ξₙ` are conditionally
  i.i.d. given the tail σ-algebra `𝒯_ξ = ⋂_n σ(θ_n ξ)`.
  
  **Proof idea:** From contractability, `(ξ_m, θ_m ξ) =^d (ξ_k, θ_k ξ)` for `k ≤ m`.
  Using the contraction-independence lemma and reverse martingale convergence:
  ```
  P[ξ_m ∈ B | θ_m ξ] = P[ξ_k ∈ B | θ_m ξ] → P[ξ_k ∈ B | 𝒯_ξ]
  ```
  This shows:
  - `P[ξ_m ∈ B | θ_m ξ] = P[ξ_m ∈ B | 𝒯_ξ]`, giving `ξ_m ⊥⊥_{𝒯_ξ} θ_m ξ`
  - By iteration, `ξ₁, ξ₂, ...` are conditionally independent given `𝒯_ξ`
  - `P[ξ_m ∈ B | 𝒯_ξ] = P[ξ₁ ∈ B | 𝒯_ξ]`, showing identical conditional laws

## References

* Olav Kallenberg, *Probabilistic Symmetries and Invariance Principles* (2005),
  Lemma 1.3 and third proof of Theorem 1.1 (page 28).
* David Aldous, *Exchangeability and related topics*, École d'Été de
  Probabilités de Saint-Flour XIII (1983).
-/

noncomputable section
open scoped MeasureTheory ProbabilityTheory Topology

namespace Exchangeability
namespace DeFinetti
namespace MartingaleApproach

open MeasureTheory Filter

variable {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]

/-- `shiftProcess X m` is the process `n ↦ X (m + n)` (Kallenberg's θₘ ξ). -/
def shiftProcess (X : ℕ → Ω → α) (m : ℕ) : ℕ → Ω → α := fun n ω => X (m + n) ω

/-- The random path of a process: ω ↦ (n ↦ X n ω). -/
def path (X : ℕ → Ω → α) : Ω → (ℕ → α) := fun ω n => X n ω

/-- Shifted random path: ω ↦ (n ↦ X (m + n) ω). -/
def shiftRV (X : ℕ → Ω → α) (m : ℕ) : Ω → (ℕ → α) :=
  fun ω n => X (m + n) ω

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

lemma measurable_shiftRV (hX : ∀ n, Measurable (X n)) (m : ℕ) :
    Measurable (shiftRV X m) := by
  classical
  simpa [shiftRV] using
    measurable_pi_iff.mpr (fun n => by simpa using hX (m + n))

end Measurability

lemma revFiltration_antitone (X : ℕ → Ω → α) :
    Antitone (revFiltration X) := by
  -- Goal: m ≤ k ⇒ revFiltration X k ≤ revFiltration X m (i.e., σ(θₖX) ⊆ σ(θₘX)).
  -- Key: shiftRV X k = (fun f n => f (k - m + n)) ∘ (shiftRV X m)
  intro m k hmk
  simp only [revFiltration]
  -- Show: comap (shiftRV X k) ≤ comap (shiftRV X m)
  -- Define the "drop" function that shifts a sequence
  let drop : (ℕ → α) → (ℕ → α) := fun f n => f (k - m + n)
  -- Key equality: shiftRV X k = drop ∘ shiftRV X m
  have h_eq : shiftRV X k = drop ∘ shiftRV X m := by
    ext ω n
    simp [shiftRV, drop]
    congr 1
    omega
  rw [h_eq]
  -- comap (drop ∘ shiftRV X m) = comap (shiftRV X m) (comap drop)
  -- and comap (shiftRV X m) (comap drop) ≤ comap (shiftRV X m) ⊤
  conv_lhs => rw [MeasurableSpace.comap_comp]
  exact MeasurableSpace.comap_mono le_top

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

Since `σ(η) ⊆ σ(ζ)`, we have that `μ₁` is `σ(η)`-measurable and `μ₂` is `σ(ζ)`-measurable,
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
  -- Step 3: Since σ(η) ⊆ σ(ζ), this implies ξ ⊥⊥_η ζ by Doob's characterization (FMP 6.6)
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

/-- Cylinder version: contractability implies measure equality on finite cylinders.

For any finite index set and measurable sets, the measures of the corresponding
cylinders agree when comparing `(X_m, shiftRV X m)` and `(X_k, shiftRV X m)`. -/
lemma contractable_dist_eq_on_cylinders
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → α} (hX : Contractable μ X) (k m : ℕ) (hk : k ≤ m)
    (B : Set α) (hB : MeasurableSet B)
    (s : Finset ℕ) (t : ∀ i ∈ s, Set α) (ht : ∀ i (hi : i ∈ s), MeasurableSet (t i hi)) :
    μ {ω | X m ω ∈ B ∧ ∀ i (hi : i ∈ s), X (m + i) ω ∈ t i hi}
      = μ {ω | X k ω ∈ B ∧ ∀ i (hi : i ∈ s), X (m + i) ω ∈ t i hi} := by
  -- Proof sketch:
  -- The cylinder event involves coordinates at positions m, m+i₁, m+i₂, ... (for i in s)
  -- and k, m+i₁, m+i₂, ... respectively.
  --
  -- Key steps:
  -- 1. Convert finset s to a sorted list to get strict ordering
  -- 2. Build index functions j_m and j_k : Fin (s.card + 1) → ℕ where:
  --    j_m(0) = m, j_m(i+1) = m + s.sort(i)
  --    j_k(0) = k, j_k(i+1) = m + s.sort(i)
  -- 3. Show both j_m and j_k are strictly monotone (uses k ≤ m and s.sort ordering)
  -- 4. Express both cylinder sets as preimages under (fun ω i => X (j i) ω)
  -- 5. Apply contractability: both distributions equal the canonical distribution
  --
  -- Required API:
  -- - Finset.sort: convert finset to sorted list
  -- - Connection between set membership and Measure.map preimages
  -- - Product cylinder set lemmas
  sorry

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
  -- 1. From condexp_convergence: 𝔼[1_{X_m∈B} | 𝔽ₙ] = 𝔼[1_{X_0∈B} | 𝔽ₙ] for all n ≥ m
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
abbrev 𝔽 (X : ℕ → Ω → α) (m : ℕ) : MeasurableSpace Ω := revFiltration X m

/-- Mₘ := 𝔼[1_{Xₖ∈B} | 𝔽ₘ].
The reverse martingale sequence for the indicator of X_k in B. -/
def M (μ : Measure Ω) [IsProbabilityMeasure μ] (X : ℕ → Ω → α) (k : ℕ) (B : Set α) (m : ℕ) : Ω → ℝ :=
  μ[Set.indicator B (fun _ => (1 : ℝ)) ∘ (X k) | revFiltration X m]

-- TODO (see CondExp.lean):
-- (1) 0 ≤ M k B m ≤ 1 a.s.
--     Lemma: condexp_indicator_bounds
-- (2) For m ≤ n, M k B n is 𝔽ₙ-measurable and E[M k B n | 𝔽ₘ] = M k B m a.s.
--     Lemmas: stronglyMeasurable_condexp, condexp_tower
-- (3) If (X m, θₘ X) =^d (X k, θₘ X), then M m B m = M k B m a.s.
--     Lemma: condexp_indicator_eq_of_dist_eq_and_le (already stated above)
-- (4) (M k B m)ₘ is a reverse martingale, so M k B m → 𝔼[1_{Xₖ∈B} | tailSigma X] a.s./L¹.
--     Lemma: condexp_tendsto_condexp_iInf (Lévy's downward theorem)

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

end MartingaleApproach
end DeFinetti
end Exchangeability
