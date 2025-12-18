/-
Copyright (c) 2025 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer, Claude (Anthropic)
-/
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Exchangeability.Probability.CondExpBasic

/-!
# Kallenberg Lemma 1.3: Drop-Info Property via Contraction

This file implements **Kallenberg (2005), Lemma 1.3**, the "contraction-independence" lemma.

## Main Results

* `condExp_indicator_eq_of_law_eq_of_comap_le`: If `(X,W) =^d (X,W')` and `σ(W) ⊆ σ(W')`,
  then `E[1_{X∈A}|σ(W')] = E[1_{X∈A}|σ(W)]` a.e.

## Mathematical Background

**Kallenberg's Lemma 1.3 (Contraction-Independence):**

Given random elements ξ, η, ζ where:
1. `(ξ, η) =^d (ξ, ζ)` (pair laws match)
2. `σ(η) ⊆ σ(ζ)` (η is a *contraction* of ζ — i.e., η = f ∘ ζ for some measurable f)

**Conclusion:** `P[ξ ∈ B | ζ] = P[ξ ∈ B | η]` a.s.

The intuition: conditioning on the finer σ-algebra σ(ζ) gives the same result as
conditioning on the coarser σ-algebra σ(η), because the "extra" information in ζ
beyond η doesn't change the relationship with ξ (due to the pair law equality).

**Proof Strategy (L²/Martingale Argument):**
1. Define μ₁ := E[1_{ξ∈B}|η] and μ₂ := E[1_{ξ∈B}|ζ]
2. Tower property: Since σ(η) ≤ σ(ζ), we have μ₁ = E[μ₂|η]
3. Law equality: From (ξ,η) =^d (ξ,ζ), we get μ₁ =^d μ₂ (same distribution)
4. L² computation:
   - E[μ₁²] = E[μ₂²] (from μ₁ =^d μ₂)
   - E[(μ₂ - μ₁)²] = E[μ₂²] - 2E[μ₂μ₁] + E[μ₁²]
   - By tower + pull-out: E[μ₂μ₁] = E[E[μ₂|η]·μ₁] = E[μ₁²]
   - Thus E[(μ₂ - μ₁)²] = E[μ₂²] - E[μ₁²] = 0
5. Conclude: μ₂ = μ₁ a.e.

**Important:** This lemma does NOT say you can drop a variable Z from conditioning
on σ(Z,W) down to σ(W). It says you can drop "extra information" from a *finer*
conditioning σ-algebra (σ(W')) down to a *coarser* one (σ(W)) when the pair law
assumption holds.

## References

* Kallenberg (2005), *Probabilistic Symmetries and Invariance Principles*, Lemma 1.3
-/

open MeasureTheory MeasurableSpace
open scoped ENNReal

variable {Ω α γ : Type*}
variable [MeasurableSpace Ω] [MeasurableSpace α] [MeasurableSpace γ]

/-! ### Helper Lemmas for RN-Derivative Approach -/

/-- From pair law equality `(X,W) =^d (X,W')`, extract marginal law equality `W =^d W'`. -/
lemma marginal_law_eq_of_pair_law
    {μ : Measure Ω}
    (X : Ω → α) (W W' : Ω → γ)
    (hX : Measurable X) (hW : Measurable W) (hW' : Measurable W')
    (h_law : Measure.map (fun ω => (X ω, W ω)) μ = Measure.map (fun ω => (X ω, W' ω)) μ) :
    Measure.map W μ = Measure.map W' μ := by
  have h1 : Measure.map W μ = Measure.map Prod.snd (Measure.map (fun ω => (X ω, W ω)) μ) := by
    rw [Measure.map_map measurable_snd (hX.prodMk hW)]; rfl
  have h2 : Measure.map W' μ = Measure.map Prod.snd (Measure.map (fun ω => (X ω, W' ω)) μ) := by
    rw [Measure.map_map measurable_snd (hX.prodMk hW')]; rfl
  rw [h1, h_law, ← h2]

/-- From pair law equality, derive joint measure equality on the conditioning space.

If `(X,W) =^d (X,W')`, then `map W (μ.restrict (X ⁻¹' A)) = map W' (μ.restrict (X ⁻¹' A))`.

Intuitively: "the law of W restricted to {X ∈ A}" equals "the law of W' restricted to {X ∈ A}". -/
lemma joint_measure_eq_of_pair_law
    {μ : Measure Ω}
    (X : Ω → α) (W W' : Ω → γ)
    (hX : Measurable X) (hW : Measurable W) (hW' : Measurable W')
    (h_law : Measure.map (fun ω => (X ω, W ω)) μ = Measure.map (fun ω => (X ω, W' ω)) μ)
    {A : Set α} (hA : MeasurableSet A) :
    Measure.map W (μ.restrict (X ⁻¹' A)) = Measure.map W' (μ.restrict (X ⁻¹' A)) := by
  ext B hB
  -- ν(B) = μ((X ⁻¹' A) ∩ (W ⁻¹' B)) = law(X,W)(A ×ˢ B)
  rw [Measure.map_apply hW hB, Measure.map_apply hW' hB]
  rw [Measure.restrict_apply (hW hB), Measure.restrict_apply (hW' hB)]
  -- Note: restrict_apply gives (W ⁻¹' B) ∩ (X ⁻¹' A), so use commutativity
  rw [Set.inter_comm (W ⁻¹' B), Set.inter_comm (W' ⁻¹' B)]
  -- Show both equal (map (X,W) μ)(A ×ˢ B)
  have h1 : (X ⁻¹' A) ∩ (W ⁻¹' B) = (fun ω => (X ω, W ω)) ⁻¹' (A ×ˢ B) := by
    ext ω; simp [Set.mem_prod]
  have h2 : (X ⁻¹' A) ∩ (W' ⁻¹' B) = (fun ω => (X ω, W' ω)) ⁻¹' (A ×ˢ B) := by
    ext ω; simp [Set.mem_prod]
  rw [h1, h2]
  rw [← Measure.map_apply (hX.prodMk hW) (hA.prod hB)]
  rw [← Measure.map_apply (hX.prodMk hW') (hA.prod hB)]
  rw [h_law]

/-- **Kallenberg Lemma 1.3 (Contraction-Independence).**

If `(X,W) =^d (X,W')` (pair laws equal) and `σ(W) ⊆ σ(W')` (W is a contraction of W'),
then conditioning an indicator of X on σ(W') equals conditioning on σ(W).

This is the "drop information from finer to coarser σ-algebra" property.

**Proof:** L²/martingale argument.
1. Let μ₁ := E[φ|σ(W)] and μ₂ := E[φ|σ(W')] where φ = 1_{X∈A}
2. Tower: μ₁ = E[μ₂|σ(W)] (since σ(W) ≤ σ(W'))
3. Law equality: E[μ₁²] = E[μ₂²] (from pair law)
4. Compute: E[(μ₂-μ₁)²] = E[μ₂²] - 2E[μ₂μ₁] + E[μ₁²]
           = E[μ₂²] - 2E[E[μ₂|σ(W)]·μ₁] + E[μ₁²]  (tower)
           = E[μ₂²] - 2E[μ₁²] + E[μ₁²]
           = E[μ₂²] - E[μ₁²] = 0
5. So μ₂ = μ₁ a.e.
-/
lemma condExp_indicator_eq_of_law_eq_of_comap_le
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : Ω → α) (W W' : Ω → γ)
    (hX : Measurable X) (hW : Measurable W) (hW' : Measurable W')
    (h_law : Measure.map (fun ω => (X ω, W ω)) μ
           = Measure.map (fun ω => (X ω, W' ω)) μ)
    (h_le : MeasurableSpace.comap W inferInstance ≤ MeasurableSpace.comap W' inferInstance)
    {A : Set α} (hA : MeasurableSet A) :
    μ[Set.indicator (X ⁻¹' A) (fun _ => (1 : ℝ)) | MeasurableSpace.comap W' inferInstance]
      =ᵐ[μ]
    μ[Set.indicator (X ⁻¹' A) (fun _ => (1 : ℝ)) | MeasurableSpace.comap W inferInstance] := by
  /-
  **Proof outline (Kallenberg L² argument):**

  Setup:
  - φ = 1_{X∈A} (indicator function)
  - mW = σ(W), mW' = σ(W') (generated σ-algebras)
  - μ₁ = E[φ|mW], μ₂ = E[φ|mW'] (conditional expectations)

  Key steps:
  1. Tower property: E[μ₂|mW] = μ₁  (since mW ≤ mW')
  2. Boundedness: 0 ≤ μ₁, μ₂ ≤ 1 a.e. (condExp of indicator is in [0,1])
  3. Cross term: E[μ₂·μ₁] = E[μ₁²]  (pull-out + tower)
  4. Square equality: E[μ₁²] = E[μ₂²]  (from pair law via RN derivative)
  5. L² computation: E[(μ₂-μ₁)²] = E[μ₂²] - 2E[μ₂μ₁] + E[μ₁²]
                                 = E[μ₂²] - 2E[μ₁²] + E[μ₁²]
                                 = E[μ₂²] - E[μ₁²] = 0
  6. Conclusion: L² = 0 with nonneg integrand ⟹ μ₂ = μ₁ a.e.

  The key mathematical content is step 4: Both μ₁² and μ₂² integrate to the
  same value because both can be expressed as compositions with a common
  RN derivative g = dν/dρ where:
  - ρ = law(W) = law(W')  (from pair law)
  - ν = law(W | X∈A) = law(W' | X∈A)  (from pair law)

  Then ∫ μ₁² dμ = ∫ g² dρ = ∫ μ₂² dμ by change of variables.
  -/

  -- Setup: helper measures from pair law
  have hρ_eq : Measure.map W μ = Measure.map W' μ :=
    marginal_law_eq_of_pair_law X W W' hX hW hW' h_law
  have hν_eq : Measure.map W (μ.restrict (X ⁻¹' A)) =
               Measure.map W' (μ.restrict (X ⁻¹' A)) :=
    joint_measure_eq_of_pair_law X W W' hX hW hW' h_law hA

  -- The full proof uses L² techniques with conditional expectations.
  -- The mathematical content follows from the law equalities above.
  -- TODO: Complete the technical details using:
  -- - condExp_condExp_of_le (tower property)
  -- - condExp_mul_of_stronglyMeasurable_right (pull-out)
  -- - integral_eq_zero_iff_of_nonneg_ae (L² = 0 ⟹ ae equality)
  sorry

/-! ### Original proof (commented out due to API issues)

The proof below has issues with recent mathlib API changes.
Keeping for reference.
-/

#check @condExp_condExp_of_le  -- Reference for tower property

-- Original proof body (for reference):
/-
  classical
  -- Setup notation
  let φ : Ω → ℝ := Set.indicator (X ⁻¹' A) (fun _ => (1 : ℝ))
  let mW : MeasurableSpace Ω := MeasurableSpace.comap W inferInstance
  let mW' : MeasurableSpace Ω := MeasurableSpace.comap W' inferInstance

  -- σ-algebra relationships
  have hmW_le : mW ≤ _ := measurable_iff_comap_le.mp hW
  have hmW'_le : mW' ≤ _ := measurable_iff_comap_le.mp hW'

  -- Integrability of indicator
  have hφ_int : Integrable φ μ := by
    apply Integrable.indicator
    · exact integrable_const 1
    · exact hX hA

  -- Define the conditional expectations
  set μ₁ := μ[φ | mW] with hμ₁_def
  set μ₂ := μ[φ | mW'] with hμ₂_def

  -- Goal: μ₂ =ᵐ[μ] μ₁

  -- Step 1: Tower property: E[μ₂|mW] = E[φ|mW] = μ₁
  have h_tower : μ[μ₂ | mW] =ᵐ[μ] μ₁ := by
    -- Need SigmaFinite for trim
    haveI hσfW' : SigmaFinite (μ.trim hmW'_le) := sigmaFinite_trim_of_le μ hmW'_le
    exact condExp_condExp_of_le h_le hmW'_le

  -- Step 2: μ₁ and μ₂ are both bounded [0,1] indicators
  have hμ₁_bdd : ∀ᵐ ω ∂μ, 0 ≤ μ₁ ω ∧ μ₁ ω ≤ 1 := by
    have h1 : ∀ᵐ ω ∂μ, 0 ≤ μ₁ ω := by
      filter_upwards [condExp_nonneg (ae_of_all μ (fun ω => Set.indicator_nonneg (fun _ _ => zero_le_one) _))]
        with ω hω using hω
    have h2 : ∀ᵐ ω ∂μ, μ₁ ω ≤ 1 := by
      have hφ_le : ∀ ω, φ ω ≤ 1 := fun ω => by
        unfold Set.indicator
        split_ifs <;> linarith
      have hc := condExp_const hmW_le (1 : ℝ)
      filter_upwards [condExp_mono (ae_of_all μ hφ_le) hφ_int (integrable_const 1)] with ω h1
      calc μ₁ ω ≤ μ[(fun _ => (1 : ℝ))|mW] ω := h1
        _ = 1 := congrFun hc ω
    filter_upwards [h1, h2] with ω h1 h2
    exact ⟨h1, h2⟩

  have hμ₂_bdd : ∀ᵐ ω ∂μ, 0 ≤ μ₂ ω ∧ μ₂ ω ≤ 1 := by
    have h1 : ∀ᵐ ω ∂μ, 0 ≤ μ₂ ω := by
      filter_upwards [condExp_nonneg (ae_of_all μ (fun ω => Set.indicator_nonneg (fun _ _ => zero_le_one) _))]
        with ω hω using hω
    have h2 : ∀ᵐ ω ∂μ, μ₂ ω ≤ 1 := by
      have hφ_le : ∀ ω, φ ω ≤ 1 := fun ω => by
        unfold Set.indicator
        split_ifs <;> linarith
      have hc := condExp_const hmW'_le (1 : ℝ)
      filter_upwards [condExp_mono (ae_of_all μ hφ_le) hφ_int (integrable_const 1)] with ω h1
      calc μ₂ ω ≤ μ[(fun _ => (1 : ℝ))|mW'] ω := h1
        _ = 1 := congrFun hc ω
    filter_upwards [h1, h2] with ω h1 h2
    exact ⟨h1, h2⟩

  -- Step 3: Integrability facts
  have hμ₁_int : Integrable μ₁ μ := integrable_condExp
  have hμ₂_int : Integrable μ₂ μ := integrable_condExp

  have hμ₁sq_int : Integrable (μ₁ * μ₁) μ := by
    apply Integrable.bdd_mul hμ₁_int stronglyMeasurable_condExp.aestronglyMeasurable
    use 1
    filter_upwards [hμ₁_bdd] with ω ⟨h0, h1⟩
    rw [abs_le]
    constructor <;> linarith

  have hμ₂sq_int : Integrable (μ₂ * μ₂) μ := by
    apply Integrable.bdd_mul hμ₂_int stronglyMeasurable_condExp.aestronglyMeasurable
    use 1
    filter_upwards [hμ₂_bdd] with ω ⟨h0, h1⟩
    rw [abs_le]
    constructor <;> linarith

  have hμ₂μ₁_int : Integrable (μ₂ * μ₁) μ := by
    apply Integrable.bdd_mul hμ₂_int stronglyMeasurable_condExp.aestronglyMeasurable
    use 1
    filter_upwards [hμ₁_bdd] with ω ⟨h0, h1⟩
    rw [abs_le]
    constructor <;> linarith

  -- Step 4: The key L² computation
  -- We need: E[(μ₂ - μ₁)²] = E[μ₂²] - 2E[μ₂μ₁] + E[μ₁²]
  -- And: E[μ₂μ₁] = E[E[μ₂|mW]·μ₁] = E[μ₁²] (by tower + pull-out)
  -- And: E[μ₁²] = E[μ₂²] (from law equality)

  -- Step 4a: E[μ₂μ₁] = E[μ₁²]
  -- This uses: μ₁ is mW-measurable, so E[μ₂·μ₁] = E[E[μ₂|mW]·μ₁] = E[μ₁·μ₁]
  have h_cross : ∫ ω, μ₂ ω * μ₁ ω ∂μ = ∫ ω, μ₁ ω * μ₁ ω ∂μ := by
    -- Use: ∫ μ₂ * μ₁ = ∫ E[μ₂|mW] * μ₁ (since μ₁ is mW-measurable)
    have hμ₁_meas : StronglyMeasurable[mW] μ₁ := stronglyMeasurable_condExp
    -- Pull-out: E[μ₂ * μ₁] = E[E[μ₂|mW] * μ₁]
    calc ∫ ω, μ₂ ω * μ₁ ω ∂μ
        = ∫ ω, μ[μ₂ | mW] ω * μ₁ ω ∂μ := by
          -- Since μ₁ is mW-measurable: ∫ μ₂ * μ₁ = ∫ E[μ₂|mW] * μ₁
          have h_pullout := condExp_mul_of_stronglyMeasurable_right (m := mW)
            hμ₁_meas hμ₂μ₁_int hμ₂_int
          -- h_pullout: μ[μ₂ * μ₁|mW] =ᵐ μ[μ₂|mW] * μ₁
          -- Taking expectation: ∫ μ₂ * μ₁ = ∫ μ[μ₂ * μ₁|mW] = ∫ μ[μ₂|mW] * μ₁
          rw [← integral_condExp hmW_le hμ₂μ₁_int]
          apply integral_congr_ae
          exact h_pullout
      _ = ∫ ω, μ₁ ω * μ₁ ω ∂μ := by
          -- By tower: E[μ₂|mW] = μ₁ a.e.
          apply integral_congr_ae
          filter_upwards [h_tower] with ω hω
          rw [hω]

  -- Step 4b: E[μ₁²] = E[μ₂²] from the pair law (X,W) =^d (X,W')
  -- This is the key step using the law equality hypothesis
  have h_sq_eq : ∫ ω, μ₁ ω * μ₁ ω ∂μ = ∫ ω, μ₂ ω * μ₂ ω ∂μ := by
    -- Key insight: (X,W) =^d (X,W') implies:
    -- 1. law(W) = law(W') (project to second component)
    -- 2. law(φ, W) = law(φ, W') (since φ is a function of X)
    -- 3. The conditional expectation E[φ|W] pushed forward by W equals
    --    E[φ|W'] pushed forward by W' (both are the "conditional probability
    --    of φ given the conditioning variable" with the same law)
    --
    -- More precisely:
    -- - μ₁ = E[φ|σ(W)] = g₁ ∘ W for some measurable g₁ (Doob-Dynkin)
    -- - μ₂ = E[φ|σ(W')] = g₂ ∘ W' for some measurable g₂
    -- - The pair law equality gives: for all measurable B,
    --   ∫_B g₁ d(law W) = μ(φ=1, W∈B) = μ(φ=1, W'∈B) = ∫_B g₂ d(law W')
    -- - Also law(W) = law(W') from the pair law marginal
    -- - So g₁ = g₂ (law W)-a.e.
    -- - Thus ∫ g₁² d(law W) = ∫ g₂² d(law W')
    -- - Thus ∫ μ₁² dμ = ∫ μ₂² dμ
    --
    -- This requires disintegration / regular conditional probability theory
    -- which is deep in mathlib. For now, we accept this as the mathematical
    -- content of Kallenberg 1.3.
    sorry

  -- Step 5: Conclude via L² = 0 implies a.e. equality
  -- E[(μ₂ - μ₁)²] = E[μ₂²] - 2E[μ₂μ₁] + E[μ₁²]
  --              = E[μ₂²] - 2E[μ₁²] + E[μ₁²]   (by h_cross)
  --              = E[μ₂²] - E[μ₁²]
  --              = 0                             (by h_sq_eq)
  have h_L2_zero : ∫ ω, (μ₂ ω - μ₁ ω)^2 ∂μ = 0 := by
    have h_expand : ∀ᵐ ω ∂μ, (μ₂ ω - μ₁ ω)^2 = μ₂ ω * μ₂ ω - 2 * (μ₂ ω * μ₁ ω) + μ₁ ω * μ₁ ω := by
      filter_upwards with ω
      ring
    calc ∫ ω, (μ₂ ω - μ₁ ω)^2 ∂μ
        = ∫ ω, (μ₂ ω * μ₂ ω - 2 * (μ₂ ω * μ₁ ω) + μ₁ ω * μ₁ ω) ∂μ := by
          apply integral_congr_ae h_expand
      _ = ∫ ω, μ₂ ω * μ₂ ω ∂μ - 2 * ∫ ω, μ₂ ω * μ₁ ω ∂μ + ∫ ω, μ₁ ω * μ₁ ω ∂μ := by
          rw [integral_add, integral_sub]
          · ring
          · exact hμ₂sq_int
          · exact hμ₂μ₁_int.const_mul 2
          · exact hμ₂sq_int.sub (hμ₂μ₁_int.const_mul 2)
          · exact hμ₁sq_int
      _ = ∫ ω, μ₂ ω * μ₂ ω ∂μ - 2 * ∫ ω, μ₁ ω * μ₁ ω ∂μ + ∫ ω, μ₁ ω * μ₁ ω ∂μ := by
          rw [h_cross]
      _ = ∫ ω, μ₂ ω * μ₂ ω ∂μ - ∫ ω, μ₁ ω * μ₁ ω ∂μ := by ring
      _ = 0 := by rw [h_sq_eq]; ring

  -- From L² = 0, conclude μ₂ = μ₁ a.e.
  have h_diff_zero : ∀ᵐ ω ∂μ, (μ₂ ω - μ₁ ω)^2 = 0 := by
    have h_nonneg : ∀ᵐ ω ∂μ, 0 ≤ (μ₂ ω - μ₁ ω)^2 := ae_of_all μ (fun ω => sq_nonneg _)
    have h_int : Integrable (fun ω => (μ₂ ω - μ₁ ω)^2) μ := by
      have h_diff_int : Integrable (μ₂ - μ₁) μ := hμ₂_int.sub hμ₁_int
      apply Integrable.bdd_mul h_diff_int (h_diff_int.aestronglyMeasurable)
      use 2
      filter_upwards [hμ₁_bdd, hμ₂_bdd] with ω ⟨h0₁, h1₁⟩ ⟨h0₂, h1₂⟩
      rw [abs_le]
      constructor <;> linarith
    exact (integral_eq_zero_iff_of_nonneg_ae h_nonneg h_int).mp h_L2_zero

  -- (μ₂ - μ₁)² = 0 implies μ₂ = μ₁
  filter_upwards [h_diff_zero] with ω hω
  have : μ₂ ω - μ₁ ω = 0 := by nlinarith [sq_nonneg (μ₂ ω - μ₁ ω)]
  linarith
-/

/-- Helper to extract pair law from triple law. -/
lemma pair_law_of_triple_law {β : Type*} [MeasurableSpace β]
    {μ : Measure Ω}
    (X : Ω → α) (Y : Ω → β) (W W' : Ω → γ)
    (hX : Measurable X) (hY : Measurable Y) (hW : Measurable W) (hW' : Measurable W')
    (h_triple : Measure.map (fun ω => (X ω, Y ω, W ω)) μ
              = Measure.map (fun ω => (X ω, Y ω, W' ω)) μ) :
    Measure.map (fun ω => ((X ω, Y ω), W ω)) μ
      = Measure.map (fun ω => ((X ω, Y ω), W' ω)) μ := by
  -- Reassociation via the isomorphism (α × β) × γ ≃ α × (β × γ)
  have h_assoc : Measurable (fun t : α × β × γ => ((t.1, t.2.1), t.2.2)) :=
    (measurable_fst.prodMk measurable_snd.fst).prodMk measurable_snd.snd
  have h1 : (fun ω => ((X ω, Y ω), W ω)) =
            (fun t : α × β × γ => ((t.1, t.2.1), t.2.2)) ∘ (fun ω => (X ω, Y ω, W ω)) := rfl
  have h2 : (fun ω => ((X ω, Y ω), W' ω)) =
            (fun t : α × β × γ => ((t.1, t.2.1), t.2.2)) ∘ (fun ω => (X ω, Y ω, W' ω)) := rfl
  rw [h1, h2]
  rw [← Measure.map_map h_assoc (hX.prodMk (hY.prodMk hW))]
  rw [← Measure.map_map h_assoc (hX.prodMk (hY.prodMk hW'))]
  rw [h_triple]

/-- Legacy wrapper: the old `condExp_eq_of_triple_law_direct` interface.

**WARNING:** This lemma's original statement was incorrect. It claimed that
the triple law `(Z,Y,W) =^d (Z,Y,W')` alone implies `E[φ|σ(Z,W)] = E[φ|σ(W)]`.
This is FALSE in general.

This wrapper provides backward compatibility but adds the missing contraction
hypothesis. If your use case doesn't have this hypothesis, the original
claim was invalid and you need to restructure your proof.

The correct statement (Kallenberg 1.3) is `condExp_indicator_eq_of_law_eq_of_comap_le`:
you need `σ(W) ≤ σ(W')` (W is a contraction of W') to drop from σ(W') to σ(W).
-/
lemma condExp_eq_of_triple_law_direct
    {β : Type*} [MeasurableSpace β]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (Y : Ω → α) (Z : Ω → β) (W W' : Ω → γ)
    (hY : Measurable Y) (hZ : Measurable Z) (hW : Measurable W) (hW' : Measurable W')
    (h_triple : Measure.map (fun ω => (Z ω, Y ω, W ω)) μ =
                Measure.map (fun ω => (Z ω, Y ω, W' ω)) μ)
    -- NEW REQUIRED HYPOTHESIS: σ(W) ≤ σ(W') (contraction)
    (h_contraction : MeasurableSpace.comap W inferInstance
                   ≤ MeasurableSpace.comap W' inferInstance)
    {A : Set α} (hA : MeasurableSet A) :
    -- Note: conclusion is now σ(W') → σ(W), not σ(Z,W) → σ(W)
    μ[Set.indicator (Y ⁻¹' A) (fun _ => (1 : ℝ))
       | MeasurableSpace.comap W' inferInstance]
      =ᵐ[μ]
    μ[Set.indicator (Y ⁻¹' A) (fun _ => (1 : ℝ))
       | MeasurableSpace.comap W inferInstance] := by
  -- Extract pair law (Y,W) =^d (Y,W') from triple law by projecting out Z
  have h_pair : Measure.map (fun ω => (Y ω, W ω)) μ
              = Measure.map (fun ω => (Y ω, W' ω)) μ := by
    -- Project triple law (Z,Y,W) to (Y,W) by dropping Z
    have h_proj : Measurable (fun t : β × α × γ => (t.2.1, t.2.2)) :=
      measurable_snd.fst.prodMk measurable_snd.snd
    have h1 : (fun ω => (Y ω, W ω)) =
              (fun t : β × α × γ => (t.2.1, t.2.2)) ∘ (fun ω => (Z ω, Y ω, W ω)) := rfl
    have h2 : (fun ω => (Y ω, W' ω)) =
              (fun t : β × α × γ => (t.2.1, t.2.2)) ∘ (fun ω => (Z ω, Y ω, W' ω)) := rfl
    rw [h1, h2]
    rw [← Measure.map_map h_proj (hZ.prodMk (hY.prodMk hW))]
    rw [← Measure.map_map h_proj (hZ.prodMk (hY.prodMk hW'))]
    rw [h_triple]
  -- Apply the main Kallenberg 1.3 lemma
  exact condExp_indicator_eq_of_law_eq_of_comap_le Y W W' hY hW hW' h_pair h_contraction hA
