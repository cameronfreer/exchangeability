/-
Copyright (c) 2025 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.Probability.ConditionalExpectation
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Exchangeability.Contractability
import Exchangeability.Probability.CondExp
import Exchangeability.Probability.Martingale
import Exchangeability.Probability.MeasureKernels
import Exchangeability.Tail.TailSigma
import Exchangeability.DeFinetti.ViaMartingale.ShiftOperations
import Exchangeability.DeFinetti.ViaMartingale.FutureFiltration
import Exchangeability.DeFinetti.ViaMartingale.FiniteCylinders
import Exchangeability.DeFinetti.ViaMartingale.CondExpConvergence
import Exchangeability.DeFinetti.ViaMartingale.Factorization
import Exchangeability.PathSpace.CylinderHelpers

/-!
# Finite Product Formula

This file proves the finite product formula: for a contractable process X,
the joint law of any strictly increasing subsequence equals the independent
product under the directing measure.

## Main results

* `measure_pi_univ_pi` - Product measures evaluate on rectangles as a finite product
* `bind_apply_univ_pi` - Bind computation on rectangles for finite product measures
* `finite_product_formula_id` - Core case: product formula for identity indexing
* `finite_product_formula_strictMono` - Product formula for strictly monotone subsequences
* `finite_product_formula` - Main wrapper theorem

## Proof strategy

1. Show equality on rectangles using factorization machinery
2. Use reverse martingale convergence for each coordinate
3. Extend from rectangles to full σ-algebra via π-λ theorem
4. Reduce strict-monotone case to identity case via contractability

## References

* Kallenberg (2005), *Probabilistic Symmetries and Invariance Principles*,
  Chapter 1, Theorem 1.1
-/

noncomputable section
open scoped MeasureTheory ProbabilityTheory Topology
open MeasureTheory Filter

namespace Exchangeability.DeFinetti.ViaMartingale

open Exchangeability.PathSpace

variable {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]

/-! ### Finite-dimensional product formula -/

/-! #### Helper lemmas for the product formula -/

/-- Convert lintegral of ENNReal product of probability measures to ofReal of real integral.

For probability measures ν ω, the finite product ∏ᵢ ν ω (Cᵢ) can be computed as either:
- ∫⁻ ω, (∏ᵢ ν ω (Cᵢ)) ∂μ (as ENNReal)
- ENNReal.ofReal (∫ ω, (∏ᵢ (ν ω (Cᵢ)).toReal) ∂μ) (as Real via toReal)

This helper establishes their equality, which is used in the finite product formula proof. -/
lemma lintegral_prod_prob_eq_ofReal_integral
    {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {m : ℕ} (ν : Ω → Measure α) [∀ ω, IsProbabilityMeasure (ν ω)]
    (hν_meas : ∀ B : Set α, MeasurableSet B → Measurable (fun ω => ν ω B))
    (C : Fin m → Set α) (hC : ∀ i, MeasurableSet (C i)) :
    ∫⁻ ω, (∏ i : Fin m, ν ω (C i)) ∂μ
      = ENNReal.ofReal (∫ ω, (∏ i : Fin m, (ν ω (C i)).toReal) ∂μ) := by
  -- Each factor ν ω (C i) ≤ 1, hence the product p(ω) ≤ 1 < ∞ and
  -- p(ω) = ENNReal.ofReal (p(ω).toReal). Use `lintegral_ofReal`.
  have h_point :
      (fun ω => (∏ i : Fin m, ν ω (C i)))
        = (fun ω => ENNReal.ofReal (∏ i : Fin m, (ν ω (C i)).toReal)) := by
    funext ω
    -- turn each factor into ofReal of its toReal (since it's ≤ 1 < ∞)
    have hfactor :
        ∀ i : Fin m, ν ω (C i) = ENNReal.ofReal ((ν ω (C i)).toReal) := by
      intro i
      -- 0 ≤ μ(C) ≤ 1 ⇒ finite ⇒ ofReal_toReal
      have hle1 : ν ω (C i) ≤ 1 := prob_le_one
      have hfin : ν ω (C i) ≠ ⊤ := ne_of_lt (lt_of_le_of_lt hle1 ENNReal.one_lt_top)
      exact (ENNReal.ofReal_toReal hfin).symm
    -- product of ofReals = ofReal of product
    rw [Finset.prod_congr rfl (fun i _ => hfactor i)]
    exact (ENNReal.ofReal_prod_of_nonneg (fun i _ => ENNReal.toReal_nonneg)).symm
  -- now apply lintegral_ofReal
  rw [h_point]
  have h_nonneg : ∀ᵐ ω ∂μ, 0 ≤ ∏ i : Fin m, (ν ω (C i)).toReal :=
    ae_of_all _ fun _ => Finset.prod_nonneg fun _ _ => ENNReal.toReal_nonneg
  -- Step 1: Show measurability of the product function
  let f : Ω → ℝ := fun ω => ∏ i : Fin m, (ν ω (C i)).toReal
  have h_meas : Measurable f := by
    -- Finite product of measurable functions is measurable
    apply Finset.measurable_prod
    intro i _
    -- ν · (C i) is measurable by hν_meas, and toReal is continuous hence measurable
    exact Measurable.ennreal_toReal (hν_meas (C i) (hC i))
  -- Step 2: Show integrability (bounded by 1) via integrable_of_bounded_on_prob
  have h_integrable : Integrable f μ := by
    apply integrable_of_bounded_on_prob h_meas
    apply ae_of_all μ; intro ω
    have h_nonneg_ω : 0 ≤ f ω :=
      Finset.prod_nonneg (fun i _ => ENNReal.toReal_nonneg (a := ν ω (C i)))
    rw [Real.norm_of_nonneg h_nonneg_ω]
    have h_bound : ∀ i : Fin m, (ν ω (C i)).toReal ≤ 1 := fun i => by
      have h1 : ν ω (C i) ≤ 1 := prob_le_one
      rw [← ENNReal.toReal_one]
      exact (ENNReal.toReal_le_toReal (ne_top_of_le_ne_top ENNReal.one_ne_top h1)
        ENNReal.one_ne_top).mpr h1
    calc f ω ≤ ∏ _i : Fin m, (1 : ℝ) :=
            Finset.prod_le_prod (fun i _ => ENNReal.toReal_nonneg) (fun i _ => h_bound i)
      _ = 1 := by simp
  -- Step 3: Apply ofReal_integral_eq_lintegral_ofReal
  symm
  exact ofReal_integral_eq_lintegral_ofReal h_integrable h_nonneg

/-! #### Core lemmas -/

/-- On a finite index type, product measures evaluate on rectangles as a finite product. -/
lemma measure_pi_univ_pi
    {α : Type*} [MeasurableSpace α] [StandardBorelSpace α]
    {m : ℕ} (μi : Fin m → Measure α) [∀ i, SigmaFinite (μi i)]
    (C : Fin m → Set α) :
  (Measure.pi (fun i : Fin m => μi i)) (Set.univ.pi C)
    = ∏ i : Fin m, μi i (C i) :=
  Measure.pi_pi μi C

/-- Bind computation on rectangles for finite product measures. -/
lemma bind_apply_univ_pi
    {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α] [StandardBorelSpace α]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {m : ℕ}
    (ν : Ω → Measure α) [∀ ω, IsProbabilityMeasure (ν ω)]
    (hν_meas : ∀ (B : Set α), MeasurableSet B → Measurable (fun ω => ν ω B))
    (C : Fin m → Set α) (hC : ∀ i, MeasurableSet (C i)) :
  (μ.bind (fun ω => Measure.pi (fun _ : Fin m => ν ω))) (Set.univ.pi C)
    = ∫⁻ ω, (∏ i : Fin m, ν ω (C i)) ∂μ := by
  -- Step 1: Apply Measure.bind_apply to get LHS = ∫⁻ ω, (Measure.pi ...) (Set.univ.pi C) ∂μ
  -- We need AEMeasurability of the kernel ω ↦ Measure.pi (fun _ => ν ω)
  have h_rect_meas : MeasurableSet (Set.univ.pi C) := by
    classical
    exact MeasurableSet.univ_pi hC

  -- AEMeasurability of the product measure kernel (using MeasureKernels.aemeasurable_measure_pi)
  have h_aemeas : AEMeasurable (fun ω => Measure.pi (fun _ : Fin m => ν ω)) μ :=
    aemeasurable_measure_pi ν (fun ω => inferInstance) hν_meas

  calc (μ.bind (fun ω => Measure.pi (fun _ : Fin m => ν ω))) (Set.univ.pi C)
      = ∫⁻ ω, (Measure.pi (fun _ : Fin m => ν ω)) (Set.univ.pi C) ∂μ :=
          Measure.bind_apply h_rect_meas h_aemeas
    _ = ∫⁻ ω, (∏ i : Fin m, ν ω (C i)) ∂μ := by
          -- Step 2: Use measure_pi_univ_pi to convert the product measure on a rectangle
          congr 1
          funext ω
          exact measure_pi_univ_pi (fun _ => ν ω) C

/-- **Finite product formula for the first m coordinates** (identity case).

This is the core case where we prove the product formula for `(X₀, X₁, ..., X_{m-1})`.
The general case for strictly monotone subsequences reduces to this via contractability.

**Important**: The statement with arbitrary `k : Fin m → ℕ` is **false** if `k` has duplicates
(e.g., `(X₀, X₀)` is not an independent product unless ν is Dirac). We avoid this by:
1. Proving the identity case here (no index map)
2. Reducing strict-monotone subsequences to the identity case via contractability

**Proof strategy:**
1. Show equality on rectangles using factorization machinery
2. Extend from rectangles to full σ-algebra via π-λ theorem -/
lemma finite_product_formula_id
    [StandardBorelSpace Ω]
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
    (m : ℕ) :
    Measure.map (fun ω => fun i : Fin m => X i ω) μ
      = μ.bind (fun ω => Measure.pi fun _ : Fin m => ν ω) := by
  classical
  -- π-system of rectangles in (Fin m → α)
  let Rectangles : Set (Set (Fin m → α)) :=
    {S | ∃ (C : Fin m → Set α), (∀ i, MeasurableSet (C i)) ∧ S = Set.univ.pi C}

  -- Characterization: Rectangles = {S | ∃ B, ...} (used multiple times below)
  have Rectangles_def : Rectangles = {S : Set (Fin m → α) | ∃ (B : Fin m → Set α),
      (∀ i, MeasurableSet (B i)) ∧ S = {x | ∀ i, x i ∈ B i}} := by
    ext S; simp only [Rectangles, Set.mem_setOf_eq]
    constructor <;> (intro ⟨B, hB, hS⟩; refine ⟨B, hB, ?_⟩; rw [hS]; ext x; simp)

  -- 1) Rectangles form a π-system and generate the Π σ-algebra
  have h_pi : IsPiSystem Rectangles := by
    rw [Rectangles_def]; exact rectangles_isPiSystem (m := m) (α := α)

  have h_gen : (inferInstance : MeasurableSpace (Fin m → α))
      = MeasurableSpace.generateFrom Rectangles := by
    rw [Rectangles_def]; exact rectangles_generate_pi_sigma (m := m) (α := α)

  -- 2) Show both measures agree on rectangles
  have h_agree :
    ∀ s ∈ Rectangles,
      (Measure.map (fun ω => fun i : Fin m => X i ω) μ) s
        = (μ.bind (fun ω => Measure.pi fun _ : Fin m => ν ω)) s := by
    rintro s ⟨C, hC, rfl⟩

    -- LHS: map-measure on a rectangle = integral of the product indicator
    have hL :
      (Measure.map (fun ω => fun i : Fin m => X i ω) μ) (Set.univ.pi C)
        = ENNReal.ofReal (∫ ω, indProd X m C ω ∂μ) := by
      -- Preimage of rectangle equals firstRCylinder
      have hpre :
        ((fun ω => fun i : Fin m => X i ω) ⁻¹' (Set.univ.pi C))
          = firstRCylinder X m C := by
        ext ω; simp [firstRCylinder]
      -- indProd equals indicator of firstRCylinder
      have hind := indProd_eq_firstRCylinder_indicator X m C
      -- Measure equals integral via indicator
      have h_meas_eq : μ (firstRCylinder X m C)
          = ENNReal.ofReal (∫ ω, indProd X m C ω ∂μ) := by
        rw [hind]
        -- For probability measure: μ S = ENNReal.ofReal ((μ S).toReal)
        rw [← ENNReal.ofReal_toReal (measure_ne_top μ _)]
        congr 1
        -- ∫ indicator S 1 = Measure.real μ S = (μ S).toReal
        have h_int := @integral_indicator_one _ _ μ (firstRCylinder X m C)
          (firstRCylinder_measurable_ambient X m C hX_meas hC)
        simp only [Measure.real] at h_int
        exact h_int.symm
      -- Apply to map measure
      calc (Measure.map (fun ω => fun i : Fin m => X i ω) μ) (Set.univ.pi C)
          = μ ((fun ω => fun i : Fin m => X i ω) ⁻¹' (Set.univ.pi C)) := by
              -- Standard: (map f μ) S = μ (f⁻¹ S) for measurable f and S
              refine Measure.map_apply ?_ ?_
              · fun_prop (disch := measurability)
              · -- Set.univ.pi C is measurable in product σ-algebra
                classical
                apply MeasurableSet.univ_pi
                exact hC
        _ = μ (firstRCylinder X m C) := by rw [hpre]
        _ = ENNReal.ofReal (∫ ω, indProd X m C ω ∂μ) := h_meas_eq

    -- Use factorization machinery
    have h_fact : ∀ M ≥ m,
        μ[indProd X m C | futureFiltration X M] =ᵐ[μ]
        (fun ω => ∏ i : Fin m,
          μ[Set.indicator (C i) (fun _ => (1:ℝ)) ∘ (X 0) | futureFiltration X M] ω) :=
      fun M hMm => finite_level_factorization X hX hX_meas m C hC M hMm

    -- Reverse martingale convergence for each coordinate
    have h_conv : ∀ i : Fin m,
        (∀ᵐ ω ∂μ, Tendsto (fun M =>
          μ[Set.indicator (C i) (fun _ => (1:ℝ)) ∘ (X 0) | futureFiltration X M] ω)
          atTop
          (𝓝 (μ[Set.indicator (C i) (fun _ => (1:ℝ)) ∘ (X 0) | tailSigma X] ω))) := by
      intro i
      have := Exchangeability.Probability.condExp_tendsto_iInf
        (μ := μ) (𝔽 := futureFiltration X)
        (h_filtration := futureFiltration_antitone X)
        (h_le := fun n => futureFiltration_le X n hX_meas)
        (f := (Set.indicator (C i) (fun _ => (1:ℝ))) ∘ X 0)
        (h_f_int := by
          simpa using
            Exchangeability.Probability.integrable_indicator_comp
              (μ := μ) (X := X 0) (hX := hX_meas 0) (hB := hC i))
      simpa [← tailSigmaFuture_eq_iInf, tailSigmaFuture_eq_tailSigma] using this

    -- Tail factorization for the product indicator (a.e. equality)
    have h_tail : μ[indProd X m C | tailSigma X] =ᵐ[μ]
        (fun ω => ∏ i : Fin m,
          μ[Set.indicator (C i) (fun _ => (1:ℝ)) ∘ (X 0) | tailSigma X] ω) :=
      tail_factorization_from_future X hX_meas m C hC h_fact h_conv

    -- Integrate both sides; tower property: ∫ μ[g|tail] = ∫ g
    -- Tower property: ∫ f = ∫ E[f|τ] and use h_tail
    have h_int_tail : ∫ ω, indProd X m C ω ∂μ
        = ∫ ω, (∏ i : Fin m,
            μ[Set.indicator (C i) (fun _ => (1:ℝ)) ∘ (X 0) | tailSigma X] ω) ∂μ :=
      ((integral_congr_ae h_tail.symm).trans (integral_condExp (tailSigma_le X hX_meas))).symm

    -- Replace each conditional expectation by ν ω (C i).toReal using hν_law
    have h_swap : (fun ω => ∏ i : Fin m,
          μ[Set.indicator (C i) (fun _ => (1:ℝ)) ∘ (X 0) | tailSigma X] ω)
        =ᵐ[μ] (fun ω => ∏ i : Fin m, (ν ω (C i)).toReal) := by
      -- For each coordinate i, we have a.e. equality from hν_law
      have h_each : ∀ i : Fin m,
          (μ[Set.indicator (C i) (fun _ => (1:ℝ)) ∘ (X 0) | tailSigma X])
            =ᵐ[μ] (fun ω => (ν ω (C i)).toReal) :=
        fun i => (hν_law 0 (C i) (hC i)).symm
      -- Combine using Finset.prod over a.e. equal functions
      -- The product of a.e. equal functions is a.e. equal
      have h_all := ae_all_iff.mpr h_each
      filter_upwards [h_all] with ω hω
      -- Both sides are products over Fin m, equal pointwise
      exact Finset.prod_congr rfl (fun i _ => hω i)

    -- RHS (mixture) on rectangle:
    -- (★) — bind on rectangles reduces to a lintegral of a finite product
    have h_bind :
      (μ.bind (fun ω => Measure.pi fun _ : Fin m => ν ω)) (Set.univ.pi C)
        = ∫⁻ ω, (∏ i : Fin m, ν ω (C i)) ∂μ :=
      bind_apply_univ_pi ν hν_meas C hC

    -- (★★) — turn lintegral of a product of ENNReal probabilities into `ofReal` of a real integral
    have h_toReal :
      ∫⁻ ω, (∏ i : Fin m, ν ω (C i)) ∂μ
        = ENNReal.ofReal (∫ ω, (∏ i : Fin m, (ν ω (C i)).toReal) ∂μ) :=
      lintegral_prod_prob_eq_ofReal_integral ν hν_meas C hC

    -- (★★★) — compute mixture on rectangle as `ofReal ∫ …` to match the LHS computation chain
    have hR :
      (μ.bind (fun ω => Measure.pi fun _ : Fin m => ν ω)) (Set.univ.pi C)
        = ENNReal.ofReal (∫ ω, (∏ i : Fin m, (ν ω (C i)).toReal) ∂μ) := by
      rw [h_bind, h_toReal]

    -- (★★★★) — assemble the chain and finish equality on rectangles
    calc (Measure.map (fun ω => fun i : Fin m => X i ω) μ) (Set.univ.pi C)
        = ENNReal.ofReal (∫ ω, indProd X m C ω ∂μ) := hL
      _ = ENNReal.ofReal (∫ ω, (∏ i : Fin m,
            μ[Set.indicator (C i) (fun _ => (1:ℝ)) ∘ (X 0) | tailSigma X] ω) ∂μ) := by
            rw [h_int_tail]
      _ = ENNReal.ofReal (∫ ω, (∏ i : Fin m, (ν ω (C i)).toReal) ∂μ) := by
            congr 1; exact integral_congr_ae h_swap
      _ = (μ.bind (fun ω => Measure.pi fun _ : Fin m => ν ω)) (Set.univ.pi C) := hR.symm

  -- π–λ extension to all measurable sets (your standard pattern)
  -- Both measures are finite (indeed probability); you can either show `univ = 1` on both
  -- or reuse the general "iUnion = univ" cover with `IsFiniteMeasure`.
  have h_univ :
      (Measure.map (fun ω => fun i : Fin m => X i ω) μ) Set.univ
        = (μ.bind (fun ω => Measure.pi fun _ : Fin m => ν ω)) Set.univ := by
    -- both are probabilities
    haveI : IsProbabilityMeasure (Measure.map (fun ω => fun i : Fin m => X i ω) μ) := by
      constructor
      have hme : Measurable (fun ω => fun i : Fin m => X i ω) := by
        fun_prop (disch := measurability)
      rw [Measure.map_apply hme MeasurableSet.univ]
      have : (fun ω => fun i : Fin m => X i ω) ⁻¹' Set.univ = Set.univ := by ext; simp
      rw [this]
      exact measure_univ
    haveI : IsProbabilityMeasure (μ.bind (fun ω => Measure.pi fun _ : Fin m => ν ω)) := by
      constructor
      -- Need to show: (μ.bind (fun ω => Measure.pi fun _ : Fin m => ν ω)) Set.univ = 1
      -- Strategy: bind of constant 1 over probability measure μ equals 1
      -- First need AEMeasurability of the kernel (using MeasureKernels.aemeasurable_measure_pi)
      have h_aemeas : AEMeasurable (fun ω => Measure.pi fun _ : Fin m => ν ω) μ :=
        aemeasurable_measure_pi ν hν_prob hν_meas
      rw [Measure.bind_apply MeasurableSet.univ h_aemeas]
      -- ∫⁻ ω, (Measure.pi (fun _ : Fin m => ν ω)) Set.univ ∂μ
      -- For each ω, Measure.pi is a product of probability measures, so it's a probability measure
      have h_pi_prob : ∀ ω, (Measure.pi (fun _ : Fin m => ν ω)) Set.univ = 1 := fun ω =>
        haveI := hν_prob ω; measure_univ
      -- Integrate constant 1: ∫⁻ ω, 1 ∂μ = 1 * μ Set.univ = 1
      simp only [h_pi_prob]
      rw [lintegral_const]
      simp [measure_univ]
    -- Now both are probability measures, so both equal 1 on univ
    calc (Measure.map (fun ω => fun i : Fin m => X i ω) μ) Set.univ
        = 1 := measure_univ
      _ = (μ.bind (fun ω => Measure.pi fun _ : Fin m => ν ω)) Set.univ := measure_univ.symm

  -- π–λ theorem: equality on the generating π-system + equality on univ ⇒ equality of measures
  -- Since both are probability measures and agree on rectangles, they are equal

  -- Define covering family (constant sequence of Set.univ)
  let Bseq : ℕ → Set (Fin m → α) := fun _ => Set.univ

  have h1B : ⋃ n, Bseq n = Set.univ := by
    simp only [Bseq, Set.iUnion_const]

  have h2B : ∀ n, Bseq n ∈ Rectangles := by
    intro n
    refine ⟨fun _ => Set.univ, fun _ => MeasurableSet.univ, ?_⟩
    ext f; simp only [Bseq, Set.mem_univ, Set.mem_univ_pi]; tauto

  have hμB : ∀ n, Measure.map (fun ω => fun i : Fin m => X i ω) μ (Bseq n) ≠ ⊤ := by
    intro n
    simp only [Bseq]
    exact measure_ne_top _ Set.univ

  -- Apply Measure.ext_of_generateFrom_of_iUnion
  exact Measure.ext_of_generateFrom_of_iUnion
    Rectangles Bseq h_gen h_pi h1B h2B hμB h_agree

/-- **Finite product formula for strictly monotone subsequences**.

For any strictly increasing subsequence `k`, the joint law of `(X_{k(0)}, ..., X_{k(m-1)})`
equals the independent product under the directing measure ν.

This reduces to the identity case via contractability. -/
lemma finite_product_formula_strictMono
    [StandardBorelSpace Ω]
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
    (m : ℕ) (k : Fin m → ℕ) (hk : StrictMono k) :
    Measure.map (fun ω => fun i : Fin m => X (k i) ω) μ
      = μ.bind (fun ω => Measure.pi fun _ : Fin m => ν ω) := by
  classical
  -- Contractability gives equality with the identity map
  calc
    Measure.map (fun ω => fun i : Fin m => X (k i) ω) μ
        = Measure.map (fun ω => fun i : Fin m => X i ω) μ := by simpa using hX m k hk
    _   = μ.bind (fun ω => Measure.pi fun _ : Fin m => ν ω) :=
          finite_product_formula_id X hX hX_meas ν hν_prob hν_meas hν_law m

/-- **Finite product formula** for strictly monotone subsequences.

For any strictly increasing subsequence `k`, the joint law of
`(X_{k(0)}, ..., X_{k(m-1)})` equals the independent product under the
directing measure `ν`. This wraps `finite_product_formula_strictMono`. -/
lemma finite_product_formula
    [StandardBorelSpace Ω]
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
    (m : ℕ) (k : Fin m → ℕ) (hk : StrictMono k) :
  Measure.map (fun ω => fun i : Fin m => X (k i) ω) μ
    = μ.bind (fun ω => Measure.pi fun _ : Fin m => ν ω) :=
  finite_product_formula_strictMono X hX hX_meas ν hν_prob hν_meas hν_law m k hk

/-- **Convenience identity case** (useful for tests and bridging). -/
lemma finite_product_formula_id'
    [StandardBorelSpace Ω]
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
    (m : ℕ) :
  Measure.map (fun ω => fun i : Fin m => X i ω) μ
    = μ.bind (fun ω => Measure.pi fun _ : Fin m => ν ω) :=
  finite_product_formula X hX hX_meas ν hν_prob hν_meas hν_law m (fun i => (i : ℕ))
    fun _ _ => id

end Exchangeability.DeFinetti.ViaMartingale
