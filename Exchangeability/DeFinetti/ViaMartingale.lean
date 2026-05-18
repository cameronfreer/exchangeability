/-
Copyright (c) 2025 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.Probability.ConditionalExpectation
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
import Mathlib.MeasureTheory.MeasurableSpace.Prod
import Mathlib.Probability.Martingale.Basic
import Mathlib.Probability.Kernel.CondDistrib
import Mathlib.Probability.Kernel.Condexp
import Mathlib.Probability.Kernel.Composition.Comp
import Exchangeability.Core
import Exchangeability.Contractability
import Exchangeability.ConditionallyIID
import Exchangeability.Probability.CondExp
import Exchangeability.Probability.CondExpHelpers
import Exchangeability.Probability.CondIndep
import Exchangeability.Probability.Martingale
import Exchangeability.Probability.TripleLawDropInfo
import Exchangeability.Tail.TailSigma
import Exchangeability.DeFinetti.MartingaleHelpers
import Exchangeability.DeFinetti.CommonEnding
import Exchangeability.DeFinetti.ViaMartingale.LocalInfrastructure
import Exchangeability.DeFinetti.ViaMartingale.PairLawEquality
import Exchangeability.DeFinetti.ViaMartingale.ShiftOperations
import Exchangeability.DeFinetti.ViaMartingale.RevFiltration
import Exchangeability.DeFinetti.ViaMartingale.FutureFiltration
import Exchangeability.DeFinetti.ViaMartingale.FutureRectangles
import Exchangeability.DeFinetti.ViaMartingale.FiniteCylinders
import Exchangeability.DeFinetti.ViaMartingale.CondExpConvergence
import Exchangeability.DeFinetti.ViaMartingale.DirectingMeasure
import Exchangeability.DeFinetti.ViaMartingale.IndicatorAlgebra
import Exchangeability.DeFinetti.ViaMartingale.Factorization
import Exchangeability.DeFinetti.ViaMartingale.FiniteProduct
import Exchangeability.Probability.MeasureKernels
import Exchangeability.Probability.ConditionalKernel

/-!
# de Finetti's Theorem via Reverse Martingales

**Aldous' elegant martingale proof** of de Finetti's theorem, as presented in
Kallenberg (2005) as the "third proof". This approach has **medium dependencies**.

**Status**: COMPLETE - 0 sorries in this file. Builds successfully.
Remaining sorries are in helper modules (`TripleLawDropInfo.lean`, `CondIndep.lean`).

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

## Infrastructure Dependencies

This file is complete (0 sorries). Remaining sorries are in helper modules:

- `TripleLawDropInfo.lean` (2 sorries) - Kallenberg Lemma 1.3 kernel uniqueness
- `CondIndep.lean` (5 sorries) - Conditional independence from distributional equality

See `VIAMARTINGALE_BLOCKERS.md` for detailed status.
-/

noncomputable section
open scoped MeasureTheory ProbabilityTheory Topology

namespace Exchangeability
namespace DeFinetti
namespace ViaMartingale

open MeasureTheory Filter
open Exchangeability.DeFinetti.MartingaleHelpers

/-! ### Infrastructure for Test Function Transfer (integral_map + Law Equality) -/

/-- **B1: Bochner integral under Measure.map (Change of variables).**
If `T : Ω → δ` is measurable and `g : δ → ℝ` is integrable w.r.t. `Measure.map T μ`,
then `∫ g ∘ T ∂μ = ∫ g ∂ (Measure.map T μ)`.

This is the Bochner integral analogue of `lintegral_map`. -/
lemma integral_map_eq
    {Ω δ : Type*} [MeasurableSpace Ω] [MeasurableSpace δ]
    {μ : Measure Ω} {T : Ω → δ} (hT : Measurable T)
    {g : δ → ℝ}
    (hg : Integrable g (Measure.map T μ)) :
  ∫ ω, g (T ω) ∂μ = ∫ y, g y ∂ (Measure.map T μ) := by
  -- Use mathlib's change-of-variables formula for Bochner integrals
  symm
  exact MeasureTheory.integral_map hT.aemeasurable hg.aestronglyMeasurable

/-- **B2: Test-function transfer under equality of laws.**
If two pushforward measures coincide, Bochner integrals of any integrable
function coincide. -/
lemma integral_eq_of_map_eq
    {Ω δ : Type*} [MeasurableSpace Ω] [MeasurableSpace δ]
    {μ : Measure Ω} {T T' : Ω → δ}
    (hMeas : Measurable T) (hMeas' : Measurable T')
    {g : δ → ℝ}
    (hg : Integrable g (Measure.map T μ))
    (hLaw : Measure.map T μ = Measure.map T' μ) :
  ∫ ω, g (T ω) ∂μ = ∫ ω, g (T' ω) ∂μ := by
  classical
  -- Use integral_map on both sides and the law equality
  have h1 := integral_map_eq hMeas hg
  have h2 : Integrable g (Measure.map T' μ) := hLaw ▸ hg
  have h3 := integral_map_eq hMeas' h2
  calc ∫ ω, g (T ω) ∂μ
      = ∫ y, g y ∂(Measure.map T μ) := h1
    _ = ∫ y, g y ∂(Measure.map T' μ) := by rw [hLaw]
    _ = ∫ ω, g (T' ω) ∂μ := h3.symm

/-- **Helper:** Generalized test function lemma without ψ factor.

From the pair law (Y,W) =^d (Y,W'), we can swap W and W' for test functions
of the form φ(Y) * g(W), where g : γ → ℝ is a bounded measurable function.

This is the key tool for the "swap back" step in the swap-condition-swap technique,
where we need to handle functions like φ * (v * 1_B)∘W without the ψ factor.

**Proof strategy:** Apply the pair law equality directly to the test function F(y,w) = φ(y)*g(w),
using integral_map to convert between ∫ F∘(Y,W) and ∫ F d[Law(Y,W)].
-/
@[nolint unusedArguments]
lemma test_fn_pair_law
  {Ω α γ : Type*}
  [MeasurableSpace Ω] [MeasurableSpace α] [MeasurableSpace γ]
  {μ : Measure Ω} [IsProbabilityMeasure μ]
  (Y : Ω → α) (W W' : Ω → γ)
  (hY : Measurable Y) (hW : Measurable W) (hW' : Measurable W')
  (h_pair : Measure.map (fun ω => (Y ω, W ω)) μ =
            Measure.map (fun ω => (Y ω, W' ω)) μ)
  (φ : Ω → ℝ) (hφ_factor : ∃ f : α → ℝ, Measurable f ∧ φ = f ∘ Y)
  (hφ_int : Integrable φ μ)
  (g : γ → ℝ) (hg : Measurable g) (hg_bdd : ∀ w, ‖g w‖ ≤ 1) :
  ∫ ω, φ ω * g (W ω) ∂μ = ∫ ω, φ ω * g (W' ω) ∂μ := by
  -- Extract the factorization f with φ = f ∘ Y
  obtain ⟨f, hf, rfl⟩ := hφ_factor

  -- Define the test function on the product space
  let g_test : α × γ → ℝ := fun ⟨y, w⟩ => f y * g w

  -- Measurability
  have hT : Measurable (fun ω => (Y ω, W ω)) := hY.prodMk hW
  have hT' : Measurable (fun ω => (Y ω, W' ω)) := hY.prodMk hW'

  -- g_test is measurable
  have hg_test_meas : Measurable g_test := by
    exact (hf.comp measurable_fst).mul (hg.comp measurable_snd)

  -- Integrability: g_test is bounded by ‖φ‖ (since |g| ≤ 1)
  have hg_test_int : Integrable g_test (Measure.map (fun ω => (Y ω, W ω)) μ) := by
    -- |g_test(y,w)| = |f(y)| * |g(w)| ≤ |f(y)| * 1 = |f(y)|
    -- So ∫ |g_test| d[law(Y,W)] = ∫ |f(Y)| * |g(W)| dμ ≤ ∫ |f(Y)| dμ = ∫ |φ| dμ < ∞
    have h_comp_int : Integrable (g_test ∘ fun ω => (Y ω, W ω)) μ := by
      refine Integrable.mono hφ_int ?_ ?_
      · exact ((hf.comp hY).mul (hg.comp hW)).aestronglyMeasurable
      · filter_upwards with ω
        simp [g_test]
        calc |f (Y ω)| * |g (W ω)|
            ≤ |f (Y ω)| * 1 := by gcongr; exact hg_bdd (W ω)
          _ = |f (Y ω)| := mul_one _
    exact (integrable_map_measure hg_test_meas.aestronglyMeasurable hT.aemeasurable).mpr h_comp_int

  -- Apply integral transfer under law equality
  have h := integral_eq_of_map_eq hT hT' hg_test_int h_pair

  -- Simplify: g_test ∘ (Y,W) = f∘Y * g∘W
  convert h using 1

/-! **Kallenberg Lemma 1.3 (Contraction-Independence)**: If the triple distribution
satisfies (Y, Z, W) =^d (Y, Z, W'), then Y and Z are conditionally independent given W.

This is the key lemma connecting distributional symmetry to conditional independence.

Note: The order (Y, Z, W) matches the natural interpretation where Y is the variable of
interest and (Z, W) provides the conditioning information.

**Proof strategy:** We prove rectangle factorization directly from the distributional equality.

**Mathematical content:** The distributional equality (Y,Z,W) =^d (Y,Z,W') combined with the
implicit "contraction" (W' may contain more information than W) implies that Z provides no
additional information about Y beyond what W provides. This is precisely conditional independence.

**What's needed to complete:** The proof requires showing that for all measurable sets A, B, C
with C ∈ σ(W):
  ∫_C 1_A(Y)·1_B(Z) dμ = (∫_C 1_A(Y)·1_C(W) dμ) · (∫ 1_B(Z)·1_C(W) dμ) / μ(C)

This factorization follows from the distributional equality via a martingale argument
(see Kallenberg 2005, proof of Lemma 1.3) or via conditional distributions.

**Mathlib target:** Mathlib.Probability.ConditionalIndependence.FromDistributionalEquality
-/

/- ===== Helpers: adjointness & indicator algebra (μ[·|m], (hm : m ≤ m0)) ===== -/

/-- Set integral as `1_s · f` (explicit unit indicator), tuned to avoid elaboration blowups. -/
lemma setIntegral_eq_integral_indicator_one_mul
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {s : Set Ω} (hs : MeasurableSet s) {f : Ω → ℝ} :
  ∫ ω in s, f ω ∂μ
  = ∫ ω, (Set.indicator s (fun _ => (1 : ℝ)) ω) * f ω ∂μ := by
  classical
  -- by definition: `∫_s f = ∫ indicator s f`; then identify with `1_s * f`
  have : ∫ ω in s, f ω ∂μ = ∫ ω, Set.indicator s f ω ∂μ :=
    (integral_indicator hs).symm
  refine this.trans ?_
  refine integral_congr_ae ?ae
  filter_upwards with ω
  by_cases hω : ω ∈ s <;> simp [Set.indicator, hω, mul_comm]

/-- If `|g| ≤ C` a.e., then `|μ[g|m]| ≤ C` a.e. (uses monotonicity of conditional expectation). -/
@[nolint unusedArguments]
lemma ae_bound_condexp_of_ae_bound
    {Ω : Type*} [m0 : MeasurableSpace Ω] (μ : Measure Ω)
    {m : MeasurableSpace Ω} (hm : m ≤ m0)
    [SigmaFinite (μ.trim hm)]
    {g : Ω → ℝ} {C : ℝ}
    (hgC : ∀ᵐ ω ∂μ, |g ω| ≤ C) :
  ∀ᵐ ω ∂μ, |μ[g | m] ω| ≤ C := by
  by_cases hC : 0 ≤ C
  · exact MeasureTheory.ae_bdd_condExp_of_ae_bdd (R := ⟨C, hC⟩) hgC
  · -- C < 0 contradicts |g ω| ≤ C since |g ω| ≥ 0
    push_neg at hC
    filter_upwards [hgC] with ω hω
    linarith [abs_nonneg (g ω)]

/-- **Adjointness for bounded `g` (L∞–L¹)**:
If `g` is essentially bounded and `ξ ∈ L¹(μ)`, then
`∫ g · μ[ξ|m] = ∫ μ[g|m] · ξ`.

This avoids the `L¹×L¹` product pitfall by using `L∞` control on `g`,
and the corresponding `L∞` control on `μ[g|m]`. -/
lemma integral_mul_condexp_adjoint_Linfty
    {Ω : Type*} [m0 : MeasurableSpace Ω] (μ : Measure Ω)
    {m : MeasurableSpace Ω} (hm : m ≤ m0)
    [SigmaFinite (μ.trim hm)]
    {g ξ : Ω → ℝ} {C : ℝ}
    (hgC : ∀ᵐ ω ∂μ, |g ω| ≤ C)
    (hg : Integrable g μ)
    (hξ : Integrable ξ μ) :
  ∫ ω, g ω * μ[ξ | m] ω ∂μ
  = ∫ ω, μ[g | m] ω * ξ ω ∂μ := by
  classical
  -- Both products are integrable
  have h_int1 : Integrable (fun ω => g ω * μ[ξ | m] ω) μ :=
    Integrable.bdd_mul (MeasureTheory.integrable_condExp (m := m) (f := ξ))
      hg.aestronglyMeasurable hgC
  have hμgC : ∀ᵐ ω ∂μ, |μ[g | m] ω| ≤ C :=
    @ae_bound_condexp_of_ae_bound Ω m0 μ m hm _ _ _ hgC
  have h_int2 : Integrable (fun ω => μ[g | m] ω * ξ ω) μ :=
    Integrable.bdd_mul hξ
      (MeasureTheory.integrable_condExp (m := m) (f := g)).aestronglyMeasurable hμgC

  -- Now copy the "adjointness by CE" argument, which is safe since both products are L¹.
  have h1 :
      ∫ ω, g ω * μ[ξ | m] ω ∂μ
    = ∫ ω, μ[(fun ω => g ω * μ[ξ | m] ω) | m] ω ∂μ := by
      simpa using (MeasureTheory.integral_condExp (μ := μ) (m := m) (hm := hm)
        (f := fun ω => g ω * μ[ξ | m] ω)).symm
  have hpull :
      μ[(fun ω => g ω * μ[ξ | m] ω) | m]
      =ᵐ[μ] (fun ω => μ[g | m] ω * μ[ξ | m] ω) := by
    -- pull out the `m`-measurable factor `μ[ξ|m]`
    have hξm :
        AEStronglyMeasurable[m] (μ[ξ | m]) μ :=
      MeasureTheory.stronglyMeasurable_condExp.aestronglyMeasurable
    -- Rewrite to match pull-out lemma signature (measurable factor on right)
    have h_comm : (fun ω => g ω * μ[ξ | m] ω) = (fun ω => μ[ξ | m] ω * g ω) := by
      ext ω; ring
    rw [h_comm]
    have h_int_comm : Integrable (fun ω => μ[ξ | m] ω * g ω) μ := by
      convert h_int1 using 1; ext ω; ring
    have h_pull := MeasureTheory.condExp_mul_of_aestronglyMeasurable_left hξm h_int_comm hg
    -- The lemma gives μ[ξ|m] * μ[g|m], but we need μ[g|m] * μ[ξ|m]
    filter_upwards [h_pull] with ω hω
    simp only [Pi.mul_apply] at hω ⊢
    rw [mul_comm]
    exact hω
  have h3 :
      ∫ ω, μ[g | m] ω * μ[ξ | m] ω ∂μ
    = ∫ ω, μ[(fun ω => μ[g | m] ω * ξ ω) | m] ω ∂μ := by
    -- reverse pull-out (now pull out `μ[g|m]`)
    have hgm :
        AEStronglyMeasurable[m] (μ[g | m]) μ :=
      MeasureTheory.stronglyMeasurable_condExp.aestronglyMeasurable
    have hpull' :
        μ[(fun ω => μ[g | m] ω * ξ ω) | m]
        =ᵐ[μ] (fun ω => μ[g | m] ω * μ[ξ | m] ω) := by
      exact MeasureTheory.condExp_mul_of_aestronglyMeasurable_left hgm h_int2 hξ
    simpa using (integral_congr_ae hpull').symm
  have h4 :
      ∫ ω, μ[(fun ω => μ[g | m] ω * ξ ω) | m] ω ∂μ
    = ∫ ω, μ[g | m] ω * ξ ω ∂μ := by
    -- Kill α/β noise by naming the product once and for all
    set F : Ω → ℝ := fun ω => μ[g | m] ω * ξ ω with hF

    -- Apply the CE integral identity to F (and orient it the way we need)
    have h_goal :
        ∫ (ω : Ω), μ[g | m] ω * ξ ω ∂μ
      = ∫ (ω : Ω), μ[(fun ω => μ[g | m] ω * ξ ω) | m] ω ∂μ := by
      simpa [hF] using
        (MeasureTheory.integral_condExp (μ := μ) (m := m) (hm := hm) (f := F)).symm

    exact h_goal.symm

  calc
    ∫ ω, g ω * μ[ξ | m] ω ∂μ
        = ∫ ω, μ[(fun ω => g ω * μ[ξ | m] ω) | m] ω ∂μ := h1
    _   = ∫ ω, μ[g | m] ω * μ[ξ | m] ω ∂μ := (integral_congr_ae hpull)
    _   = ∫ ω, μ[(fun ω => μ[g | m] ω * ξ ω) | m] ω ∂μ := h3
    _   = ∫ ω, μ[g | m] ω * ξ ω ∂μ := h4

-- Utility lemmas for indicator-set integral conversion
@[nolint unusedArguments]
lemma indicator_comp_preimage_one
  {Ω S : Type*} [MeasurableSpace S] {W : Ω → S} {T : Set S} :
  (fun ω => Set.indicator T (fun _ : S => (1 : ℝ)) (W ω))
  =
  Set.indicator (W ⁻¹' T) (fun _ : Ω => (1 : ℝ)) := by
  funext ω
  by_cases h : W ω ∈ T <;> simp [Set.indicator_of_mem, Set.indicator_of_notMem, h]

lemma integral_mul_indicator_to_set {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
  {S : Set Ω} (hS : MeasurableSet S) (f : Ω → ℝ) :
  ∫ ω, f ω * Set.indicator S (fun _ : Ω => (1 : ℝ)) ω ∂ μ
  = ∫ ω in S, f ω ∂ μ := by
  have : (fun ω => f ω * Set.indicator S (fun _ : Ω => (1 : ℝ)) ω) = S.indicator f := by
    funext ω; by_cases h : ω ∈ S <;> simp [h]
  simp [this, integral_indicator, hS]

/- DELETED: The following two lemmas are unused in this file.
   The stronger rectangle-based lemma `condexp_indicator_eq_of_agree_on_future_rectangles`
   from CondExp.lean provides the needed functionality.

/-- **Lemma 1.3 (contraction and independence).**

If `(ξ, η) =^d (ξ, ζ)` and `σ(η) ⊆ σ(ζ)`, then `ξ ⊥⊥_η ζ`.
[Proof sketch omitted - would use L² martingale argument]
*Kallenberg (2005), Lemma 1.3.* -/
-- lemma contraction_independence ... -- OMITTED (proof sketch available)

/-- If `(ξ,η)` and `(ξ,ζ)` have the same law and `σ(η) ≤ σ(ζ)`,
then for all measurable `B`, the conditional expectations of `1_{ξ∈B}` coincide.
[Proof sketch omitted - would use L² norm comparison] -/
-- lemma condexp_indicator_eq_of_dist_eq_and_le ... -- OMITTED (proof sketch available)
-/

-- FutureCylinders, FirstBlockCylinder, IndicatorAlgebra, FutureRectangles sections
-- have been extracted to MartingaleHelpers.lean and ViaMartingale/FutureRectangles.lean

variable {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]


-- FiniteCylinders content (finFutureSigma, contractable_finite_cylinder_measure, etc.)
-- has been extracted to ViaMartingale/FiniteCylinders.lean

variable {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]

-- Note: condexp_indicator_drop_info_of_pair_law_direct and condexp_indicator_drop_info_of_pair_law
-- have been extracted to ViaMartingale/DropInfo.lean

-- Note: block_coord_condIndep, condexp_indicator_inter_of_condIndep,
-- finite_level_factorization, and tail_factorization_from_future
-- have been extracted to ViaMartingale/Factorization.lean

-- Note: measure_pi_univ_pi, bind_apply_univ_pi, finite_product_formula_id,
-- finite_product_formula_strictMono, finite_product_formula, and finite_product_formula_id'
-- have been extracted to ViaMartingale/FiniteProduct.lean

/-! ### Main Theorem: de Finetti via Reverse Martingales -/

section MainTheorem

open ProbabilityTheory

/-- **Mixture representation on every finite block** (strict‑mono version)
using the canonical directing measure.

This is the key infrastructure lemma that assembles all the pieces:
- `directingMeasure` with its probability and measurability properties
- `conditional_law_eq_directingMeasure` extending X₀-marginal to all coordinates
- `finite_product_formula` for the strict-mono product identity

The public-facing theorem `deFinetti_viaMartingale` is in `TheoremViaMartingale.lean`. -/
lemma finite_product_formula_with_directing
    {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {α : Type*} [MeasurableSpace α] [StandardBorelSpace α] [Nonempty α]
    (X : ℕ → Ω → α) (hX : Contractable μ X) (hX_meas : ∀ n, Measurable (X n))
    (m : ℕ) (k : Fin m → ℕ) (hk : StrictMono k) :
  Measure.map (fun ω => fun i : Fin m => X (k i) ω) μ
    = μ.bind (fun ω => Measure.pi fun _ : Fin m => directingMeasure (μ := μ) X hX_meas ω) := by
  classical
  -- Assemble the hypotheses required by `finite_product_formula`.
  have hν_prob : ∀ ω, IsProbabilityMeasure (directingMeasure (μ := μ) X hX_meas ω) :=
    directingMeasure_isProb (μ := μ) X hX_meas
  have hν_meas :
      ∀ B : Set α, MeasurableSet B →
        Measurable (fun ω => directingMeasure (μ := μ) X hX_meas ω B) :=
    directingMeasure_measurable_eval (μ := μ) X hX_meas
  -- X₀ marginal identity → all coordinates via conditional_law_eq_directingMeasure
  have hν_law :
      ∀ n B, MeasurableSet B →
        (fun ω => (directingMeasure (μ := μ) X hX_meas ω B).toReal)
          =ᵐ[μ]
        μ[Set.indicator B (fun _ => (1 : ℝ)) ∘ (X n) | tailSigma X] := by
    intro n B hB
    exact conditional_law_eq_directingMeasure (μ := μ) X hX hX_meas n B hB
  -- Now invoke finite_product_formula wrapper.
  exact finite_product_formula X hX hX_meas
    (directingMeasure (μ := μ) X hX_meas) hν_prob hν_meas hν_law m k hk

end MainTheorem

/-!
## Notes

The main de Finetti theorem using this machinery is in `TheoremViaMartingale.lean`.
This file provides the proof infrastructure (helper lemmas and constructions).
-/

end ViaMartingale
end DeFinetti
end Exchangeability
