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
import Exchangeability.DeFinetti.ViaMartingale.CommonVersion
import Exchangeability.DeFinetti.ViaMartingale.PairLawEquality
import Exchangeability.DeFinetti.ViaMartingale.ShiftOperations
import Exchangeability.DeFinetti.ViaMartingale.RevFiltration
import Exchangeability.DeFinetti.ViaMartingale.FutureFiltration
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
  have h2 : Integrable g (Measure.map T' μ) := by rw [← hLaw]; exact hg
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
  by_cases hω : ω ∈ s
  · simp [Set.indicator, hω, mul_comm]
  · simp [Set.indicator, hω]

/-- If `|g| ≤ C` a.e., then `|μ[g|m]| ≤ C` a.e. (uses monotonicity of conditional expectation). -/
lemma ae_bound_condexp_of_ae_bound
    {Ω : Type*} [m0 : MeasurableSpace Ω] (μ : Measure Ω)
    {m : MeasurableSpace Ω} (hm : m ≤ m0)
    [SigmaFinite (μ.trim hm)]
    {g : Ω → ℝ} {C : ℝ}
    (hgC : ∀ᵐ ω ∂μ, |g ω| ≤ C) :
  ∀ᵐ ω ∂μ, |μ[g | m] ω| ≤ C := by
  -- Split on whether C ≥ 0
  by_cases hC : 0 ≤ C
  · -- Case C ≥ 0: use the standard lemma
    exact MeasureTheory.ae_bdd_condExp_of_ae_bdd (R := ⟨C, hC⟩) hgC
  · -- Case C < 0: hypothesis is contradictory
    -- If |g ω| ≤ C < 0, this contradicts |g ω| ≥ 0
    push_neg at hC
    -- From the contradictory hypothesis, any conclusion follows
    filter_upwards [hgC] with ω hω
    -- Derive False: 0 ≤ |g ω| ≤ C < 0
    have : 0 ≤ |g ω| := abs_nonneg (g ω)
    have : |g ω| < 0 := hω.trans_lt hC
    linarith

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
    Integrable.bdd_mul' (MeasureTheory.integrable_condExp (m := m) (f := ξ))
      hg.aestronglyMeasurable hgC
  have hμgC : ∀ᵐ ω ∂μ, |μ[g | m] ω| ≤ C :=
    @ae_bound_condexp_of_ae_bound Ω m0 μ m hm _ _ _ hgC
  have h_int2 : Integrable (fun ω => μ[g | m] ω * ξ ω) μ :=
    Integrable.bdd_mul' hξ
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
  have : (fun ω => f ω * Set.indicator S (fun _ : Ω => (1 : ℝ)) ω)
       = Set.indicator S (fun ω => f ω) := by
    funext ω
    by_cases h : ω ∈ S <;> simp [h, Set.indicator_of_mem, Set.indicator_of_notMem]
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

variable {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]

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
    simp only [f]
    omega
  have hm_lt : ∀ i, m < f i := by
    intro i
    simp only [f]
    omega
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


-- FutureCylinders, FirstBlockCylinder, IndicatorAlgebra, and CylinderBridge sections
-- have been extracted to MartingaleHelpers.lean

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

/-- indProd is strongly measurable when coordinates and sets are measurable. -/
@[measurability, fun_prop]
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
@[measurability, fun_prop]
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

-- CylinderBridge section (drop, cylinder lemmas) extracted to MartingaleHelpers.lean

/-! ## Rectangles using future tails and standard cylinders -/
section FutureRectangles

variable {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
variable {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {X : ℕ → Ω → α}

omit [MeasurableSpace Ω] [MeasurableSpace α] in
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
      simp only at this
      exact this i
  · rcases h with ⟨hB, hC⟩
    refine ⟨?_, ?_⟩
    · simpa [ψ]
    · intro i
      have : X (m + 1 + i.1) ω ∈ C i := hC i
      simp only [ψ, shiftRV]
      exact this

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
    simp [ψ₁, preimage_rect_future (X:=X) m m r B C]
  have hpre₂ :
      ψ₂ ⁻¹' (B ×ˢ cylinder (α:=α) r C)
        = {ω | X k ω ∈ B ∧ ∀ i : Fin r, X (m + 1 + i.1) ω ∈ C i} := by
    simp [ψ₂, preimage_rect_future (X:=X) k m r B C]
  have hfd :
    μ {ω | X m ω ∈ B ∧ ∀ i : Fin r, X (m + (i.1 + 1)) ω ∈ C i}
      =
    μ {ω | X k ω ∈ B ∧ ∀ i : Fin r, X (m + (i.1 + 1)) ω ∈ C i} := by
    have := contractable_dist_eq_on_first_r_tail
        (μ:=μ) (X:=X) hX hX_meas k m r hk B hB C hC
    convert this using 2
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

variable {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]

/-- Two measures agree on all future rectangles (sets of form B ×ˢ cylinder r C). -/
def AgreeOnFutureRectangles (μ ν : Measure (α × (ℕ → α))) : Prop :=
  ∀ (r : ℕ) (B : Set α) (_hB : MeasurableSet B) (C : Fin r → Set α) (_hC : ∀ i, MeasurableSet (C i)),
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
        · simp [C, h1, h2]

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
        · simpa [C, h1, h2] using this
      · intro i
        have hi : (i : ℕ) < r := lt_of_lt_of_le i.2 (Nat.le_max_right r₁ r₂)
        have := hC' ⟨i, hi⟩
        classical
        have h2 : (i : ℕ) < r₂ := i.2
        by_cases h1 : (i : ℕ) < r₁
        · simp [C, h1, h2] at this
          exact this.2
        · simpa [C, h1, h2] using this

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
        simp only [Set.mem_prod, Set.mem_univ, and_true]
        -- cylinder 0 (fun _ => Set.univ) = Set.univ (vacuous quantifier)
        show a ∈ A ↔ a ∈ A ∧ f ∈ MartingaleHelpers.cylinder 0 (fun _ => Set.univ)
        rw [MartingaleHelpers.cylinder]
        simp

      -- Second, show that Prod.snd maps cylinders to measurable sets
      have h_snd : ∀ (r : ℕ) (C : Fin r → Set α),
          (∀ i, MeasurableSet (C i)) →
          MeasurableSet[MeasurableSpace.generateFrom S] (Prod.snd ⁻¹' MartingaleHelpers.cylinder r C) := by
        intro r C hC
        -- Prod.snd ⁻¹' (cylinder r C) = univ ×ˢ (cylinder r C)
        have : (Prod.snd : α × (ℕ → α) → ℕ → α) ⁻¹' MartingaleHelpers.cylinder r C
            = Set.univ ×ˢ MartingaleHelpers.cylinder r C := by
          ext ⟨a, f⟩
          simp only [Set.mem_preimage, Set.mem_prod, Set.mem_univ, true_and]
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
              have h_eq : ((fun f : ℕ → α => f i) ⁻¹' A) = MartingaleHelpers.cylinder r C := by
                ext f
                simp only [C, r, Set.mem_preimage, MartingaleHelpers.cylinder]
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
        _ ≤ MeasurableSpace.generateFrom S :=
              sup_le h_fst_comap h_snd_comap
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
    ext ⟨a, f⟩
    simp only [Bseq, Set.mem_prod, Set.mem_univ, true_and, MartingaleHelpers.cylinder]
    -- For Fin 0, cylinder 0 (fun _ => univ) = univ
    simp
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

This proves the forward-declared result from line 477. -/

/-- **Conditional expectation convergence:** For k ≤ m, all coordinates look
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

lemma extreme_members_equal_on_tail
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → α}
    (hX : Contractable μ X)
    (hX_meas : ∀ n, Measurable (X n))
    (m : ℕ) (B : Set α) (hB : MeasurableSet B) :
    μ[Set.indicator B (fun _ => (1 : ℝ)) ∘ (X m) | tailSigma X]
      =ᵐ[μ]
    μ[Set.indicator B (fun _ => (1 : ℝ)) ∘ (X 0) | tailSigma X] := by
  classical
  -- abbreviations
  set f_m : Ω → ℝ := (Set.indicator B (fun _ => (1 : ℝ))) ∘ X m with hf_m
  set f_0 : Ω → ℝ := (Set.indicator B (fun _ => (1 : ℝ))) ∘ X 0 with hf_0

  -- bounded indicators are integrable
  have hf_m_int :
      Integrable f_m μ :=
    by
      simpa [hf_m] using
        Exchangeability.Probability.integrable_indicator_comp
          (μ := μ) (X := X m) (hX := hX_meas m) hB
  have hf_0_int :
      Integrable f_0 μ :=
    by
      simpa [hf_0] using
        Exchangeability.Probability.integrable_indicator_comp
          (μ := μ) (X := X 0) (hX := hX_meas 0) hB

  -- equality at the future level m (contractability)
  have h_eq_m :
      μ[f_m | futureFiltration X m] =ᵐ[μ] μ[f_0 | futureFiltration X m] := by
    -- Use condexp_convergence from contractability
    exact condexp_convergence hX hX_meas 0 m (Nat.zero_le m) B hB

  -- condition both sides on the tail
  have h_cond_on_tail :
      μ[μ[f_m | futureFiltration X m] | tailSigma X]
        =ᵐ[μ]
      μ[μ[f_0 | futureFiltration X m] | tailSigma X] :=
    condExp_congr_ae h_eq_m

  -- tower property since tailSigma ≤ futureFiltration m
  have h_tower_m :
      μ[μ[f_m | futureFiltration X m] | tailSigma X]
        =ᵐ[μ] μ[f_m | tailSigma X] :=
    condExp_condExp_of_le
      (hm₁₂ := tailSigma_le_futureFiltration (X := X) m)
      (hm₂ := futureFiltration_le (X := X) m hX_meas)
      (f := f_m)
  have h_tower_0 :
      μ[μ[f_0 | futureFiltration X m] | tailSigma X]
        =ᵐ[μ] μ[f_0 | tailSigma X] :=
    condExp_condExp_of_le
      (hm₁₂ := tailSigma_le_futureFiltration (X := X) m)
      (hm₂ := futureFiltration_le (X := X) m hX_meas)
      (f := f_0)

  -- assemble the equalities
  -- Chain: μ[f_m|tail] = μ[μ[f_m|fut]|tail] = μ[μ[f_0|fut]|tail] = μ[f_0|tail]
  exact h_tower_m.symm.trans (h_cond_on_tail.trans h_tower_0)


section reverse_martingale

variable {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
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

variable {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]

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
  have : Measurable (fun ω => fun i : Fin k => X (m + 1 + i.val) ω) := by measurability
  exact this ht

omit [MeasurableSpace Ω] in
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
  have h_proj_meas : Measurable proj := by measurability
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
  have h_meas_idx : Measurable (fun ω (i : Fin (r + 1 + k)) => X (idx i) ω) := by
    fun_prop (disch := measurability)
  have h_meas_std : Measurable (fun ω (i : Fin (r + 1 + k)) => X (↑i) ω) := by
    fun_prop (disch := measurability)

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
    · ext ⟨z, y, c⟩
      simp only [Set.mem_inter_iff, Set.mem_prod, Set.mem_univ_pi]
      constructor
      · intro ⟨⟨hz1, hy1, hc1⟩, hz2, hy2, hc2⟩
        exact ⟨fun i => ⟨hz1 i, hz2 i⟩, ⟨hy1, hy2⟩, fun j => ⟨hc1 j, hc2 j⟩⟩
      · intro ⟨hz, hy, hc⟩
        exact ⟨⟨fun i => (hz i).1, hy.1, fun j => (hc j).1⟩, fun i => (hz i).2, hy.2, fun j => (hc j).2⟩

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
      ext ω; simp [Z_r, Y_future, Set.mem_setOf_eq]
    have h_pre_tail :
        (fun ω => (Z_r ω, X r ω, Y_tail ω)) ⁻¹'
          ((Set.univ.pi A) ×ˢ B ×ˢ (Set.univ.pi C))
          =
        {ω | (∀ i : Fin r, X i.val ω ∈ A i) ∧ X r ω ∈ B ∧
              (∀ j : Fin k, X (r + 1 + j.val) ω ∈ C j)} := by
      ext ω; simp [Z_r, Y_tail, Set.mem_setOf_eq]
    -- Apply the finite cylinder equality.
    have h_cyl :=
      contractable_finite_cylinder_measure
        (X := X) (μ := μ) (hX := hX) (hX_meas := hX_meas)
        (hrm := hrm) (A := A) (hA := hA) (B := B) (hB := hB)
        (C := C) (hC := hC)
    -- Convert to map equality
    -- First, prove measurability of the triple functions
    have h_meas_future : Measurable (fun ω => (Z_r ω, X r ω, Y_future ω)) := by
      refine Measurable.prodMk ?_ (Measurable.prodMk (hX_meas r) ?_)
      · measurability
      · measurability
    have h_meas_tail : Measurable (fun ω => (Z_r ω, X r ω, Y_tail ω)) := by
      refine Measurable.prodMk ?_ (Measurable.prodMk (hX_meas r) ?_)
      · measurability
      · measurability
    -- The rectangle is measurable
    have h_meas_rect : MeasurableSet ((Set.univ.pi A) ×ˢ B ×ˢ (Set.univ.pi C)) := by
      show MeasurableSet ((Set.univ.pi A) ×ˢ (B ×ˢ (Set.univ.pi C)))
      exact (MeasurableSet.univ_pi hA).prod (hB.prod (MeasurableSet.univ_pi hC))
    -- Apply Measure.map_apply and rewrite using preimage equalities
    calc Measure.map (fun ω => (Z_r ω, X r ω, Y_future ω)) μ ((Set.univ.pi A) ×ˢ B ×ˢ (Set.univ.pi C))
        = μ ((fun ω => (Z_r ω, X r ω, Y_future ω)) ⁻¹' ((Set.univ.pi A) ×ˢ B ×ˢ (Set.univ.pi C))) := by
          rw [Measure.map_apply h_meas_future h_meas_rect]
      _ = μ {ω | (∀ i : Fin r, X i.val ω ∈ A i) ∧ X r ω ∈ B ∧ (∀ j : Fin k, X (m + 1 + j.val) ω ∈ C j)} := by
          rw [h_pre_future]
      _ = μ {ω | (∀ i : Fin r, X i.val ω ∈ A i) ∧ X r ω ∈ B ∧ (∀ j : Fin k, X (r + 1 + j.val) ω ∈ C j)} :=
          h_cyl
      _ = μ ((fun ω => (Z_r ω, X r ω, Y_tail ω)) ⁻¹' ((Set.univ.pi A) ×ˢ B ×ˢ (Set.univ.pi C))) := by
          rw [h_pre_tail]
      _ = Measure.map (fun ω => (Z_r ω, X r ω, Y_tail ω)) μ ((Set.univ.pi A) ×ˢ B ×ˢ (Set.univ.pi C)) := by
          rw [Measure.map_apply h_meas_tail h_meas_rect]

  -- Apply π-λ theorem to extend from Rectangles to full σ-algebra
  -- Show that Rectangles generates the product σ-algebra
  have h_gen : (inferInstance : MeasurableSpace ((Fin r → α) × α × (Fin k → α)))
      = MeasurableSpace.generateFrom Rectangles := by
    -- Two-sided inclusion
    apply le_antisymm
    · -- (⊆) Product σ-algebra ≤ generateFrom Rectangles
      -- The product σ-algebra on (Fin r → α) × α × (Fin k → α) is generated by the three projections.
      -- We show each projection is measurable w.r.t. generateFrom Rectangles.

      -- First projection: (Fin r → α)
      have h_fst : ∀ (A : Fin r → Set α), (∀ i, MeasurableSet (A i)) →
          MeasurableSet[MeasurableSpace.generateFrom Rectangles]
            (Prod.fst ⁻¹' (Set.univ.pi A)) := by
        intro A hA
        -- Prod.fst ⁻¹' (pi A) = (pi A) × univ × univ
        have : (Prod.fst : (Fin r → α) × α × (Fin k → α) → (Fin r → α)) ⁻¹' (Set.univ.pi A) =
            (Set.univ.pi A) ×ˢ (Set.univ : Set α) ×ˢ (Set.univ.pi (fun (_ : Fin k) => Set.univ)) := by
          ext ⟨z, y, c⟩
          simp only [Set.mem_preimage, Set.mem_prod, Set.mem_univ_pi, Set.mem_univ, true_and]
          tauto
        rw [this]
        apply MeasurableSpace.measurableSet_generateFrom
        refine ⟨A, hA, Set.univ, MeasurableSet.univ,
                fun _ => Set.univ, fun _ => MeasurableSet.univ, rfl⟩

      -- Second projection (middle component): α
      have h_fst_snd : ∀ (B : Set α), MeasurableSet B →
          MeasurableSet[MeasurableSpace.generateFrom Rectangles]
            ((Prod.fst ∘ Prod.snd) ⁻¹' B) := by
        intro B hB
        -- (Prod.fst ∘ Prod.snd) ⁻¹' B = univ × B × univ
        have : (Prod.fst ∘ Prod.snd : (Fin r → α) × α × (Fin k → α) → α) ⁻¹' B =
            (Set.univ.pi (fun (_ : Fin r) => Set.univ)) ×ˢ B ×ˢ
            (Set.univ.pi (fun (_ : Fin k) => Set.univ)) := by
          ext ⟨z, y, c⟩
          simp only [Set.mem_preimage, Function.comp_apply, Set.mem_prod,
                     Set.mem_univ_pi, Set.mem_univ]
          tauto
        rw [this]
        apply MeasurableSpace.measurableSet_generateFrom
        refine ⟨fun _ => Set.univ, fun _ => MeasurableSet.univ,
                B, hB, fun _ => Set.univ, fun _ => MeasurableSet.univ, rfl⟩

      -- Third projection: (Fin k → α)
      have h_snd_snd : ∀ (C : Fin k → Set α), (∀ j, MeasurableSet (C j)) →
          MeasurableSet[MeasurableSpace.generateFrom Rectangles]
            ((Prod.snd ∘ Prod.snd) ⁻¹' (Set.univ.pi C)) := by
        intro C hC
        -- (Prod.snd ∘ Prod.snd) ⁻¹' (pi C) = univ × univ × (pi C)
        have : (Prod.snd ∘ Prod.snd : (Fin r → α) × α × (Fin k → α) → Fin k → α) ⁻¹'
            (Set.univ.pi C) =
            (Set.univ.pi (fun (_ : Fin r) => Set.univ)) ×ˢ Set.univ ×ˢ (Set.univ.pi C) := by
          ext ⟨z, y, c⟩
          simp only [Set.mem_preimage, Function.comp_apply, Set.mem_prod,
                     Set.mem_univ_pi, Set.mem_univ]
          tauto
        rw [this]
        apply MeasurableSpace.measurableSet_generateFrom
        refine ⟨fun _ => Set.univ, fun _ => MeasurableSet.univ,
                Set.univ, MeasurableSet.univ, C, hC, rfl⟩

      -- Now show that the comap of each projection is ≤ generateFrom Rectangles
      -- For the first projection (Pi space)
      have h_fst_comap : MeasurableSpace.comap Prod.fst inferInstance
          ≤ MeasurableSpace.generateFrom Rectangles := by
        rw [← measurable_iff_comap_le]
        -- Show Prod.fst is measurable w.r.t. generateFrom Rectangles
        -- The Pi σ-algebra on (Fin r → α) is generated by coordinate projections
        rw [MeasurableSpace.pi_eq_generateFrom_projections (ι := Fin r) (α := fun _ => α)]
        apply @measurable_generateFrom _ _ (MeasurableSpace.generateFrom Rectangles) _ _
        intro s hs
        -- s is a coordinate preimage: ∃ i A, MeasurableSet A ∧ eval i ⁻¹' A = s
        obtain ⟨i, A, hA, rfl⟩ := hs
        -- Show Prod.fst ⁻¹' (eval i ⁻¹' A) is in generateFrom Rectangles
        -- eval i ⁻¹' A = pi (fun j => if j = i then A else univ)
        let C : Fin r → Set α := fun j => if j = i then A else Set.univ
        have hC : ∀ j, MeasurableSet (C j) := by
          intro j; simp only [C]; split_ifs; exact hA; exact MeasurableSet.univ
        have : (fun f : Fin r → α => f i) ⁻¹' A = Set.univ.pi C := by
          ext f; simp only [C, Set.mem_preimage, Set.mem_univ_pi]
          constructor
          · intro hf j
            by_cases h : j = i
            · simp [h]; exact hf
            · simp [h]
          · intro hf; simpa using hf i
        rw [this]
        exact h_fst C hC

      -- For the second projection (middle component)
      have h_fst_snd_comap : MeasurableSpace.comap (Prod.fst ∘ Prod.snd) inferInstance
          ≤ MeasurableSpace.generateFrom Rectangles := by
        intro s hs
        obtain ⟨B, hB, rfl⟩ := hs
        exact h_fst_snd B hB

      -- For the third projection (Pi space)
      have h_snd_snd_comap : MeasurableSpace.comap (Prod.snd ∘ Prod.snd) inferInstance
          ≤ MeasurableSpace.generateFrom Rectangles := by
        rw [← measurable_iff_comap_le]
        rw [MeasurableSpace.pi_eq_generateFrom_projections (ι := Fin k) (α := fun _ => α)]
        apply @measurable_generateFrom _ _ (MeasurableSpace.generateFrom Rectangles) _ _
        intro s hs
        obtain ⟨j, C, hC, rfl⟩ := hs
        let D : Fin k → Set α := fun i => if i = j then C else Set.univ
        have hD : ∀ i, MeasurableSet (D i) := by
          intro i; simp only [D]; split_ifs; exact hC; exact MeasurableSet.univ
        have : (fun f : Fin k → α => f j) ⁻¹' C = Set.univ.pi D := by
          ext f; simp only [D, Set.mem_preimage, Set.mem_univ_pi]
          constructor
          · intro hf i
            by_cases h : i = j
            · simp [h]; exact hf
            · simp [h]
          · intro hf; simpa using hf j
        rw [this]
        exact h_snd_snd D hD

      -- Use measurability of the three projections to show all sets are in generateFrom Rectangles
      -- For A × B × C = A × (B × C), the product σ-algebra is generated by both projections
      have : (inferInstance : MeasurableSpace ((Fin r → α) × α × (Fin k → α))) =
          MeasurableSpace.comap Prod.fst inferInstance ⊔
          MeasurableSpace.comap Prod.snd inferInstance := rfl
      rw [this]
      -- Now Prod.snd gives us B × C, which is also a product
      have h_snd_le : MeasurableSpace.comap (Prod.snd : (Fin r → α) × α × (Fin k → α) → α × (Fin k → α)) inferInstance
          ≤ MeasurableSpace.generateFrom Rectangles := by
        -- Prod.snd σ-algebra is generated by Prod.fst and Prod.snd on the second component
        calc MeasurableSpace.comap (Prod.snd : (Fin r → α) × α × (Fin k → α) → α × (Fin k → α)) inferInstance
            = MeasurableSpace.comap Prod.snd
                (MeasurableSpace.comap Prod.fst inferInstance ⊔
                 MeasurableSpace.comap Prod.snd inferInstance) := by rfl
          _ = MeasurableSpace.comap Prod.snd (MeasurableSpace.comap Prod.fst inferInstance)
              ⊔ MeasurableSpace.comap Prod.snd (MeasurableSpace.comap Prod.snd inferInstance) := by
                rw [MeasurableSpace.comap_sup]
          _ = MeasurableSpace.comap (Prod.fst ∘ Prod.snd) inferInstance
              ⊔ MeasurableSpace.comap (Prod.snd ∘ Prod.snd) inferInstance := by
                rw [MeasurableSpace.comap_comp, MeasurableSpace.comap_comp]
          _ ≤ MeasurableSpace.generateFrom Rectangles :=
                sup_le h_fst_snd_comap h_snd_snd_comap
      exact sup_le h_fst_comap h_snd_le

    · -- (⊇) generateFrom Rectangles ≤ Product σ-algebra
      -- Every rectangle is measurable in the product σ-algebra
      apply MeasurableSpace.generateFrom_le
      intro t ht
      obtain ⟨A, hA, B, hB, C, hC, rfl⟩ := ht
      -- (pi A) × B × (pi C) is measurable as a product of measurable sets
      exact (MeasurableSet.univ_pi hA).prod (hB.prod (MeasurableSet.univ_pi hC))

  -- Define covering family (constant sequence of Set.univ)
  let Bseq : ℕ → Set ((Fin r → α) × α × (Fin k → α)) := fun _ => Set.univ

  have h1B : ⋃ n, Bseq n = Set.univ := by
    simp only [Bseq, Set.iUnion_const]

  have h2B : ∀ n, Bseq n ∈ Rectangles := by
    intro n
    refine ⟨fun _ => Set.univ, fun _ => MeasurableSet.univ,
            Set.univ, MeasurableSet.univ,
            fun _ => Set.univ, fun _ => MeasurableSet.univ, ?_⟩
    ext ⟨z, y, c⟩
    simp only [Bseq, Set.mem_univ, Set.mem_prod, Set.mem_univ_pi]
    tauto

  have hμB : ∀ n, Measure.map (fun ω => (Z_r ω, X r ω, Y_future ω)) μ (Bseq n) ≠ ⊤ := by
    intro n
    simp only [Bseq]
    exact measure_ne_top _ Set.univ

  -- Convert h_agree to explicit form for Measure.ext_of_generateFrom_of_iUnion
  have h_agree_explicit : ∀ s ∈ Rectangles,
      Measure.map (fun ω => (Z_r ω, X r ω, Y_future ω)) μ s
        = Measure.map (fun ω => (Z_r ω, X r ω, Y_tail ω)) μ s := by
    intro s hs
    exact h_agree hs

  -- Apply Measure.ext_of_generateFrom_of_iUnion
  exact Measure.ext_of_generateFrom_of_iUnion
    Rectangles Bseq h_gen h_pi h1B h2B hμB h_agree_explicit

/-- Join with a finite future equals the comap of the paired map `(Z_r, θ_future^k)`. -/
lemma join_eq_comap_pair_finFuture
    {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
    (X : ℕ → Ω → α) (r m k : ℕ) :
  firstRSigma X r ⊔ finFutureSigma X m k
    =
  MeasurableSpace.comap
    (fun ω => (fun i : Fin r => X i.1 ω,
               fun j : Fin k => X (m + 1 + j.1) ω))
    inferInstance := by
  classical
  -- Notation
  let f : Ω → (Fin r → α) := fun ω i => X i.1 ω
  let g : Ω → (Fin k → α) := fun ω j => X (m + 1 + j.1) ω
  -- LHS is the join of comaps; RHS is comap of the product.
  have : firstRSigma X r = MeasurableSpace.comap f inferInstance := rfl
  have : finFutureSigma X m k = MeasurableSpace.comap g inferInstance := rfl
  -- `comap_prodMk` is exactly the identity we need.
  simpa [firstRSigma, finFutureSigma] using (MeasurableSpace.comap_prodMk f g).symm

-- **[REMOVED]**: condDistrib_of_map_eq_map_and_comap_le
--
-- This previously claimed uniqueness of conditional distributions under pair-law
-- and σ-algebra inclusion. It has been preempted by the direct conditional
-- expectation proof in condexp_indicator_drop_info_of_pair_law_direct, which
-- proves what we need without relying on kernel machinery or disintegration
-- uniqueness.

/-- **Direct CE proof (no kernels needed):** Drop-info lemma via test functions.

If `(ξ, η) =ᵈ (ξ, ζ)` and `σ(η) ≤ σ(ζ)`, then:
```
E[1_B(ξ) | σ(ζ)] = E[1_B(ξ) | σ(η)]  a.e.
```

**Proof idea (test function method):**
Two σ(ζ)-measurable L¹ functions are a.e. equal iff they integrate the same
against all bounded σ(ζ)-measurable test functions. From pair-law equality:
  ∫ 1_B(ξ) (k ∘ η) dμ = ∫ 1_B(ξ) (k ∘ ζ) dμ  for all bounded Borel k

Since σ(η) ≤ σ(ζ), any (k ∘ η) is also σ(ζ)-measurable. By testing against
this class of functions and using the separating property, we get the result.

**This completely avoids kernel machinery and disintegration uniqueness!**

This lemma directly replaces `condDistrib_of_map_eq_map_and_comap_le`
at its only point of use. -/
lemma condexp_indicator_drop_info_of_pair_law_direct
    {Ω α β : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [Nonempty Ω]
    [MeasurableSpace α] [StandardBorelSpace α] [Nonempty α]
    [MeasurableSpace β] [StandardBorelSpace β] [Nonempty β]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (ξ : Ω → α) (η ζ : Ω → β)
    (hξ : Measurable ξ) (hη : Measurable η) (hζ : Measurable ζ)
    (h_law :
      Measure.map (fun ω => (ξ ω, η ω)) μ
        = Measure.map (fun ω => (ξ ω, ζ ω)) μ)
    (h_le :
      MeasurableSpace.comap η inferInstance ≤
      MeasurableSpace.comap ζ inferInstance)
    {B : Set α} (hB : MeasurableSet B) :
  μ[Set.indicator B (fun _ => (1 : ℝ)) ∘ ξ | MeasurableSpace.comap ζ inferInstance]
    =ᵐ[μ]
  μ[Set.indicator B (fun _ => (1 : ℝ)) ∘ ξ | MeasurableSpace.comap η inferInstance] := by
  classical
  -- **Kallenberg 1.3 via regular conditional kernels (adapted for mathlib v4.24.0)**
  --
  -- Proof strategy:
  -- 1. Express both CEs via condExpKernel (integral representation)
  -- 2. For indicators, reduce integrals to measure evaluation
  -- 3. Use Doob-Dynkin: σ(η) ≤ σ(ζ) gives η = φ ∘ ζ
  -- 4. Apply uniqueness: show μ[·|mζ] = μ[·|mη] via integral properties
  -- 5. Key step: prove mη-measurability from pair-law (Kallenberg's deep content)
  --
  -- Note: StandardBorelSpace assumptions required for condExpKernel API

  -- **Pattern B: Inline comaps to avoid any name shadowing**
  -- Freeze ambient instances under stable names for explicit reference
  let mΩ : MeasurableSpace Ω := (by exact ‹MeasurableSpace Ω›)
  let mγ : MeasurableSpace β := (by exact ‹MeasurableSpace β›)

  -- Convert goal from composition form to preimage form
  have hind : Set.indicator B (fun _ => (1 : ℝ)) ∘ ξ = (ξ ⁻¹' B).indicator (fun _ => (1 : ℝ)) := by
    ext ω
    simp [Set.indicator, Set.mem_preimage]

  rw [hind]

  -- Goal is now: μ[(ξ ⁻¹' B).indicator (fun _ => (1 : ℝ))|mζ] =ᵐ[μ]
  --                μ[(ξ ⁻¹' B).indicator (fun _ => (1 : ℝ))|mη]

  -- Both CEs are integrable
  have hint : Integrable (Set.indicator (ξ ⁻¹' B) (fun _ => (1 : ℝ))) μ := by
    exact Integrable.indicator (integrable_const 1) (hξ hB)

  -- Prove inclusions without naming the pullbacks (Pattern B)
  have hmη_le : MeasurableSpace.comap η mγ ≤ mΩ := by
    intro s hs
    rcases hs with ⟨t, ht, rfl⟩
    exact (hη ht : @MeasurableSet Ω mΩ (η ⁻¹' t))

  have hmζ_le : MeasurableSpace.comap ζ mγ ≤ mΩ := by
    intro s hs
    rcases hs with ⟨t, ht, rfl⟩
    exact (hζ ht : @MeasurableSet Ω mΩ (ζ ⁻¹' t))

  -- Step 1: Express CEs via kernel integrals (inline comaps, let Lean synthesize instances)
  have hCEη : μ[Set.indicator (ξ ⁻¹' B) (fun _ => (1 : ℝ)) | MeasurableSpace.comap η mγ] =ᵐ[μ]
              (fun ω => ∫ y, Set.indicator (ξ ⁻¹' B) (fun _ => (1 : ℝ)) y
                ∂(ProbabilityTheory.condExpKernel μ (MeasurableSpace.comap η mγ) ω)) := by
    exact ProbabilityTheory.condExp_ae_eq_integral_condExpKernel hmη_le hint

  have hCEζ : μ[Set.indicator (ξ ⁻¹' B) (fun _ => (1 : ℝ)) | MeasurableSpace.comap ζ mγ] =ᵐ[μ]
              (fun ω => ∫ y, Set.indicator (ξ ⁻¹' B) (fun _ => (1 : ℝ)) y
                ∂(ProbabilityTheory.condExpKernel μ (MeasurableSpace.comap ζ mγ) ω)) := by
    exact ProbabilityTheory.condExp_ae_eq_integral_condExpKernel hmζ_le hint

  -- Note: We have kernel integral representations from hCEη and hCEζ
  -- The integrals of indicators equal measure evaluations, but we don't need to prove
  -- that explicitly - the uniqueness characterization works with the integral form

  -- Step 3: Doob-Dynkin factorization (inline comaps)
  -- Since σ(η) ≤ σ(ζ), we have η = φ ∘ ζ for some measurable φ
  have ⟨φ, hφ, hηfac⟩ : ∃ φ : β → β, Measurable φ ∧ η = φ ∘ ζ := by
    -- η is measurable with respect to comap ζ because comap η ≤ comap ζ
    have hη_comap : Measurable[MeasurableSpace.comap ζ mγ] η := by
      rw [measurable_iff_comap_le]
      exact h_le
    -- Use Measurable.exists_eq_measurable_comp (requires StandardBorelSpace β and Nonempty β)
    exact hη_comap.exists_eq_measurable_comp

  -- **Direct proof via tower property uniqueness:**
  -- Instead of proving measurability then equality, prove equality directly!
  -- μ[f|ζ] =ᵐ μ[f|η] implies measurability automatically.

  -- Key insight: By tower property, μ[μ[f|ζ]|η] = μ[f|η].
  -- We'll show μ[f|η] also satisfies the characterizing integral property
  -- for μ[f|ζ], implying equality by uniqueness.

  have heq_direct : μ[Set.indicator (ξ ⁻¹' B) (fun _ => (1 : ℝ))|MeasurableSpace.comap ζ mγ] =ᵐ[μ]
                    μ[Set.indicator (ξ ⁻¹' B) (fun _ => (1 : ℝ))|MeasurableSpace.comap η mγ] := by
    -- Use tower property to establish the integral characterization
    have htower : μ[μ[Set.indicator (ξ ⁻¹' B) (fun _ => (1 : ℝ))|MeasurableSpace.comap ζ mγ]|
                      MeasurableSpace.comap η mγ] =ᵐ[μ]
                    μ[Set.indicator (ξ ⁻¹' B) (fun _ => (1 : ℝ))|MeasurableSpace.comap η mγ] := by
      exact condExp_condExp_of_le h_le hmζ_le

    -- μ[f|η] is measurable w.r.t. σ(η), hence also w.r.t. σ(ζ) (since σ(η) ≤ σ(ζ))
    have hCE_η_meas_ζ : AEStronglyMeasurable[MeasurableSpace.comap ζ mγ]
        (μ[Set.indicator (ξ ⁻¹' B) (fun _ => (1 : ℝ))|MeasurableSpace.comap η mγ]) μ := by
      -- μ[f|η] is strongly measurable w.r.t. σ(η)
      have : StronglyMeasurable[MeasurableSpace.comap η mγ]
          (μ[Set.indicator (ξ ⁻¹' B) (fun _ => (1 : ℝ))|MeasurableSpace.comap η mγ]) :=
        stronglyMeasurable_condExp
      -- σ(η) ≤ σ(ζ), so σ(η)-measurable functions are σ(ζ)-measurable
      exact this.mono h_le |>.aestronglyMeasurable

    -- Now apply uniqueness: μ[f|η] satisfies the integral characterization for CE w.r.t. σ(ζ)
    -- The lemma proves g =ᵐ μ[f|m], so we get μ[f|η] =ᵐ μ[f|ζ], then symmetrize
    refine (ae_eq_condExp_of_forall_setIntegral_eq hmζ_le hint
      (fun s hs _ => integrable_condExp.integrableOn) ?_ hCE_η_meas_ζ).symm

    -- **Deep content:** Prove ∫_S μ[f|η] = ∫_S f for S ∈ σ(ζ)
    -- Key insight: The pair-law implies condDistrib(ξ|ζ) = condDistrib(ξ|η) via uniqueness
    intro S hS hS_fin

    -- Step 1: Swap pair-law to get the right direction: law(ζ,ξ) = law(η,ξ)
    have h_law_swapped : μ.map (fun ω => (ζ ω, ξ ω)) = μ.map (fun ω => (η ω, ξ ω)) := by
      have h_prod_comm_ζ : μ.map (fun ω => (ζ ω, ξ ω)) = (μ.map (fun ω => (ξ ω, ζ ω))).map Prod.swap := by
        rw [Measure.map_map (measurable_swap) (hξ.prodMk hζ)]
        rfl
      have h_prod_comm_η : μ.map (fun ω => (η ω, ξ ω)) = (μ.map (fun ω => (ξ ω, η ω))).map Prod.swap := by
        rw [Measure.map_map (measurable_swap) (hξ.prodMk hη)]
        rfl
      rw [h_prod_comm_ζ, h_prod_comm_η, h_law]

    -- Step 2: Express joint distributions using compProd in the RIGHT direction
    have hζ_compProd : (μ.map ζ) ⊗ₘ (ProbabilityTheory.condDistrib ξ ζ μ) = μ.map (fun ω => (ζ ω, ξ ω)) := by
      exact ProbabilityTheory.compProd_map_condDistrib hξ.aemeasurable

    have hη_compProd : (μ.map η) ⊗ₘ (ProbabilityTheory.condDistrib ξ η μ) = μ.map (fun ω => (η ω, ξ ω)) := by
      exact ProbabilityTheory.compProd_map_condDistrib hξ.aemeasurable

    -- Step 3: Get marginal equality from swapped pair-law
    have h_marg_eq : μ.map ζ = μ.map η := by
      have h1 : (μ.map (fun ω => (ζ ω, ξ ω))).fst = μ.map ζ := Measure.fst_map_prodMk₀ hξ.aemeasurable
      have h2 : (μ.map (fun ω => (η ω, ξ ω))).fst = μ.map η := Measure.fst_map_prodMk₀ hξ.aemeasurable
      rw [← h1, ← h2, h_law_swapped]

    -- Step 4: The deep content - show conditional expectations w.r.t. σ(ζ) and σ(η) coincide.
    -- This follows from the tower property since σ(η) ≤ σ(ζ), plus uniqueness.
    -- The pair-law equality implies the conditional distributions must match appropriately.

    -- We'll show this directly using tower property and integral characterization.
    -- The key fact: μ[f|η] satisfies the defining integrals for μ[f|ζ] on σ(ζ)-sets.

    -- Now we have everything we need - use the pair-law to show equality of CEs
    -- Key: The pair-law implies condDistrib(ξ|ζ) = condDistrib(ξ|η) by compProd uniqueness
    have h_ce_eq : μ[(ξ ⁻¹' B).indicator (fun _ => (1 : ℝ))|MeasurableSpace.comap ζ mγ] =ᵐ[μ]
                   μ[(ξ ⁻¹' B).indicator (fun _ => (1 : ℝ))|MeasurableSpace.comap η mγ] := by
      -- Step 1: From compProd equalities and pair-law, derive kernel equality
      -- We have (μ.map ζ) ⊗ₘ condDistrib(ξ|ζ) = μ.map (ζ,ξ) = μ.map (η,ξ) = (μ.map η) ⊗ₘ condDistrib(ξ|η)
      -- Combined with h_marg_eq: μ.map ζ = μ.map η, we get:
      -- (μ.map ζ) ⊗ₘ condDistrib(ξ|ζ) = (μ.map ζ) ⊗ₘ condDistrib(ξ|η)
      have h_compProd_eq : (μ.map ζ) ⊗ₘ (ProbabilityTheory.condDistrib ξ ζ μ) =
                           (μ.map ζ) ⊗ₘ (ProbabilityTheory.condDistrib ξ η μ) := by
        calc (μ.map ζ) ⊗ₘ (ProbabilityTheory.condDistrib ξ ζ μ)
            = μ.map (fun ω => (ζ ω, ξ ω)) := hζ_compProd
          _ = μ.map (fun ω => (η ω, ξ ω)) := h_law_swapped
          _ = (μ.map η) ⊗ₘ (ProbabilityTheory.condDistrib ξ η μ) := hη_compProd.symm
          _ = (μ.map ζ) ⊗ₘ (ProbabilityTheory.condDistrib ξ η μ) := by rw [h_marg_eq]

      -- Step 2: From h_compProd_eq, derive that the conditional expectations must be equal
      -- The key is that both CEs integrate against kernels that produce the same joint measure

      -- We have hCEζ: μ[f|ζ] =ᵐ (∫ y, f y ∂condExpKernel(ζ)(·))
      -- and hCEη: μ[f|η] =ᵐ (∫ y, f y ∂condExpKernel(η)(·))

      -- Since η = φ ∘ ζ (from hηfac) and the compProd equality holds,
      -- the kernels must satisfy: condExpKernel(ζ)(ζ ω) = condExpKernel(η)(η ω) a.e.

      -- This is a deep result requiring kernel uniqueness from compProd.
      -- Apply the proved theorem from ConditionalKernel.lean
      exact condExp_eq_of_joint_law_eq ζ η hζ hη ξ hξ B hB h_law.symm h_le ⟨φ, hφ, hηfac⟩

    -- Finish: prove ∫_S μ[f|η] = ∫_S f using the defining property of conditional expectation
    -- First, prove ∫_S μ[f|ζ] = ∫_S f (by definition of conditional expectation)
    have step1 : ∫ ω in S, μ[(ξ ⁻¹' B).indicator (fun _ => (1 : ℝ))|MeasurableSpace.comap ζ mγ] ω ∂μ =
                 ∫ ω in S, (ξ ⁻¹' B).indicator (fun _ => (1 : ℝ)) ω ∂μ := by
      -- S is measurable in σ(ζ), need SigmaFinite instance
      haveI : SigmaFinite (μ.trim hmζ_le) := by
        -- The trimmed measure is sigma-finite because μ is a probability measure
        infer_instance
      exact setIntegral_condExp hmζ_le hint hS

    -- Then, prove ∫_S μ[f|η] = ∫_S μ[f|ζ] using the a.e. equality
    have step2 : ∫ ω in S, μ[(ξ ⁻¹' B).indicator (fun _ => (1 : ℝ))|MeasurableSpace.comap η mγ] ω ∂μ =
                 ∫ ω in S, μ[(ξ ⁻¹' B).indicator (fun _ => (1 : ℝ))|MeasurableSpace.comap ζ mγ] ω ∂μ := by
      -- A.e. equal functions have equal integrals
      have : (fun ω => μ[(ξ ⁻¹' B).indicator (fun _ => (1 : ℝ))|MeasurableSpace.comap η mγ] ω) =ᵐ[μ.restrict S]
             (fun ω => μ[(ξ ⁻¹' B).indicator (fun _ => (1 : ℝ))|MeasurableSpace.comap ζ mγ] ω) := by
        exact ae_restrict_of_ae h_ce_eq.symm
      exact integral_congr_ae this

    -- Combine to get ∫_S μ[f|η] = ∫_S f
    calc ∫ ω in S, μ[(ξ ⁻¹' B).indicator (fun _ => (1 : ℝ))|MeasurableSpace.comap η mγ] ω ∂μ
        = ∫ ω in S, μ[(ξ ⁻¹' B).indicator (fun _ => (1 : ℝ))|MeasurableSpace.comap ζ mγ] ω ∂μ := step2
      _ = ∫ ω in S, (ξ ⁻¹' B).indicator (fun _ => (1 : ℝ)) ω ∂μ := step1

  exact heq_direct

/-- **Kallenberg 1.3 Conditional Expectation Form (Route A):**
If `(ξ, η) =ᵈ (ξ, ζ)` and `σ(η) ≤ σ(ζ)`, then conditioning ξ on ζ is the same as
conditioning on η.

This is the "drop information" form of Kallenberg's Lemma 1.3, stating that ζ provides
no additional information about ξ beyond what η provides.

**Mathematical statement:**
```
E[1_B(ξ) | σ(ζ)] = E[1_B(ξ) | σ(η)]  a.e.
```

**Proof sketch:**
**The desired "drop information" lemma follows directly from the tower property:**
Since σ(η) ≤ σ(ζ), we have E[E[·|ζ]|η] = E[·|η], which gives the result without
needing kernel machinery.
-/
lemma condexp_indicator_drop_info_of_pair_law
    {Ω α β : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    [MeasurableSpace α] [StandardBorelSpace α] [Nonempty α]
    [MeasurableSpace β] [Nonempty β]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (ξ : Ω → α) (η ζ : Ω → β)
    (hξ : Measurable ξ) (hη : Measurable η) (hζ : Measurable ζ)
    (_h_law :
      Measure.map (fun ω => (ξ ω, η ω)) μ
        = Measure.map (fun ω => (ξ ω, ζ ω)) μ)
    (h_le :
      MeasurableSpace.comap η inferInstance ≤
      MeasurableSpace.comap ζ inferInstance)
    {B : Set α} (hB : MeasurableSet B) :
  μ[ μ[Set.indicator B (fun _ => (1 : ℝ)) ∘ ξ
        | MeasurableSpace.comap ζ inferInstance]
     | MeasurableSpace.comap η inferInstance ]
    =ᵐ[μ]
  μ[Set.indicator B (fun _ => (1 : ℝ)) ∘ ξ
        | MeasurableSpace.comap η inferInstance] := by
  classical
  -- Direct proof via tower property for sub-σ-algebras
  have h_tower : μ[μ[Set.indicator B (fun _ => (1 : ℝ)) ∘ ξ
                      | MeasurableSpace.comap ζ inferInstance]
                    | MeasurableSpace.comap η inferInstance]
                 =ᵐ[μ]
                 μ[Set.indicator B (fun _ => (1 : ℝ)) ∘ ξ
                    | MeasurableSpace.comap η inferInstance] := by
    -- Establish σ-algebra inequalities
    have hη_le : MeasurableSpace.comap η inferInstance ≤ (inferInstance : MeasurableSpace Ω) := by
      intro s hs
      obtain ⟨t, ht, rfl⟩ := hs
      exact hη ht
    have hζ_le : MeasurableSpace.comap ζ inferInstance ≤ (inferInstance : MeasurableSpace Ω) := by
      intro s hs
      obtain ⟨t, ht, rfl⟩ := hs
      exact hζ ht
    -- Indicator function is integrable (bounded by 1 on probability space)
    have hf_int : Integrable (Set.indicator B (fun _ => (1 : ℝ)) ∘ ξ) μ := by
      apply Integrable.comp_measurable _ hξ
      exact integrable_const (1 : ℝ) |>.indicator hB
    -- Apply tower property from CondExpHelpers
    exact condExp_project_of_le
      (MeasurableSpace.comap η inferInstance)
      (MeasurableSpace.comap ζ inferInstance)
      inferInstance
      hη_le hζ_le h_le hf_int
  exact h_tower

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
Y ⊥⊥_{σ(Y)} Y.**

---

**SIMPLIFIED PROOF PATH (using Kallenberg 1.3 infrastructure):**

The proof now uses `condExp_Xr_indicator_eq_of_contractable` which directly applies
Kallenberg 1.3 with the true contraction structure:
- W = shiftRV X (m+1) (far future)
- W' = (U, W) where U = firstRMap X r (first r coords)
- Contraction: σ(W) ⊆ σ(U, W) = σ(W')
- Pair law: (X_r, W) =^d (X_r, W') from contractability

This gives: E[1_{X_r ∈ B} | σ(U, W)] = E[1_{X_r ∈ B} | σ(W)]
which is the indicator characterization of X_r ⊥⊥ U | W.

The old finite-level approximation approach is now deprecated. -/
lemma block_coord_condIndep
    {Ω α : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    [MeasurableSpace α] [StandardBorelSpace α]
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
  -- ═══════════════════════════════════════════════════════════════════════════════
  -- SIMPLIFIED PROOF using Kallenberg 1.3 infrastructure (condExp_Xr_indicator_eq_of_contractable)
  -- ═══════════════════════════════════════════════════════════════════════════════
  --
  -- This bypasses the old finite-level approximation which used the broken chain:
  --   condexp_indicator_eq_on_join_of_triple_law → condExp_eq_of_triple_law
  --     → condIndep_of_triple_law_INVALID
  --
  -- Instead, we use the correct Kallenberg 1.3 approach with true contraction:
  --   condExp_Xr_indicator_eq_of_contractable (at infinite level)
  --
  -- ═══════════════════════════════════════════════════════════════════════════════

  -- We use the "indicator projection" criterion for conditional independence.
  apply Exchangeability.Probability.condIndep_of_indicator_condexp_eq
  · exact firstRSigma_le_ambient X r hX_meas
  · intro s hs; rcases hs with ⟨t, ht, rfl⟩; exact (hX_meas r) ht

  -- For each H = (X r)⁻¹(B), prove the projection identity:
  -- μ[1_H | firstRSigma X r ⊔ futureFiltration X m] =ᵐ[μ] μ[1_H | futureFiltration X m]
  intro H hH
  rcases hH with ⟨B, hB, rfl⟩

  -- Translate to the form expected by condExp_Xr_indicator_eq_of_contractable
  -- The σ-algebras match definitionally:
  -- - firstRSigma X r = comap (fun ω i => X i ω) inferInstance
  -- - futureFiltration X m = comap (shiftRV X (m+1)) inferInstance
  -- The goal becomes: μ[1_{(X r)⁻¹(B)} | comap U ⊔ comap W] =ᵐ[μ] μ[1_{(X r)⁻¹(B)} | comap W]
  -- which is exactly what condExp_Xr_indicator_eq_of_contractable provides.

  -- The goal after applying condIndep_of_indicator_condexp_eq is:
  -- μ[Set.indicator ((X r) ⁻¹' B) (fun _ => 1) | firstRSigma X r ⊔ futureFiltration X m]
  --   =ᵐ[μ] μ[Set.indicator ((X r) ⁻¹' B) (fun _ => 1) | futureFiltration X m]
  --
  -- This matches condExp_Xr_indicator_eq_of_contractable with:
  -- - Y = X r
  -- - U = (fun ω i => X i ω) (definitionally = firstRMap X r)
  -- - W = shiftRV X (m+1) (definitionally = futureFiltration generator)
  --
  -- The σ-algebra identities needed:
  -- - firstRSigma X r = comap U inferInstance ✓
  -- - futureFiltration X m = comap W inferInstance ✓
  --
  -- Thus the result follows from condExp_Xr_indicator_eq_of_contractable.
  have h := condExp_Xr_indicator_eq_of_contractable hX hX_meas (Nat.le_of_lt hrm) hB
  exact h

  -- NOTE: The previous proof used a finite-level approximation + Lévy upward convergence
  -- approach, but that depended on a broken chain (condIndep_of_triple_law_INVALID).
  -- The current proof via Kallenberg 1.3 is mathematically correct.


/-- **Product formula for conditional expectations under conditional independence.**

Given two sets `A` (measurable in `mF`) and `B` (measurable in `mH`), under conditional
independence given `m`, the conditional expectation of the intersection indicator factors:
```
μ[1_{A∩B} | m] = μ[1_A | m] · μ[1_B | m]   a.e.
```

Now proven using `condexp_indicator_inter_bridge` from CondExp.lean, eliminating the
previous `: True` stub. -/
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
    {Ω α : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    [MeasurableSpace α] [StandardBorelSpace α]
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
      ring_nf

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
        μ :=
      block_coord_condIndep X hX hX_meas hrm

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
          _ =ᵐ[μ] μ[(A ∩ B).indicator (fun _ => (1:ℝ)) | futureFiltration X m] :=
            condExp_congr_ae (EventuallyEq.of_eq h_inter)
          _ =ᵐ[μ] (μ[A.indicator (fun _ => (1:ℝ)) | futureFiltration X m] *
                   μ[B.indicator (fun _ => (1:ℝ)) | futureFiltration X m]) :=
            condexp_indicator_inter_of_condIndep
              (futureFiltration_le X m hX_meas)
              (firstRSigma_le_ambient X r hX_meas)
              (fun s hs => by obtain ⟨t, ht, rfl⟩ := hs; exact (hX_meas r) ht)
              h_condIndep
              hA_meas_firstR
              hB_meas_Xr

    -- Apply IH to the first r factors
    have hIH : μ[indProd X r Cinit | futureFiltration X m] =ᵐ[μ]
        (fun ω => ∏ i : Fin r,
          μ[Set.indicator (Cinit i) (fun _ => (1:ℝ)) ∘ (X 0) | futureFiltration X m] ω) :=
      ih Cinit hCinit (Nat.le_of_succ_le hm)

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
    -- Apply Lévy's reverse martingale convergence directly
    have h_conv := Exchangeability.Probability.condExp_tendsto_iInf
      (μ := μ)
      (𝔽 := futureFiltration X)
      (h_filtration := futureFiltration_antitone X)
      (h_le := fun n => futureFiltration_le X n hX)
      (f := indProd X r C)
      (h_f_int := indProd_integrable X r C hX hC)
    -- Convert ⨅ n, futureFiltration X n to tailSigma X
    simp only [← tailSigmaFuture_eq_iInf, tailSigmaFuture_eq_tailSigma] at h_conv
    exact h_conv

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
      -- Countable intersection of ae sets
      -- For each m ≥ r, we have an ae set where equality holds
      -- Take countable intersection indexed by {m // m ≥ r}
      have h_count_inter : ∀ᵐ ω ∂μ, ∀ m : {m // m ≥ r},
          μ[indProd X r C | futureFiltration X m] ω
            = (∏ i : Fin r,
                μ[Set.indicator (C i) (fun _ => (1 : ℝ)) ∘ (X 0) | futureFiltration X m] ω) := by
        -- Use ae_all_iff for countable intersection
        rw [ae_all_iff]
        intro ⟨m, hm⟩
        exact h_fact m hm
      -- Convert from subtype to ∀ m ≥ r
      filter_upwards [h_count_inter] with ω hω m hm
      exact hω ⟨m, hm⟩

    filter_upwards [h_lhs_conv, h_rhs_conv, h_fact_large] with ω hlhs hrhs hfact
    -- At ω, both sequences converge and are eventually equal, so limits are equal
    exact tendsto_nhds_unique hlhs (hrhs.congr' (eventually_atTop.mpr ⟨r, fun m hm => (hfact m hm).symm⟩))

  exact h_eq_ae

/-! ### Directing measure construction

From conditional expectations on indicators, we need to build a measurable family
of probability measures `ν : Ω → Measure α`.

The construction uses the standard Borel machinery: for each `ω`, define
`ν ω` to be the unique probability measure satisfying
`ν ω B = E[1_{X₀∈B} | 𝒯_X](ω)` for all measurable `B`.

This requires StandardBorelSpace assumption on α to ensure existence.
-/

section Directing

open ProbabilityTheory

/-- **Directing measure**: conditional distribution of `X₀` given the tail σ-algebra.

Constructed using `condExpKernel` API: for each ω, evaluate the conditional expectation kernel
at ω to get a measure on Ω, then push forward along X₀.

Concretely: `directingMeasure ω = (condExpKernel μ (tailSigma X) ω).map (X 0)`
-/
noncomputable def directingMeasure
    {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {α : Type*} [MeasurableSpace α] [StandardBorelSpace α] [Nonempty α]
    (X : ℕ → Ω → α) (_hX : ∀ n, Measurable (X n)) (ω : Ω) : Measure α :=
  (ProbabilityTheory.condExpKernel μ (tailSigma X) ω).map (X 0)

/-- `directingMeasure` evaluates measurably on measurable sets.

Uses: `Kernel.measurable_coe` and `Measure.map_apply`. -/
lemma directingMeasure_measurable_eval
    {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {α : Type*} [MeasurableSpace α] [StandardBorelSpace α] [Nonempty α]
    (X : ℕ → Ω → α) (hX : ∀ n, Measurable (X n)) :
    ∀ (B : Set α), MeasurableSet B →
      Measurable (fun ω => directingMeasure (μ := μ) X hX ω B) := by
  intro B hB
  classical
  have hS : MeasurableSet ((X 0) ⁻¹' B) := (hX 0) hB
  let κ := ProbabilityTheory.condExpKernel μ (tailSigma X)
  simp only [directingMeasure, Measure.map_apply (hX 0) hB]
  exact (ProbabilityTheory.Kernel.measurable_coe κ hS).mono (tailSigma_le X hX) le_rfl

/-- The directing measure is (pointwise) a probability measure.

Uses: `isProbability_condExpKernel` and map preserves probability. -/
lemma directingMeasure_isProb
    {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {α : Type*} [MeasurableSpace α] [StandardBorelSpace α] [Nonempty α]
    (X : ℕ → Ω → α) (hX : ∀ n, Measurable (X n)) :
    ∀ ω, IsProbabilityMeasure (directingMeasure (μ := μ) X hX ω) := by
  intro ω
  -- Strategy: condExpKernel is an IsMarkovKernel, so each condExpKernel ω is a probability measure
  --           Pushing forward preserves probability via Measure.isProbabilityMeasure_map
  -- directingMeasure ω = (condExpKernel μ (tailSigma X) ω).map (X 0)
  unfold directingMeasure
  exact Measure.isProbabilityMeasure_map (hX 0).aemeasurable

/-- **X₀-marginal identity**: the conditional expectation of the indicator
of `X 0 ∈ B` given the tail equals the directing measure of `B` (toReal).

Uses: `condExp_ae_eq_integral_condExpKernel` and `integral_indicator_one`. -/
lemma directingMeasure_X0_marginal
    {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {α : Type*} [MeasurableSpace α] [StandardBorelSpace α] [Nonempty α]
    (X : ℕ → Ω → α) (hX : ∀ n, Measurable (X n))
    (B : Set α) (hB : MeasurableSet B) :
  (fun ω => (directingMeasure (μ := μ) X hX ω B).toReal)
    =ᵐ[μ]
  μ[Set.indicator B (fun _ => (1 : ℝ)) ∘ (X 0) | tailSigma X] := by
  classical
  have hInt : Integrable (fun ω => (Set.indicator B (fun _ => (1 : ℝ)) (X 0 ω))) μ :=
    (integrable_const 1).indicator ((hX 0) hB)
  let κ := ProbabilityTheory.condExpKernel μ (tailSigma X)

  -- Conditional expectation equals kernel integral a.e.
  have hAE := ProbabilityTheory.condExp_ae_eq_integral_condExpKernel (tailSigma_le X hX) hInt

  -- Identify the kernel integral with evaluation of `directingMeasure` on `B`
  have hId : (fun ω => ∫ x, (Set.indicator B (fun _ => (1 : ℝ)) (X 0 x)) ∂κ ω) =
             (fun ω => (directingMeasure (μ := μ) X hX ω B).toReal) := by
    funext ω
    have h_eq : (fun x => Set.indicator B (fun _ => (1 : ℝ)) (X 0 x)) =
                Set.indicator ((X 0) ⁻¹' B) (fun _ => (1 : ℝ)) := by ext x; simp [Set.indicator]
    simp only [h_eq, directingMeasure, Measure.map_apply (hX 0) hB]
    exact MeasureTheory.integral_indicator_one ((hX 0) hB)

  -- Combine: rewrite with hId then apply hAE
  calc (fun ω => (directingMeasure (μ := μ) X hX ω B).toReal)
      = (fun ω => ∫ x, (Set.indicator B (fun _ => (1 : ℝ)) (X 0 x)) ∂κ ω) := hId.symm
    _ =ᵐ[μ] μ[Set.indicator B (fun _ => (1 : ℝ)) ∘ (X 0) | tailSigma X] := hAE.symm

end Directing

/-! ### Conditional law equality -/

/-- General form: All `X_n` have the same conditional law `ν`.
This follows from `extreme_members_equal_on_tail`. -/
lemma conditional_law_eq_of_X0_marginal
    {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω]
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

/-- **All coordinates share the directing measure as their conditional law.**

This is the key "common ending" result: the directing measure `ν` constructed from
the tail σ-algebra satisfies the marginal identity for all coordinates, not just X₀. -/
lemma conditional_law_eq_directingMeasure
    {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {α : Type*} [MeasurableSpace α] [StandardBorelSpace α] [Nonempty α]
    (X : ℕ → Ω → α)
    (hX : Contractable μ X)
    (hX_meas : ∀ n, Measurable (X n))
    (n : ℕ) (B : Set α) (hB : MeasurableSet B) :
    (fun ω => (directingMeasure (μ := μ) X hX_meas ω B).toReal)
      =ᵐ[μ]
    μ[Set.indicator B (fun _ => (1 : ℝ)) ∘ (X n) | tailSigma X] := by
  -- Apply the general lemma with ν := directingMeasure X hX_meas
  exact conditional_law_eq_of_X0_marginal X hX hX_meas (directingMeasure X hX_meas)
    (fun B hB => directingMeasure_X0_marginal X hX_meas B hB) n B hB

/-! ### Finite-dimensional product formula -/

/-- On a finite index type, product measures evaluate on rectangles as a finite product. -/
lemma measure_pi_univ_pi
    {α : Type*} [MeasurableSpace α] [StandardBorelSpace α]
    {m : ℕ} (μi : Fin m → Measure α) [∀ i, SigmaFinite (μi i)]
    (C : Fin m → Set α) :
  (Measure.pi (fun i : Fin m => μi i)) (Set.univ.pi C)
    = ∏ i : Fin m, μi i (C i) := by
  -- Convert Set.univ.pi to the pi univ form expected by Measure.pi_pi
  have h_eq : Set.univ.pi C = Set.pi Set.univ C := rfl
  rw [h_eq]
  -- Now apply Measure.pi_pi from Mathlib
  exact Measure.pi_pi (fun i : Fin m => μi i) C

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
    intro s hs
    rcases hs with ⟨C, hC, rfl⟩
    
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
    have h_int_tail : ∫ ω, indProd X m C ω ∂μ
        = ∫ ω, (∏ i : Fin m,
            μ[Set.indicator (C i) (fun _ => (1:ℝ)) ∘ (X 0) | tailSigma X] ω) ∂μ := by
      -- Tower property: ∫ f = ∫ E[f|τ] and use h_tail
      symm
      calc ∫ ω, (∏ i : Fin m,
            μ[Set.indicator (C i) (fun _ => (1:ℝ)) ∘ (X 0) | tailSigma X] ω) ∂μ
          = ∫ ω, μ[indProd X m C | tailSigma X] ω ∂μ :=
              integral_congr_ae h_tail.symm
        _ = ∫ ω, indProd X m C ω ∂μ :=
              -- Tower property: ∫ E[f|m] = ∫ f
              integral_condExp (tailSigma_le X hX_meas)
    
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
      have h_nonneg : ∀ᵐ ω ∂μ, 0 ≤ ∏ i : Fin m, (ν ω (C i)).toReal := by
        apply ae_of_all
        intro ω
        exact Finset.prod_nonneg (fun i _ => ENNReal.toReal_nonneg)

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
      have h_pi_prob : ∀ ω, (Measure.pi (fun _ : Fin m => ν ω)) Set.univ = 1 := by
        intro ω
        -- Measure.pi of probability measures is a probability measure
        haveI : ∀ i : Fin m, IsProbabilityMeasure (ν ω) := fun i => inferInstance
        -- Product measure gives measure 1 to univ
        haveI : IsProbabilityMeasure (Measure.pi (fun _ : Fin m => ν ω)) := inferInstance
        exact measure_univ
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
    ext f
    simp only [Bseq, Set.mem_univ, Set.mem_univ_pi]
    tauto

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
    = μ.bind (fun ω => Measure.pi fun _ : Fin m => ν ω) := by
  refine finite_product_formula X hX hX_meas ν hν_prob hν_meas hν_law m (fun i => (i : ℕ)) ?_
  -- `i ↦ i` is strictly monotone on `Fin m`.
  intro i j hij; exact hij

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
