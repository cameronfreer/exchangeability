/-
Copyright (c) 2025 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.MeasureTheory.Function.FactorsThrough
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Exchangeability.Probability.CondExp

/-!
# Common Version Lemma for Conditional Expectations

This file contains infrastructure lemmas and the main Common Version Lemma,
which is fundamental to the martingale approach proof of de Finetti's theorem.

## Main results

* `common_version_condexp_bdd` - Common Borel version for CEs along equal pair laws (bounded case)
* `common_version_condExp` - Common version lemma (general)
* `common_version_condExp_with_props` - Enhanced version with measurability and boundedness

## Infrastructure lemmas (A1-A4)

* `exists_borel_factor_of_comap_measurable` - Doob-Dynkin factorization
* `ae_eq_of_comp_ae_eq` - Pushing a.e. equalities along maps
* `exists_clipped_version` - Clipping to get pointwise bounds
* `integral_pair_transfer` - Topology-free integral transfer via pushforward measures

These are extracted from ViaMartingale.lean to enable modular imports.
-/

noncomputable section
open scoped MeasureTheory
open MeasureTheory Filter

namespace Exchangeability.DeFinetti.ViaMartingale

/-! ### Infrastructure for Common Version Lemma (Doob-Dynkin + Pushforward Uniqueness) -/

/-- **A1: Doob–Dynkin factorization (real-valued):**
If `f : Ω → ℝ` is a.e. strongly measurable w.r.t. `σ(W)` (that is, measurable for
`MeasurableSpace.comap W ‹_›`), then there exists a Borel measurable
`v : γ → ℝ` such that `f = v ∘ W` a.e.

This is a simplified version for the specific case needed in conditional expectations. -/
lemma exists_borel_factor_of_comap_measurable
    {Ω γ : Type*} [MeasurableSpace Ω] [MeasurableSpace γ]
    {μ : Measure Ω}
    (W : Ω → γ) (f : Ω → ℝ)
    (hf_meas : Measurable[MeasurableSpace.comap W inferInstance] f) :
  ∃ v : γ → ℝ, Measurable v ∧ f =ᵐ[μ] v ∘ W := by
  -- For comap-measurable functions, they factor through W by construction
  -- This is the Doob-Dynkin lemma: use Measurable.exists_eq_measurable_comp
  obtain ⟨v, hv_meas, hv_eq⟩ := hf_meas.exists_eq_measurable_comp
  -- f = v ∘ W exactly, so f =ᵐ[μ] v ∘ W trivially
  exact ⟨v, hv_meas, EventuallyEq.of_eq hv_eq⟩

/-- **A2: Pushing a.e. equalities along map (uniqueness via the law):**
If `v₁ ∘ W = v₂ ∘ W` almost everywhere w.r.t. `μ`, then `v₁ = v₂` a.e.
w.r.t. the pushforward measure `Measure.map W μ`. -/
lemma ae_eq_of_comp_ae_eq
    {Ω γ : Type*} [MeasurableSpace Ω] [MeasurableSpace γ]
    {μ : Measure Ω} {W : Ω → γ} {v₁ v₂ : γ → ℝ}
    (hW : Measurable W)
    (hv₁ : Measurable v₁) (hv₂ : Measurable v₂)
    (h : v₁ ∘ W =ᵐ[μ] v₂ ∘ W) :
  v₁ =ᵐ[Measure.map W μ] v₂ := by
  -- v₁ =ᵐ[map W μ] v₂ means ∀ᵐ y ∂(map W μ), v₁ y = v₂ y
  -- By ae_map_iff, this holds iff ∀ᵐ ω ∂μ, v₁ (W ω) = v₂ (W ω)
  -- which is exactly h
  rw [Filter.EventuallyEq]
  rw [ae_map_iff hW.aemeasurable (measurableSet_eq_fun hv₁ hv₂)]
  -- Now goal is ∀ᵐ ω ∂μ, v₁ (W ω) = v₂ (W ω), which is h
  convert h using 1

/-- **A3: Clip to get pointwise bounds for the version:**
From an a.e.-bounded version on `Law(W)`, produce a **pointwise bounded** Borel version
by clipping to `[-C, C]`. -/
lemma exists_clipped_version
    {γ : Type*} [MeasurableSpace γ]
    (v₀ : γ → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hv₀ : Measurable v₀)
    {ν : Measure γ}
    (hBound : ∀ᵐ y ∂ν, ‖v₀ y‖ ≤ C) :
  ∃ v : γ → ℝ, Measurable v ∧ (∀ y, ‖v y‖ ≤ C) ∧ v =ᵐ[ν] v₀ := by
  -- Clip v₀ to [-C, C]: v y := max (-C) (min (v₀ y) C)
  let v := fun y => max (-C) (min (v₀ y) C)
  refine ⟨v, ?_, ?_, ?_⟩
  · -- Measurability: composition of measurable functions
    exact measurable_const.max (hv₀.min measurable_const)
  · -- Pointwise bound
    intro y
    simp only [v, Real.norm_eq_abs, abs_le]
    exact ⟨le_max_left _ _, max_le (neg_le_self (by linarith [hC])) (min_le_right _ _)⟩
  · -- A.e. equality: v = v₀ wherever |v₀| ≤ C
    filter_upwards [hBound] with y hy
    simp only [v]
    have : -C ≤ v₀ y ∧ v₀ y ≤ C := by
      rw [Real.norm_eq_abs, abs_le] at hy; exact hy
    simp [this]

/-- **Topology-free integral transfer via pushforward measures.**

For a measurable function `φ : β × γ → ℝ` whose composition with the pair maps is integrable,
and random variables with equal pair laws, the integral of `φ ∘ (ξ, η)` equals the integral
of `φ ∘ (ξ, ζ)`.

This avoids `AEStronglyMeasurable` requirements by working entirely with pushforward measures.
We only require integrability of the composed functions, not pointwise bounds on `φ`. -/
lemma integral_pair_transfer
    {Ω β γ : Type*} [MeasurableSpace Ω] [MeasurableSpace β] [MeasurableSpace γ]
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {ξ : Ω → β} {η ζ : Ω → γ}
    (hξη : Measurable fun ω => (ξ ω, η ω))
    (hξζ : Measurable fun ω => (ξ ω, ζ ω))
    (pairLaw : Measure.map (fun ω => (ξ ω, η ω)) μ =
               Measure.map (fun ω => (ξ ω, ζ ω)) μ)
    {φ : β × γ → ℝ} (hφm : Measurable φ)
    (hint : Integrable (fun ω => φ (ξ ω, η ω)) μ) :
    ∫ ω, φ (ξ ω, η ω) ∂μ = ∫ ω, φ (ξ ω, ζ ω) ∂μ := by
  classical
  -- Integrability of φ over the first pushforward follows from integrability of the composition
  have hint₁ : Integrable φ (Measure.map (fun ω => (ξ ω, η ω)) μ) := by
    rwa [integrable_map_measure hφm.aestronglyMeasurable hξη.aemeasurable]

  have hint₂ : Integrable φ (Measure.map (fun ω => (ξ ω, ζ ω)) μ) := by
    rw [← pairLaw]
    exact hint₁

  -- Change of variables for pushforward integrals
  have map₁ : ∫ x, φ x ∂(Measure.map (fun ω => (ξ ω, η ω)) μ) =
              ∫ ω, φ (ξ ω, η ω) ∂μ := integral_map hξη.aemeasurable hint₁.aestronglyMeasurable
  have map₂ : ∫ x, φ x ∂(Measure.map (fun ω => (ξ ω, ζ ω)) μ) =
              ∫ ω, φ (ξ ω, ζ ω) ∂μ := integral_map hξζ.aemeasurable hint₂.aestronglyMeasurable

  -- Apply the pair-law on the pushforward side
  calc ∫ ω, φ (ξ ω, η ω) ∂μ
      = ∫ x, φ x ∂(Measure.map (fun ω => (ξ ω, η ω)) μ) := map₁.symm
    _ = ∫ x, φ x ∂(Measure.map (fun ω => (ξ ω, ζ ω)) μ) := by rw [pairLaw]
    _ = ∫ ω, φ (ξ ω, ζ ω) ∂μ := map₂

/-- **A4: Common Borel version for conditional expectations along equal pair laws.**

Let `ψ ∘ Z` be integrable, `W, W' : Ω → γ`, and assume the pair laws `(Z,W)` and `(Z,W')`
are equal. Then there exists a **Borel** `v : γ → ℝ` with the **pointwise bound**
`‖v‖ ≤ C` (if `‖ψ‖ ≤ C` a.e.) such that

`μ[ψ ∘ Z | σ(W)] = v ∘ W` a.e.   and   `μ[ψ ∘ Z | σ(W')] = v ∘ W'` a.e. -/
lemma common_version_condexp_bdd
    {Ω γ β : Type*} [MeasurableSpace Ω] [MeasurableSpace γ] [MeasurableSpace β]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {Z : Ω → β} {W W' : Ω → γ}
    {ψ : β → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hZ : Measurable Z) (hW : Measurable W) (hW' : Measurable W')
    (hψ : Measurable ψ)
    (hψ_int : Integrable (ψ ∘ Z) μ)
    (hψ_bdd : ∀ᵐ ω ∂μ, ‖ψ (Z ω)‖ ≤ C)
    (hPair : Measure.map (fun ω => (Z ω, W ω)) μ =
             Measure.map (fun ω => (Z ω, W' ω)) μ) :
  ∃ v : γ → ℝ, Measurable v ∧ (∀ y, ‖v y‖ ≤ C)
    ∧ μ[(ψ ∘ Z) | MeasurableSpace.comap W inferInstance] =ᵐ[μ] v ∘ W
    ∧ μ[(ψ ∘ Z) | MeasurableSpace.comap W' inferInstance] =ᵐ[μ] v ∘ W' := by
  classical
  -- Step 1: Doob-Dynkin on each side
  let V  := μ[(ψ ∘ Z) | MeasurableSpace.comap W  inferInstance]
  let V' := μ[(ψ ∘ Z) | MeasurableSpace.comap W' inferInstance]

  -- V is σ(W)-measurable, so factors through W
  have hV_meas : Measurable[MeasurableSpace.comap W inferInstance] V := by
    -- stronglyMeasurable_condExp gives StronglyMeasurable[comap W]
    -- For ℝ-valued functions, StronglyMeasurable implies Measurable
    exact stronglyMeasurable_condExp.measurable
  have hV_ae : AEStronglyMeasurable V μ := by
    -- stronglyMeasurable_condExp gives StronglyMeasurable[comap W]
    -- Apply aestronglyMeasurable to get AEStronglyMeasurable[comap W]
    -- Then use mono to lift to ambient σ-algebra
    let m0 : MeasurableSpace Ω := inferInstance
    have h_le : MeasurableSpace.comap W inferInstance ≤ m0 := by
      intro s hs
      obtain ⟨t, ht, rfl⟩ := hs
      exact hW ht
    exact stronglyMeasurable_condExp.aestronglyMeasurable.mono h_le

  obtain ⟨v₁, hv₁_meas, hV_eq⟩ := exists_borel_factor_of_comap_measurable W V hV_meas

  -- Similarly for V'
  have hV'_meas : Measurable[MeasurableSpace.comap W' inferInstance] V' := by
    -- Same as for V: stronglyMeasurable implies measurable for ℝ
    exact stronglyMeasurable_condExp.measurable
  have hV'_ae : AEStronglyMeasurable V' μ := by
    -- Same approach as for V
    let m0 : MeasurableSpace Ω := inferInstance
    have h_le : MeasurableSpace.comap W' inferInstance ≤ m0 := by
      intro s hs
      obtain ⟨t, ht, rfl⟩ := hs
      exact hW' ht
    exact stronglyMeasurable_condExp.aestronglyMeasurable.mono h_le

  obtain ⟨v₂, hv₂_meas, hV'_eq⟩ := exists_borel_factor_of_comap_measurable W' V' hV'_meas

  -- Step 2: Show v₁ = v₂ a.e. on Law(W) using pair law equality
  -- Strategy: prove ∫_S v₁ = ∫_S v₂ for all measurable S, then apply uniqueness
  have hv_eq : v₁ =ᵐ[Measure.map W μ] v₂ := by
    -- First establish Law(W) = Law(W') from the pair law
    have h_law_eq : Measure.map W μ = Measure.map W' μ := by
      rw [← Measure.snd_map_prodMk₀ (Y := W) hZ.aemeasurable,
          ← Measure.snd_map_prodMk₀ (Y := W') hZ.aemeasurable, hPair]

    -- Show v₁ and v₂ are integrable on Law(W)
    have hv₁_int : Integrable v₁ (Measure.map W μ) :=
      (integrable_map_measure hv₁_meas.aestronglyMeasurable hW.aemeasurable).mpr
        (integrable_condExp.congr hV_eq)
    have hv₂_int : Integrable v₂ (Measure.map W μ) := h_law_eq ▸
      (integrable_map_measure hv₂_meas.aestronglyMeasurable hW'.aemeasurable).mpr
        (integrable_condExp.congr hV'_eq)

    -- Main proof: show ∫_S v₁ = ∫_S v₂ for all measurable S using CE properties + pair law
    refine Integrable.ae_eq_of_forall_setIntegral_eq v₁ v₂ hv₁_int hv₂_int fun S hS hS_fin => ?_

    -- For measurable S ⊆ γ, prove ∫_S v₁ d[Law(W)] = ∫_S v₂ d[Law(W)]
    -- Key insight: Use CE set integral property on W^{-1}(S)
    let T := W ⁻¹' S
    let T' := W' ⁻¹' S

    have hT_meas : MeasurableSet[MeasurableSpace.comap W inferInstance] T := ⟨S, hS, rfl⟩
    have hT'_meas : MeasurableSet[MeasurableSpace.comap W' inferInstance] T' := ⟨S, hS, rfl⟩

    calc ∫ y in S, v₁ y ∂(Measure.map W μ)
        = ∫ ω in T, (v₁ ∘ W) ω ∂μ := by
          -- Change of variables for set integral
          rw [setIntegral_map hS hv₁_meas.aestronglyMeasurable hW.aemeasurable]
          rfl
      _ = ∫ ω in T, V ω ∂μ := by
          -- V = v₁∘W a.e.
          refine setIntegral_congr_ae (hW hS) ?_
          filter_upwards [hV_eq] with ω h_eq h_mem
          exact h_eq.symm
      _ = ∫ ω in T, (ψ ∘ Z) ω ∂μ := by
          -- Defining property of CE: ∫_T V = ∫_T (ψ∘Z) for T ∈ σ(W)
          have hm_le : MeasurableSpace.comap W inferInstance ≤ (inferInstance : MeasurableSpace Ω) := by
            intro s hs
            obtain ⟨t, ht, rfl⟩ := hs
            exact hW ht
          exact haveI : SigmaFinite (μ.trim hm_le) := inferInstance
            setIntegral_condExp hm_le hψ_int hT_meas
      _ = ∫ ω in T', (ψ ∘ Z) ω ∂μ := by
          -- Pair law: T and T' have same (ψ∘Z)-integral via measure equality
          -- From hPair: law(Z,W) = law(Z,W'), transfer integral via product measure
          -- Key: ∫_{W^{-1}(S)} ψ(Z) dμ = ∫ ψ(z) · 1_S(w) d[law(Z,W)]
          --                             = ∫ ψ(z) · 1_S(w) d[law(Z,W')]  (by hPair)
          --                             = ∫_{W'^{-1}(S)} ψ(Z) dμ
          have hprod_int : ∫ ω, (ψ ∘ Z) ω * (S.indicator (fun _ => 1) ∘ W) ω ∂μ =
                           ∫ ω, (ψ ∘ Z) ω * (S.indicator (fun _ => 1) ∘ W') ω ∂μ := by
            -- Apply topology-free integral transfer via pushforward measures
            let g : β × γ → ℝ := fun (z, w) => ψ z * S.indicator (fun _ => 1) w

            have hg_meas : Measurable g :=
              (hψ.comp measurable_fst).mul ((measurable_const.indicator hS).comp measurable_snd)

            -- Prove g ∘ (Z, W) is integrable
            have hg_int : Integrable (fun ω => g (Z ω, W ω)) μ := by
              show Integrable (fun ω => (ψ ∘ Z) ω * (S.indicator (fun _ => 1) ∘ W) ω) μ
              -- Rewrite as indicator * ψ to match bdd_mul' signature
              suffices Integrable (fun ω => (S.indicator (fun _ => (1:ℝ)) ∘ W) ω * (ψ ∘ Z) ω) μ by
                convert this using 1
                ext ω
                ring
              -- Indicator function is bounded
              have hind_bdd : ∀ᵐ (ω : Ω) ∂μ, ‖(S.indicator (fun _ => (1:ℝ)) ∘ W) ω‖ ≤ 1 := by
                filter_upwards with ω
                simp [Set.indicator]
                split_ifs <;> norm_num
              -- Indicator is ae strongly measurable
              have hind_ae : AEStronglyMeasurable (S.indicator (fun _ => (1:ℝ)) ∘ W) μ :=
                (measurable_const.indicator hS).comp_aemeasurable hW.aemeasurable |>.aestronglyMeasurable
              -- Apply bounded multiplication: proves (indicator * integrable) is integrable
              exact Integrable.bdd_mul' hψ_int hind_ae hind_bdd

            -- Prove the pair maps are measurable
            have hZW_meas : Measurable fun ω => (Z ω, W ω) := hZ.prodMk hW
            have hZW'_meas : Measurable fun ω => (Z ω, W' ω) := hZ.prodMk hW'

            -- Apply integral_pair_transfer
            calc ∫ ω, (ψ ∘ Z) ω * (S.indicator (fun _ => 1) ∘ W) ω ∂μ
                = ∫ ω, g (Z ω, W ω) ∂μ := rfl
              _ = ∫ ω, g (Z ω, W' ω) ∂μ :=
                  integral_pair_transfer hZW_meas hZW'_meas hPair hg_meas hg_int
              _ = ∫ ω, (ψ ∘ Z) ω * (S.indicator (fun _ => 1) ∘ W') ω ∂μ := rfl
          -- Convert product form back to set integral form
          have : ∫ ω in T, (ψ ∘ Z) ω ∂μ = ∫ ω, (ψ ∘ Z) ω * (S.indicator (fun _ => 1) ∘ W) ω ∂μ := by
            rw [← integral_indicator (hW hS)]
            congr 1; ext ω
            simp [Set.indicator]
          rw [this, hprod_int]
          rw [← integral_indicator (hW' hS)]
          congr 1; ext ω
          simp [Set.indicator]
      _ = ∫ ω in T', V' ω ∂μ := by
          -- Defining property of CE for V'
          have hm'_le : MeasurableSpace.comap W' inferInstance ≤ (inferInstance : MeasurableSpace Ω) := by
            intro s hs
            obtain ⟨t, ht, rfl⟩ := hs
            exact hW' ht
          exact haveI : SigmaFinite (μ.trim hm'_le) := inferInstance
            (setIntegral_condExp hm'_le hψ_int hT'_meas).symm
      _ = ∫ ω in T', (v₂ ∘ W') ω ∂μ := by
          -- V' = v₂∘W' a.e.
          refine setIntegral_congr_ae (hW' hS) ?_
          filter_upwards [hV'_eq] with ω h_eq h_mem
          exact h_eq
      _ = ∫ y in S, v₂ y ∂(Measure.map W' μ) := by
          -- Change of variables back
          rw [setIntegral_map hS hv₂_meas.aestronglyMeasurable hW'.aemeasurable]
          rfl
      _ = ∫ y in S, v₂ y ∂(Measure.map W μ) := by
          -- Law(W) = Law(W')
          rw [h_law_eq]

  -- Step 3: Clip to enforce pointwise bounds
  have hv₁_bdd : ∀ᵐ y ∂(Measure.map W μ), ‖v₁ y‖ ≤ C := by
    -- V = μ[(ψ ∘ Z)|comap W] is bounded by C
    -- We have ‖ψ (Z ω)‖ ≤ C a.e., which gives |ψ (Z ω)| ≤ C a.e. since C ≥ 0
    have hψ_bdd' : ∀ᵐ ω ∂μ, |ψ (Z ω)| ≤ C := by
      filter_upwards [hψ_bdd] with ω hω
      exact Real.norm_eq_abs _ ▸ hω
    -- Apply mathlib's ae_bdd_condExp_of_ae_bdd
    have hV_bdd : ∀ᵐ ω ∂μ, |V ω| ≤ C :=
      MeasureTheory.ae_bdd_condExp_of_ae_bdd (R := ⟨C, hC⟩) hψ_bdd'
    -- V = v₁ ∘ W a.e., so |v₁ (W ω)| ≤ C a.e.
    have : ∀ᵐ ω ∂μ, |v₁ (W ω)| ≤ C := by
      filter_upwards [hV_bdd, hV_eq] with ω hω_bdd hω_eq
      calc |v₁ (W ω)|
          = |(v₁ ∘ W) ω| := rfl
        _ = |V ω| := by rw [← hω_eq]
        _ ≤ C := hω_bdd
    -- Convert to norm and transfer to Measure.map W μ
    have : ∀ᵐ ω ∂μ, ‖v₁ (W ω)‖ ≤ C := by
      filter_upwards [this] with ω hω
      rwa [Real.norm_eq_abs]
    -- Transfer to Measure.map W μ using ae_map_iff
    -- Need to show {y | ‖v₁ y‖ ≤ C} is measurable
    have hmeas : MeasurableSet {y : γ | ‖v₁ y‖ ≤ C} := by
      -- ‖v₁ ·‖ is measurable as composition of measurable v₁ and continuous norm
      have : Measurable fun y => ‖v₁ y‖ := hv₁_meas.norm
      exact this (measurableSet_Iic : MeasurableSet (Set.Iic C))
    rwa [ae_map_iff hW.aemeasurable hmeas]

  obtain ⟨v, hv_meas, hv_bdd, hv_eq_v₁⟩ := exists_clipped_version v₁ C hC hv₁_meas hv₁_bdd

  -- Step 4: Pull back the equalities
  refine ⟨v, hv_meas, hv_bdd, ?_, ?_⟩
  · -- V = v ∘ W a.e.
    calc V
        =ᵐ[μ] v₁ ∘ W := hV_eq
      _ =ᵐ[μ] v ∘ W := by
          -- v₁ = v a.e. on Law(W), so v₁ ∘ W = v ∘ W a.e. on μ
          exact (MeasureTheory.ae_eq_comp hW.aemeasurable hv_eq_v₁).symm
  · -- V' = v ∘ W' a.e.
    -- Law(W') = Law(W) from pair law (marginal equality)
    have h_law_eq : Measure.map W' μ = Measure.map W μ := by
      have h1 : Measure.map W μ = (Measure.map (fun ω => (Z ω, W ω)) μ).map Prod.snd := by
        rw [Measure.map_map measurable_snd (hZ.prodMk hW)]; rfl
      have h2 : Measure.map W' μ = (Measure.map (fun ω => (Z ω, W' ω)) μ).map Prod.snd := by
        rw [Measure.map_map measurable_snd (hZ.prodMk hW')]; rfl
      rw [h1, h2, hPair]
    calc V'
        =ᵐ[μ] v₂ ∘ W' := hV'_eq
      _ =ᵐ[μ] v₁ ∘ W' := by
          have hv_eq' : v₁ =ᵐ[Measure.map W' μ] v₂ := h_law_eq ▸ hv_eq
          exact (MeasureTheory.ae_eq_comp hW'.aemeasurable hv_eq').symm
      _ =ᵐ[μ] v ∘ W' := by
          have hv_eq' : v =ᵐ[Measure.map W' μ] v₁ := h_law_eq ▸ hv_eq_v₁
          exact (MeasureTheory.ae_eq_comp hW'.aemeasurable hv_eq').symm

/-- **Common Version Lemma:** When (Z,W) and (Z,W') have the same distribution,
conditional expectations V = μ[ψ(Z) | σ(W)] and V' = μ[ψ(Z) | σ(W')] admit a common
Borel representative v : γ → ℝ such that V = v∘W and V' = v∘W' a.e.

This is a key lemma for the swap-condition-swap back technique: it allows us to transfer
conditional expectations between the two probability spaces via the shared regression function v.

**Proof strategy:**
1. By Doob-Dynkin, V = v₁∘W and V' = v₂∘W' for some measurable v₁, v₂
2. For any bounded measurable h : γ → ℝ:
   ∫ (v₁*h)∘W dμ = ∫ ψ(Z)*(h∘W) dμ   (defining property of V)
   ∫ ψ(Z)*(h∘W) dμ = ∫ ψ(Z)*(h∘W') dμ  (from pair law equality)
   ∫ ψ(Z)*(h∘W') dμ = ∫ (v₂*h)∘W' dμ  (defining property of V')
3. Since Law(W) = Law(W') (marginal of pair law), this implies
   ∫ v₁*h d[Law(W)] = ∫ v₂*h d[Law(W)]
4. Therefore v₁ = v₂ a.e. w.r.t. Law(W), giving the common representative v

**Not in mathlib:** This requires custom proof from first principles.
-/
lemma common_version_condExp
  {Ω β γ : Type*}
  [MeasurableSpace Ω] [MeasurableSpace β] [MeasurableSpace γ]
  {μ : Measure Ω} [IsProbabilityMeasure μ]
  (Z : Ω → β) (W W' : Ω → γ) (ψ : β → ℝ)
  (hZ : Measurable Z) (hW : Measurable W) (hW' : Measurable W')
  (hψ : Measurable ψ) (hψ_bdd : ∀ z, ‖ψ z‖ ≤ 1)
  (hψ_int : Integrable (ψ ∘ Z) μ)
  (h_pair : Measure.map (fun ω => (Z ω, W ω)) μ =
            Measure.map (fun ω => (Z ω, W' ω)) μ) :
  ∃ v : γ → ℝ,
    (∀ᵐ ω ∂μ, μ[(ψ ∘ Z) | MeasurableSpace.comap W inferInstance] ω = v (W ω)) ∧
    (∀ᵐ ω ∂μ, μ[(ψ ∘ Z) | MeasurableSpace.comap W' inferInstance] ω = v (W' ω)) := by
  -- Use the bounded version and drop the boundedness constraint
  obtain ⟨v, _, _, hv_W, hv_W'⟩ :=
    common_version_condexp_bdd (C := 1) (by norm_num : (0:ℝ) ≤ 1)
      hZ hW hW' hψ hψ_int (by filter_upwards with ω; exact hψ_bdd (Z ω)) h_pair
  exact ⟨v, hv_W, hv_W'⟩

/-- **Enhanced Common Version Lemma with Measurability and Boundedness:**
A common Borel version for the two conditional expectations E[ψ|σ(W)] and E[ψ|σ(W')].
If |ψ| ≤ 1, we can choose v with |v| ≤ 1 pointwise and v Borel-measurable.

This uses only the pair law equality (Z,W) =^d (Z,W') (a marginal of the triple law),
Doob-Dynkin factorization, and the defining property of conditional expectation.

**Key improvements over basic common_version_condExp:**
- Asserts Measurable v (from Doob-Dynkin)
- Asserts ∀ w, |v w| ≤ 1 when |ψ| ≤ 1 (from conditional expectation bounds)
- Required for test_fn_pair_law and swap-based proofs
-/
lemma common_version_condExp_with_props
  {Ω β γ : Type*}
  [MeasurableSpace Ω] [MeasurableSpace β] [MeasurableSpace γ]
  {μ : Measure Ω} [IsProbabilityMeasure μ]
  (Z : Ω → β) (W W' : Ω → γ) (ψ : β → ℝ)
  (hZ : Measurable Z) (hW : Measurable W) (hW' : Measurable W')
  (hψ : Measurable ψ) (hψ_bdd : ∀ z, ‖ψ z‖ ≤ 1)
  (hψ_int : Integrable (ψ ∘ Z) μ)
  (h_pair : Measure.map (fun ω => (Z ω, W ω)) μ =
            Measure.map (fun ω => (Z ω, W' ω)) μ) :
  ∃ v : γ → ℝ,
    Measurable v ∧
    (∀ w, ‖v w‖ ≤ 1) ∧
    (∀ᵐ ω ∂μ, μ[(ψ ∘ Z) | MeasurableSpace.comap W inferInstance] ω = v (W ω)) ∧
    (∀ᵐ ω ∂μ, μ[(ψ ∘ Z) | MeasurableSpace.comap W' inferInstance] ω = v (W' ω)) := by
  -- Use the infrastructure lemma with C = 1
  exact common_version_condexp_bdd (C := 1) (by norm_num) hZ hW hW' hψ hψ_int
    (by filter_upwards with ω; exact hψ_bdd (Z ω)) h_pair

end Exchangeability.DeFinetti.ViaMartingale
