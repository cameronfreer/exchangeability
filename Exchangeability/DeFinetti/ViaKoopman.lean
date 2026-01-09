/-
Copyright (c) 2025 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Exchangeability.DeFinetti.ViaKoopman.ContractableFactorization
import Exchangeability.DeFinetti.ViaKoopman.DirectingKernel
import Exchangeability.DeFinetti.CommonEnding
import Exchangeability.Util.StrictMono

/-!
# de Finetti's Theorem via Contractability (Kallenberg's First Proof)

This file provides de Finetti's theorem using contractability directly, following
Kallenberg's "first proof" which uses disjoint-block averaging rather than permutations.

## Main results

* `deFinetti_viaKoopman_path`: de Finetti's theorem from contractability (path-space version).
  For a contractable sequence on a standard Borel space, there exists a kernel ν
  such that the coordinates are conditionally i.i.d. given ν.

## Mathematical overview

The key insight of Kallenberg's first proof is that contractability (invariance under
strictly monotone subsequences) directly implies conditional i.i.d., without going
through exchangeability.

The proof proceeds as follows:

1. **Block injection**: For `m` blocks of size `n`, define strictly monotone maps
   `ρⱼ : ℕ → ℕ` that select one element from each block.

2. **Contractability application**: For each choice function `j : Fin m → Fin n`,
   the block injection `ρⱼ` is strictly monotone, so contractability gives:
   `∫ ∏ fᵢ(ωᵢ) dμ = ∫ ∏ fᵢ(ω(ρⱼ(i))) dμ`

3. **Averaging**: Sum over all `n^m` choice functions to get:
   `∫ ∏ fᵢ(ωᵢ) dμ = ∫ ∏ blockAvg_i dμ`

4. **L¹ convergence**: As `n → ∞`, block averages converge in L¹ to conditional
   expectations (using Cesàro convergence).

5. **Factorization**: Taking limits yields:
   `CE[∏ fᵢ(ωᵢ) | mSI] = ∏ CE[fᵢ(ω₀) | mSI]` a.e.

6. **Kernel construction**: The product factorization gives kernel independence,
   from which we construct the directing measure ν.

## References

* Kallenberg (2005), *Probabilistic Symmetries and Invariance Principles*, Chapter 1
-/

open Filter MeasureTheory

noncomputable section

namespace Exchangeability.DeFinetti

open MeasureTheory Filter Topology ProbabilityTheory
open Exchangeability.Ergodic
open Exchangeability.PathSpace
open Exchangeability.DeFinetti.ViaKoopman
open Exchangeability.Util.StrictMono (injective_implies_strictMono_perm)
open scoped BigOperators

variable {α : Type*} [MeasurableSpace α] [StandardBorelSpace α]

-- Short notation for shift-invariant σ-algebra
local notation "mSI" => shiftInvariantSigma (α := α)

/-- de Finetti's Theorem from contractability (Kallenberg's first proof).

For a contractable probability measure on path space where the shift is measure-preserving,
there exists a kernel ν (the "directing measure") such that the coordinates are
conditionally i.i.d. given ν.

**Hypotheses:**
- `hσ`: The shift map is measure-preserving
- `hContract`: The measure is contractable (invariant under strictly monotone subsequences)

**Conclusion:**
There exists a kernel `ν : Ω[α] → Measure α` such that:
1. `ν ω` is a probability measure for a.e. ω
2. For any bounded measurable functions `fs : Fin m → α → ℝ`:
   `∫ ∏ fᵢ(ωᵢ) dμ = ∫ (∏ᵢ ∫ fᵢ dν(ω)) dμ(ω)`

This is the **product factorization** form of de Finetti:
- LHS: Product at different coordinates ω(0), ω(1), ..., ω(m-1)
- RHS: Product of expectations, each ∫ fᵢ dν evaluated against same ν(ω)

**Mathematical content:**
This is the hard direction of de Finetti's equivalence:
  Contractable → Conditionally i.i.d.

The proof uses disjoint-block averaging (see `ContractableFactorization.lean`):
1. For each n, partition into blocks and average over block positions
2. Contractability ensures the integral is unchanged
3. As n → ∞, block averages converge to conditional expectations
4. The product factorization gives kernel independence
5. The kernel ν is constructed from the conditional expectation
-/
private theorem deFinetti_viaKoopman_path
    {μ : Measure (Ω[α])} [IsProbabilityMeasure μ]
    (hσ : MeasurePreserving shift μ μ)
    (hContract : ∀ (m : ℕ) (k : Fin m → ℕ), StrictMono k →
        Measure.map (fun ω i => ω (k i)) μ = Measure.map (fun ω (i : Fin m) => ω i.val) μ) :
    ∃ (ν : (Ω[α]) → Measure α),
      (∀ᵐ ω ∂μ, IsProbabilityMeasure (ν ω)) ∧
      (∀ (m : ℕ) (fs : Fin m → α → ℝ),
        (∀ i, Measurable (fs i)) →
        (∀ i, ∃ C, ∀ x, |fs i x| ≤ C) →
        ∫ ω, (∏ i : Fin m, fs i (ω i.val)) ∂μ =
          ∫ ω, (∏ i : Fin m, ∫ x, fs i x ∂(ν ω)) ∂μ) := by
  -- Use ν from KernelIndependence.lean (the regular conditional distribution)
  use ν (μ := μ)
  constructor
  · -- Step 1: ν ω is a probability measure for a.e. ω
    -- This follows from rcdKernel being a Markov kernel
    apply ae_of_all
    intro ω
    exact IsMarkovKernel.isProbabilityMeasure ω
  · -- Step 2: Product factorization for bounded measurable functions
    intro m fs hfs_meas hfs_bd
    -- Key step: for each i, ∫ fs_i d(ν ω) =ᵃᵉ μ[fs_i ∘ π0 | mSI](ω)
    have h_ν_eq_ce : ∀ i, (fun ω => ∫ x, fs i x ∂(ν (μ := μ) ω)) =ᵐ[μ]
        μ[fun ω' => fs i (ω' 0) | mSI] := by
      intro i
      have hfi_int : Integrable (fun ω' => fs i (ω' 0)) μ := by
        obtain ⟨C, hC⟩ := hfs_bd i
        apply Integrable.of_bound
          ((hfs_meas i).comp (measurable_pi_apply 0)).aestronglyMeasurable C
        exact ae_of_all μ (fun ω => (Real.norm_eq_abs _).trans_le (hC (ω 0)))
      have h_ce := condExp_ae_eq_integral_condExpKernel (shiftInvariantSigma_le (α := α)) hfi_int
      filter_upwards [h_ce] with ω hω
      calc ∫ x, fs i x ∂(ν (μ := μ) ω)
          = ∫ y, fs i (y 0) ∂(condExpKernel μ mSI ω) := integral_ν_eq_integral_condExpKernel ω (hfs_meas i)
        _ = μ[fun ω' => fs i (ω' 0) | mSI] ω := hω.symm
    -- Product of a.e. equalities
    have h_prod_ae : (fun ω => ∏ i : Fin m, ∫ x, fs i x ∂(ν (μ := μ) ω)) =ᵐ[μ]
        (fun ω => ∏ i : Fin m, μ[fun ω' => fs i (ω' 0) | mSI] ω) := by
      have h_all := ae_all_iff.mpr h_ν_eq_ce
      filter_upwards [h_all] with ω hω
      exact Finset.prod_congr rfl (fun i _ => hω i)
    -- Apply condexp_product_factorization_contractable
    have h_fact := condexp_product_factorization_contractable hσ hContract fs hfs_meas hfs_bd
    -- The factorization gives: μ[(∏ fᵢ(ωᵢ)) | mSI] =ᵐ ∏ μ[fᵢ(ω₀) | mSI]
    -- Integrate both sides using tower property
    have h_lhs_tower : ∫ ω, (∏ i : Fin m, fs i (ω i.val)) ∂μ =
        ∫ ω, μ[(fun ω' => ∏ i : Fin m, fs i (ω' i.val)) | mSI] ω ∂μ := by
      symm
      apply integral_condExp (shiftInvariantSigma_le (α := α))
    rw [h_lhs_tower]
    apply integral_congr_ae
    filter_upwards [h_fact, h_prod_ae] with ω h_fact_ω h_prod_ω
    rw [h_fact_ω, ← h_prod_ω]

/-- Contractability implies conditional i.i.d. (Kallenberg's first proof).

This is the key implication in de Finetti's theorem: a contractable sequence
is conditionally i.i.d. given the tail σ-algebra.

This theorem provides the **standard form** of conditionally i.i.d.:
1. ν(ω) is the conditional distribution at coordinate 0 given mSI
2. The conditional expectation of the indicator of a cylinder set factors as
   a product of conditional expectations of single-coordinate indicators
-/
private theorem conditionallyIID_of_contractable_path
    {μ : Measure (Ω[α])} [IsProbabilityMeasure μ]
    (hσ : MeasurePreserving shift μ μ)
    (hContract : ∀ (m : ℕ) (k : Fin m → ℕ), StrictMono k →
        Measure.map (fun ω i => ω (k i)) μ = Measure.map (fun ω (i : Fin m) => ω i.val) μ) :
    ∃ (ν : (Ω[α]) → Measure α),
      (∀ᵐ ω ∂μ, IsProbabilityMeasure (ν ω)) ∧
      -- Identical distribution: ν ω = conditional distribution at coordinate 0
      (∀ s, MeasurableSet s →
        (fun ω => (ν ω s).toReal) =ᵐ[μ]
          μ[(fun ω' => Set.indicator s (1 : α → ℝ) (ω' 0)) | mSI]) ∧
      -- Conditional independence: joint CE factors as product
      (∀ (m : ℕ) (sets : Fin m → Set α),
        (∀ i, MeasurableSet (sets i)) →
        μ[(fun ω' => Set.indicator (⋂ (i : Fin m), (fun ω'' => ω'' i.val) ⁻¹' sets i) (1 : Ω[α] → ℝ) ω') | mSI]
          =ᵐ[μ] fun ω =>
            ∏ i : Fin m, μ[(fun ω' => Set.indicator ((fun ω'' => ω'' 0) ⁻¹' sets i) (1 : Ω[α] → ℝ) ω') | mSI] ω) := by
  -- Use ν from KernelIndependence.lean
  use ν (μ := μ)
  refine ⟨?_, ?_, ?_⟩
  · -- Part 1: ν ω is a probability measure for a.e. ω
    apply ae_of_all
    intro ω
    exact IsMarkovKernel.isProbabilityMeasure ω
  · -- Part 2: Identical distribution - ν ω s = CE[1_s(ω₀) | mSI](ω) a.e.
    -- This is the definition of ν via rcdKernel (pushforward of condExpKernel by π₀)
    --
    -- By definition:
    --   ν ω = rcdKernel ω
    --       = (condExpKernel μ mSI).map π₀ ω
    --
    -- For a measurable set s ⊆ α:
    --   (ν ω) s = (condExpKernel μ mSI ω) (π₀⁻¹(s))
    --           = (condExpKernel μ mSI ω) {ω' | ω' 0 ∈ s}
    --
    -- And by condExp_ae_eq_integral_condExpKernel:
    --   CE[1_s(ω₀) | mSI] =ᵐ ∫ 1_{ω' 0 ∈ s} d(condExpKernel μ mSI ω)
    --                     = (condExpKernel μ mSI ω) {ω' | ω' 0 ∈ s}
    --                     = (ν ω) s
    --
    -- The proof requires unwinding the definitions of ν, rcdKernel, and condExpKernel.
    intro s hs
    -- The integrand fun ω' => 1_s(ω' 0) is f ∘ π0 where f = Set.indicator s 1
    let f : α → ℝ := Set.indicator s 1
    have hf_meas : Measurable f := measurable_const.indicator hs
    have hf_int : Integrable (f ∘ π0) μ := by
      apply Integrable.indicator
      · exact integrable_const 1
      · exact (measurable_pi0 (α := α)) hs
    -- By condExp_ae_eq_integral_condExpKernel:
    -- μ[f ∘ π0 | mSI] =ᵃᵉ ∫ y, f (y 0) ∂(condExpKernel μ mSI ω)
    have h_ce := condExp_ae_eq_integral_condExpKernel (shiftInvariantSigma_le (α := α)) hf_int
    -- Combine all the identities
    filter_upwards [h_ce] with ω hω
    calc (ν (μ := μ) ω s).toReal
        = (ν (μ := μ) ω).real s := by simp only [Measure.real]
      _ = ∫ x, f x ∂(ν (μ := μ) ω) := (integral_indicator_one hs).symm
      _ = ∫ y, f (y 0) ∂(condExpKernel μ mSI ω) := integral_ν_eq_integral_condExpKernel ω hf_meas
      _ = μ[(f ∘ π0) | mSI] ω := hω.symm
  · -- Part 3: Conditional independence - CE factors as product for indicator functions
    -- This is exactly condexp_product_factorization_contractable applied to indicators
    intro m sets hsets
    -- Define indicator functions fs : Fin m → α → ℝ
    let fs : Fin m → α → ℝ := fun i => Set.indicator (sets i) 1
    -- These are bounded (by 1) and measurable
    have hfs_meas : ∀ i, Measurable (fs i) := fun i =>
      measurable_const.indicator (hsets i)
    have hfs_bd : ∀ i, ∃ C, ∀ x, |fs i x| ≤ C := fun i => ⟨1, fun x => by
      simp only [fs]
      by_cases hx : x ∈ sets i
      · simp [Set.indicator_of_mem hx]
      · simp [Set.indicator_of_notMem hx]⟩
    -- Apply condexp_product_factorization_contractable
    have h_fact := condexp_product_factorization_contractable hσ hContract fs hfs_meas hfs_bd
    -- The LHS indicator is the product of individual indicators
    -- 1_{∩ᵢ ωᵢ ∈ sets i} = ∏ᵢ 1_{sets i}(ωᵢ)
    have h_prod_eq : (fun ω' => Set.indicator
        (⋂ (i : Fin m), (fun ω'' => ω'' i.val) ⁻¹' sets i) (1 : Ω[α] → ℝ) ω')
        = (fun ω' => ∏ i : Fin m, fs i (ω' i.val)) := by
      ext ω'
      simp only [fs]
      by_cases h : ω' ∈ ⋂ (i : Fin m), (fun ω'' => ω'' i.val) ⁻¹' sets i
      · -- ω' is in the intersection, so each coordinate is in the corresponding set
        have h' : ∀ i : Fin m, ω' i.val ∈ sets i := by
          simpa only [Set.mem_iInter, Set.mem_preimage] using h
        rw [Set.indicator_of_mem h]
        -- Each indicator is 1
        have h_each : ∀ i, Set.indicator (sets i) (1 : α → ℝ) (ω' i.val) = 1 := by
          intro i
          rw [Set.indicator_of_mem (h' i)]
          rfl
        simp only [h_each, Finset.prod_const_one, Pi.one_apply]
      · -- ω' is not in the intersection
        rw [Set.indicator_of_notMem h]
        -- At least one indicator is 0
        simp only [Set.mem_iInter, Set.mem_preimage, not_forall] at h
        obtain ⟨i, hi⟩ := h
        symm
        apply Finset.prod_eq_zero (Finset.mem_univ i)
        rw [Set.indicator_of_notMem hi]
    -- The RHS factors as product of CEs at coordinate 0
    -- The key is that 1_{ω' 0 ∈ s}(ω') = 1_s(ω' 0) for ω' : Ω[α]
    have h_integrands_eq : ∀ i, (fun ω' : Ω[α] => Set.indicator ((fun ω'' => ω'' 0) ⁻¹' sets i)
        (1 : Ω[α] → ℝ) ω') = (fun ω' => fs i (ω' 0)) := by
      intro i
      ext ω'
      -- Both are indicator functions that evaluate to 1 iff ω' 0 ∈ sets i
      simp only [fs]
      rfl
    have h_rhs_eq : (fun ω => ∏ i : Fin m,
        μ[(fun ω' => Set.indicator ((fun ω'' => ω'' 0) ⁻¹' sets i) (1 : Ω[α] → ℝ) ω') | mSI] ω)
        = (fun ω => ∏ i : Fin m, μ[(fun ω' => fs i (ω' 0)) | mSI] ω) := by
      ext ω
      apply Finset.prod_congr rfl
      intro i _
      simp only [h_integrands_eq i]
    -- Combine using h_fact
    rw [h_prod_eq, h_rhs_eq]
    exact h_fact

/-! ### Transfer to General Spaces

The path-space result `conditionallyIID_of_contractable_path` can be transferred to general
random sequences `X : ℕ → Ω → α` via the pushforward measure.

**Key insight**: For `X : ℕ → Ω → α`, the pushforward measure `μ.map (fun ω i => X i ω)`
on path space satisfies the contractability hypothesis if `X` is contractable.
-/

omit [StandardBorelSpace α] in
/-- Transfer path-space contractability to the pushforward of a general sequence.

Given `X : ℕ → Ω → α` that is contractable, the pushforward measure on `Ω[α] = ℕ → α`
satisfies the path-space contractability hypothesis. -/
lemma pathSpace_contractable_of_contractable
    {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ℕ → Ω → α) (hX_meas : ∀ i, Measurable (X i))
    (hContract : Contractable μ X) :
    ∀ (m : ℕ) (k : Fin m → ℕ), StrictMono k →
      Measure.map (fun ω i => ω (k i)) (μ.map (fun ω' i => X i ω')) =
      Measure.map (fun ω (i : Fin m) => ω i.val) (μ.map (fun ω' i => X i ω')) := by
  intro m k hk
  -- The path-space map is the pushforward of the original contractability
  have hφ_meas : Measurable (fun ω' i => X i ω') :=
    measurable_pi_lambda _ (fun i => hX_meas i)
  have hk_meas : Measurable (fun (ω : Ω[α]) i => ω (k i)) :=
    measurable_pi_lambda _ (fun i => measurable_pi_apply (k i))
  have hid_meas : Measurable (fun (ω : Ω[α]) (i : Fin m) => ω i.val) :=
    measurable_pi_lambda _ (fun i => measurable_pi_apply i.val)
  -- Rewrite using composition
  rw [Measure.map_map hk_meas hφ_meas, Measure.map_map hid_meas hφ_meas]
  -- The compositions give the original contractability
  have h1 : (fun ω i => ω (k i)) ∘ (fun ω' i => X i ω') = fun ω' i => X (k i) ω' := rfl
  have h2 : (fun ω (i : Fin m) => ω i.val) ∘ (fun ω' i => X i ω') = fun ω' i => X i.val ω' := rfl
  rw [h1, h2]
  exact hContract m k hk

omit [StandardBorelSpace α] in
/-- Shifting coordinates by +1 preserves the pushforward measure for contractable sequences.

This is the key measure-theoretic step for shift-preservation: if X is contractable,
then μ.map(i ↦ X(i+1)) = μ.map(i ↦ X i).

**Proof outline:**
1. Contractability gives finite-dimensional marginal equality
2. For each n, the marginal on {0,...,n-1} of μ.map(i ↦ X(i+1)) equals
   the marginal of μ.map(i ↦ X i) (by contractability with k(i) = i+1)
3. Apply `measure_eq_of_fin_marginals_eq_prob` to conclude measure equality
-/
lemma measure_map_shift_eq_of_contractable
    {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ℕ → Ω → α) (hX_meas : ∀ i, Measurable (X i))
    (hContract : Contractable μ X) :
    Measure.map (fun ω' i => X (i + 1) ω') μ = Measure.map (fun ω' i => X i ω') μ := by
  -- Both measures are probability measures
  have hφ_meas : Measurable (fun ω' i => X i ω') :=
    measurable_pi_lambda _ (fun i => hX_meas i)
  have hφ1_meas : Measurable (fun ω' i => X (i + 1) ω') :=
    measurable_pi_lambda _ (fun i => hX_meas (i + 1))
  haveI h1 : IsProbabilityMeasure (Measure.map (fun ω' i => X (i + 1) ω') μ) :=
    Measure.isProbabilityMeasure_map hφ1_meas.aemeasurable
  haveI h2 : IsProbabilityMeasure (Measure.map (fun ω' i => X i ω') μ) :=
    Measure.isProbabilityMeasure_map hφ_meas.aemeasurable
  -- Use measure_eq_of_fin_marginals_eq_prob: two probability measures agree iff
  -- their finite marginals agree
  apply Exchangeability.measure_eq_of_fin_marginals_eq_prob (α := α)
  intro n S hS
  -- Need: marginal on first n coords of μ.map(i ↦ X(i+1)) = marginal of μ.map(i ↦ X i)
  -- LHS marginal: μ.map(i < n ↦ X(i+1))
  -- RHS marginal: μ.map(i < n ↦ X i)
  -- By contractability with k(i) = i+1 (strictly monotone): these are equal
  have hk : StrictMono (fun i : Fin n => (i.val + 1 : ℕ)) := by
    intro i j hij
    exact Nat.add_lt_add_right hij 1
  -- The marginal projection
  have h_proj_L : Measure.map (Exchangeability.prefixProj α n) (Measure.map (fun ω' i => X (i + 1) ω') μ)
      = Measure.map (fun ω' (i : Fin n) => X (i.val + 1) ω') μ := by
    rw [Measure.map_map (Exchangeability.measurable_prefixProj (α := α)) hφ1_meas]
    rfl
  have h_proj_R : Measure.map (Exchangeability.prefixProj α n) (Measure.map (fun ω' i => X i ω') μ)
      = Measure.map (fun ω' (i : Fin n) => X i.val ω') μ := by
    rw [Measure.map_map (Exchangeability.measurable_prefixProj (α := α)) hφ_meas]
    rfl
  rw [h_proj_L, h_proj_R]
  -- Now apply contractability: hContract gives measure equality
  have h_eq := hContract n (fun i => i.val + 1) hk
  -- Extract the set-wise equality from measure equality
  rw [h_eq]

/-- Shift-preservation transfers to the pushforward measure.

If `X` is contractable, the pushforward measure is shift-preserving. -/
lemma pathSpace_shift_preserving_of_contractable
    {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ℕ → Ω → α) (hX_meas : ∀ i, Measurable (X i))
    (hContract : Contractable μ X) :
    MeasurePreserving shift (μ.map (fun ω' i => X i ω')) (μ.map (fun ω' i => X i ω')) := by
  constructor
  · exact shift_measurable
  · -- Use contractability with k(i) = i + 1
    have hφ_meas : Measurable (fun ω' i => X i ω') :=
      measurable_pi_lambda _ (fun i => hX_meas i)
    rw [Measure.map_map shift_measurable hφ_meas]
    -- shift ∘ φ = (fun ω i => X (i+1) ω)
    have h_comp : shift ∘ (fun ω' i => X i ω') = fun ω' i => X (i + 1) ω' := by
      ext ω i
      simp [shift]
    rw [h_comp]
    -- Apply the helper lemma
    exact measure_map_shift_eq_of_contractable X hX_meas hContract

omit [StandardBorelSpace α] in
/-- ConditionallyIID transfers between path space and original space.

If `μ_path = μ.map φ` where `φ ω = (fun i => X i ω)`, then
`ConditionallyIID μ_path id ↔ ConditionallyIID μ X`
where `id` on path space is `fun i ω => ω i`. -/
lemma conditionallyIID_transfer
    {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ℕ → Ω → α) (hX_meas : ∀ i, Measurable (X i))
    (hCIID_path : Exchangeability.ConditionallyIID
        (μ.map (fun ω' i => X i ω')) (fun i (ω : Ω[α]) => ω i)) :
    Exchangeability.ConditionallyIID μ X := by
  -- Extract the directing measure from path-space result
  obtain ⟨ν_path, hν_prob, hν_meas, h_bind⟩ := hCIID_path
  -- Define the directing measure on original space via composition
  let φ : Ω → Ω[α] := fun ω' i => X i ω'
  have hφ_meas : Measurable φ := measurable_pi_lambda _ (fun i => hX_meas i)
  -- The directing measure on Ω is ν_path ∘ φ
  let ν : Ω → Measure α := fun ω => ν_path (φ ω)
  use ν
  refine ⟨?_, ?_, ?_⟩
  · -- ν(ω) is a probability measure
    intro ω
    exact hν_prob (φ ω)
  · -- Measurability of ν
    intro B hB
    have : (fun ω => ν ω B) = (fun ω => ν_path (φ ω) B) := rfl
    rw [this]
    exact (hν_meas B hB).comp hφ_meas
  · -- The bind formula
    intro m k hk
    -- LHS: μ.map (fun ω => fun i => X (k i) ω)
    -- This equals (μ.map φ).map (fun ω => fun i => ω (k i))
    have h_lhs : Measure.map (fun ω => fun i : Fin m => X (k i) ω) μ =
        Measure.map (fun (ω : Ω[α]) => fun i : Fin m => ω (k i)) (μ.map φ) := by
      have hk_meas : Measurable (fun (ω : Ω[α]) => fun i : Fin m => ω (k i)) :=
        measurable_pi_lambda _ (fun i => measurable_pi_apply (k i))
      -- Use map_map forward: map f (map g μ) = map (f ∘ g) μ
      rw [Measure.map_map hk_meas hφ_meas]
      -- The composition (fun ω i => ω (k i)) ∘ φ = (fun ω i => X (k i) ω)
      rfl
    -- RHS: μ.bind (fun ω => Measure.pi (fun _ => ν ω))
    -- This equals (μ.map φ).bind (fun ω => Measure.pi (fun _ => ν_path ω))
    have h_rhs : μ.bind (fun ω => Measure.pi fun _ : Fin m => ν ω) =
        (μ.map φ).bind (fun ω => Measure.pi fun _ : Fin m => ν_path ω) := by
      simp only [Measure.bind, ν]
      have h_pi_meas : Measurable (fun ω' : Ω[α] => Measure.pi fun _ : Fin m => ν_path ω') := by
        apply measurable_measure_pi
        · intro ω; exact hν_prob ω
        · intro s hs; exact hν_meas s hs
      rw [Measure.map_map h_pi_meas hφ_meas]
      rfl
    rw [h_lhs, h_rhs]
    -- Now apply the path-space bind formula
    exact h_bind m k hk

/-! ### Bridge from Contractability to ConditionallyIID

The bridge from contractability to the bind-based `Exchangeability.ConditionallyIID` requires
extending from StrictMono indices (which contractability gives) to arbitrary Injective indices
(which `CommonEnding.conditional_iid_from_directing_measure` needs).

The key insight is that any injective function can be sorted to a StrictMono one, and products
are commutative. So for injective k : Fin m → ℕ:
1. Sort k to get sorted : Fin m → ℕ which is StrictMono
2. k = sorted ∘ σ for some permutation σ of Fin m
3. Use contractability with sorted to reduce to consecutive indices
4. Use product commutativity to handle the σ reordering
-/

omit [StandardBorelSpace α] in
/-- Bridge condition for contractable measures: extends from StrictMono to Injective.

This is the key technical step connecting contractability to `conditional_iid_from_directing_measure`.
The proof uses that any injective function on Fin m can be sorted to a StrictMono one.
Then contractability reduces to consecutive indices, and product commutativity handles reordering.

**Proof sketch**:
1. Sort k to get ρ : Fin m → ℕ (StrictMono) and σ : Fin m ≃ Fin m with k = ρ ∘ σ
2. ∏ i, indicator(B i)(ω(k i)) = ∏ j, indicator(B(σ⁻¹ j))(ω(ρ j))  (reorder)
3. By contractability: ∫ ... dμ at ρ-indices = ∫ ... dμ at consecutive indices
4. By condexp_product_factorization_contractable: = ∫ ∏ j, (∫ indicator(B(σ⁻¹ j)) dν) dμ
5. = ∫ ∏ i, ν(B i) dμ  (by product commutativity)
-/
lemma indicator_product_bridge_contractable
    {μ : Measure (Ω[α])} [IsProbabilityMeasure μ] [StandardBorelSpace α]
    (hσ : MeasurePreserving shift μ μ)
    (hContract : ∀ (m : ℕ) (k : Fin m → ℕ), StrictMono k →
        Measure.map (fun ω i => ω (k i)) μ = Measure.map (fun ω (i : Fin m) => ω i.val) μ)
    (m : ℕ) (k : Fin m → ℕ) (hk : Function.Injective k) (B : Fin m → Set α)
    (hB_meas : ∀ i, MeasurableSet (B i)) :
    ∫⁻ ω, ∏ i : Fin m, ENNReal.ofReal ((B i).indicator (fun _ => (1 : ℝ)) (ω (k i))) ∂μ
      = ∫⁻ ω, ∏ i : Fin m, (ν (μ := μ) ω) (B i) ∂μ := by
  classical
  -- Handle m = 0 trivially (empty products are 1)
  rcases Nat.eq_zero_or_pos m with rfl | hm_pos
  · simp only [Finset.univ_eq_empty, Finset.prod_empty]
  -- For m > 0, we proceed by sorting k
  -- Step 1: Get σ : Perm (Fin m) such that ρ := fun i => k (σ i) is StrictMono
  obtain ⟨σ, hρ_mono⟩ := injective_implies_strictMono_perm k hk
  -- Define ρ := k ∘ σ (the sorted version of k)
  let ρ : Fin m → ℕ := fun i => k (σ i)
  -- Step 2: Product reindexing lemmas (k i = ρ (σ⁻¹ i) by definition)
  have h_lhs_reindex : ∀ ω : Ω[α],
      ∏ i, (B i).indicator (fun _ => (1 : ℝ)) (ω (k i)) =
      ∏ j, (B (σ j)).indicator (fun _ => (1 : ℝ)) (ω (ρ j)) := fun ω =>
    (Equiv.prod_comp σ (fun i => (B i).indicator (fun _ => (1 : ℝ)) (ω (k i)))).symm
  have h_rhs_reindex : ∀ ω : Ω[α],
      ∏ i, (ν (μ := μ) ω) (B i) = ∏ j, (ν (μ := μ) ω) (B (σ j)) := fun ω =>
    (Equiv.prod_comp σ (fun i => (ν (μ := μ) ω) (B i))).symm
  -- Step 3: Use contractability to reduce from ρ-indices to consecutive indices
  have h_contr_ρ := hContract m ρ hρ_mono
  -- Step 4: For consecutive indices, apply the existing factorization
  let fs_σ : Fin m → α → ℝ := fun j => (B (σ j)).indicator (fun _ => 1)
  have hfs_meas : ∀ j, Measurable (fs_σ j) := fun j =>
    Measurable.indicator measurable_const (hB_meas (σ j))
  have hfs_bd : ∀ j, ∃ C, ∀ x, |fs_σ j x| ≤ C := fun j => ⟨1, fun x => by
    by_cases h : x ∈ B (σ j) <;> simp [fs_σ, h]⟩
  -- Use conditional expectation factorization
  have h_ν_eq_ce : ∀ j, (fun ω => ∫ x, fs_σ j x ∂(ν (μ := μ) ω)) =ᵐ[μ]
      μ[fun ω' => fs_σ j (ω' 0) | mSI] := by
    intro j
    have hfj_int : Integrable (fun ω' => fs_σ j (ω' 0)) μ := by
      obtain ⟨C, hC⟩ := hfs_bd j
      apply Integrable.of_bound
        ((hfs_meas j).comp (measurable_pi_apply 0)).aestronglyMeasurable C
      exact ae_of_all μ (fun ω => (Real.norm_eq_abs _).trans_le (hC (ω 0)))
    have h_ce := condExp_ae_eq_integral_condExpKernel (shiftInvariantSigma_le (α := α)) hfj_int
    filter_upwards [h_ce] with ω hω
    calc ∫ x, fs_σ j x ∂(ν (μ := μ) ω)
        = ∫ y, fs_σ j (y 0) ∂(condExpKernel μ mSI ω) := integral_ν_eq_integral_condExpKernel ω (hfs_meas j)
      _ = μ[fun ω' => fs_σ j (ω' 0) | mSI] ω := hω.symm
  have h_prod_ae : (fun ω => ∏ j : Fin m, ∫ x, fs_σ j x ∂(ν (μ := μ) ω)) =ᵐ[μ]
      (fun ω => ∏ j : Fin m, μ[fun ω' => fs_σ j (ω' 0) | mSI] ω) := by
    have h_all := ae_all_iff.mpr h_ν_eq_ce
    filter_upwards [h_all] with ω hω
    exact Finset.prod_congr rfl (fun j _ => hω j)
  have h_fact := condexp_product_factorization_contractable hσ hContract fs_σ hfs_meas hfs_bd
  -- Tower property and consecutive-index result
  have h_consec : ∫ ω, (∏ j : Fin m, fs_σ j (ω j.val)) ∂μ =
      ∫ ω, (∏ j : Fin m, ∫ x, fs_σ j x ∂(ν (μ := μ) ω)) ∂μ := by
    have h_lhs_tower : ∫ ω, (∏ j : Fin m, fs_σ j (ω j.val)) ∂μ =
        ∫ ω, μ[(fun ω' => ∏ j : Fin m, fs_σ j (ω' j.val)) | mSI] ω ∂μ := by
      symm; apply integral_condExp (shiftInvariantSigma_le (α := α))
    rw [h_lhs_tower]
    apply integral_congr_ae
    filter_upwards [h_fact, h_prod_ae] with ω h_fact_ω h_prod_ω
    rw [h_fact_ω, ← h_prod_ω]
  have h_ind_integral : ∀ j ω, ∫ x, fs_σ j x ∂(ν (μ := μ) ω) = ((ν (μ := μ) ω) (B (σ j))).toReal :=
    fun j ω => integral_indicator_one (hB_meas (σ j))
  -- Step 5: Integral at ρ-indices equals integral at consecutive indices
  have h_ρ_to_consec : ∫ ω, ∏ j, fs_σ j (ω (ρ j)) ∂μ = ∫ ω, ∏ j, fs_σ j (ω j.val) ∂μ := by
    have hρ_meas : Measurable (fun (ω : Ω[α]) (j : Fin m) => ω (ρ j)) :=
      measurable_pi_lambda _ (fun j => measurable_pi_apply (ρ j))
    have hconsec_meas : Measurable (fun (ω : Ω[α]) (j : Fin m) => ω j.val) :=
      measurable_pi_lambda _ (fun j => measurable_pi_apply j.val)
    have hg_meas : Measurable (fun ω' : Fin m → α => ∏ j, fs_σ j (ω' j)) :=
      Finset.measurable_prod Finset.univ (fun j _ => (hfs_meas j).comp (measurable_pi_apply j))
    calc ∫ ω, ∏ j, fs_σ j (ω (ρ j)) ∂μ
        = ∫ ω', (fun ω'' => ∏ j, fs_σ j (ω'' j)) ω' ∂(Measure.map (fun ω j => ω (ρ j)) μ) := by
            rw [integral_map hρ_meas.aemeasurable hg_meas.aestronglyMeasurable]
      _ = ∫ ω', (fun ω'' => ∏ j, fs_σ j (ω'' j)) ω' ∂(Measure.map (fun ω j => ω j.val) μ) := by
            rw [h_contr_ρ]
      _ = ∫ ω, ∏ j, fs_σ j (ω j.val) ∂μ := by
            rw [integral_map hconsec_meas.aemeasurable hg_meas.aestronglyMeasurable]
  -- Define auxiliary functions for lintegral conversion
  let F_ρ : Ω[α] → ℝ := fun ω => ∏ j, fs_σ j (ω (ρ j))
  let G : Ω[α] → ℝ := fun ω => ∏ j, ((ν (μ := μ) ω) (B (σ j))).toReal
  have hF_nonneg : ∀ ω, 0 ≤ F_ρ ω := fun ω =>
    Finset.prod_nonneg (fun j _ => Set.indicator_nonneg (fun _ _ => zero_le_one) _)
  have hF_bd : ∀ ω, F_ρ ω ≤ 1 := fun ω => by
    apply Finset.prod_le_one (fun j _ => Set.indicator_nonneg (fun _ _ => zero_le_one) _)
    intro j _
    by_cases h : ω (ρ j) ∈ B (σ j)
    · simp only [Set.indicator_of_mem h]; norm_num
    · simp only [Set.indicator_of_notMem h]; norm_num
  have hF_int : Integrable F_ρ μ := by
    apply Integrable.of_bound (C := 1)
    · exact (Finset.measurable_prod Finset.univ (fun j _ =>
        (hfs_meas j).comp (measurable_pi_apply (ρ j)))).aestronglyMeasurable
    · exact ae_of_all μ (fun ω => by simp [Real.norm_eq_abs, abs_of_nonneg (hF_nonneg ω), hF_bd ω])
  have hG_nonneg : ∀ ω, 0 ≤ G ω := fun ω =>
    Finset.prod_nonneg (fun j _ => ENNReal.toReal_nonneg)
  have hG_bd : ∀ ω, G ω ≤ 1 := fun ω => by
    apply Finset.prod_le_one (fun j _ => ENNReal.toReal_nonneg)
    intro j _
    haveI : IsProbabilityMeasure (ν (μ := μ) ω) := ν_isProbabilityMeasure (μ := μ) ω
    exact ENNReal.toReal_le_of_le_ofReal (by linarith : (0 : ℝ) ≤ 1)
      (prob_le_one.trans_eq ENNReal.ofReal_one.symm)
  have hG_int : Integrable G μ := by
    apply Integrable.of_bound (C := 1)
    · exact (Finset.measurable_prod Finset.univ (fun j _ =>
        (ν_eval_measurable (hB_meas (σ j))).ennreal_toReal)).aestronglyMeasurable
    · exact ae_of_all μ (fun ω => by simp [Real.norm_eq_abs, abs_of_nonneg (hG_nonneg ω), hG_bd ω])
  -- Chain of equalities
  calc ∫⁻ ω, ∏ i, ENNReal.ofReal ((B i).indicator (fun _ => (1 : ℝ)) (ω (k i))) ∂μ
      = ∫⁻ ω, ∏ j, ENNReal.ofReal ((B (σ j)).indicator (fun _ => (1 : ℝ)) (ω (ρ j))) ∂μ := by
          congr 1; funext ω
          rw [← ENNReal.ofReal_prod_of_nonneg (fun i _ =>
            Set.indicator_nonneg (fun _ _ => zero_le_one) _)]
          rw [← ENNReal.ofReal_prod_of_nonneg (fun j _ =>
            Set.indicator_nonneg (fun _ _ => zero_le_one) _)]
          congr 1
          exact h_lhs_reindex ω
    _ = ∫⁻ ω, ENNReal.ofReal (F_ρ ω) ∂μ := by
          congr 1; funext ω
          rw [ENNReal.ofReal_prod_of_nonneg (fun j _ => Set.indicator_nonneg (fun _ _ => zero_le_one) _)]
    _ = ENNReal.ofReal (∫ ω, F_ρ ω ∂μ) :=
          (ofReal_integral_eq_lintegral_ofReal hF_int (ae_of_all μ hF_nonneg)).symm
    _ = ENNReal.ofReal (∫ ω, ∏ j, fs_σ j (ω j.val) ∂μ) := by rw [h_ρ_to_consec]
    _ = ENNReal.ofReal (∫ ω, G ω ∂μ) := by
          congr 1
          rw [h_consec]
          apply integral_congr_ae
          filter_upwards with ω
          simp only [G]; congr 1; ext j; exact h_ind_integral j ω
    _ = ∫⁻ ω, ENNReal.ofReal (G ω) ∂μ :=
          ofReal_integral_eq_lintegral_ofReal hG_int (ae_of_all μ hG_nonneg)
    _ = ∫⁻ ω, ∏ j, ENNReal.ofReal (((ν (μ := μ) ω) (B (σ j))).toReal) ∂μ := by
          congr 1; funext ω
          rw [ENNReal.ofReal_prod_of_nonneg (fun j _ => ENNReal.toReal_nonneg)]
    _ = ∫⁻ ω, ∏ j, (ν (μ := μ) ω) (B (σ j)) ∂μ := by
          congr 1; funext ω; congr 1; ext j
          haveI : IsProbabilityMeasure (ν (μ := μ) ω) := ν_isProbabilityMeasure (μ := μ) ω
          exact ENNReal.ofReal_toReal (measure_ne_top _ _)
    _ = ∫⁻ ω, ∏ i, (ν (μ := μ) ω) (B i) ∂μ := by
          congr 1; funext ω; conv_rhs => rw [h_rhs_reindex ω]

omit [StandardBorelSpace α] in
/-- Bridge from contractable to bind-based ConditionallyIID on path space.

This is the key lemma connecting contractability to `Exchangeability.ConditionallyIID`.
It uses `CommonEnding.conditional_iid_from_directing_measure` with the bridge condition
proved by `indicator_product_bridge_contractable`. -/
lemma conditionallyIID_bind_of_contractable
    {μ : Measure (Ω[α])} [IsProbabilityMeasure μ] [StandardBorelSpace α]
    (hσ : MeasurePreserving shift μ μ)
    (hContract : ∀ (m : ℕ) (k : Fin m → ℕ), StrictMono k →
        Measure.map (fun ω i => ω (k i)) μ = Measure.map (fun ω (i : Fin m) => ω i.val) μ) :
    Exchangeability.ConditionallyIID μ (fun i (ω : Ω[α]) => ω i) := by
  -- Apply CommonEnding.conditional_iid_from_directing_measure
  apply CommonEnding.conditional_iid_from_directing_measure
  -- 1. Coordinates are measurable
  · exact fun i => measurable_pi_apply i
  -- 2. ν is a probability measure at each point
  · intro ω
    exact ν_isProbabilityMeasure (μ := μ) ω
  -- 3. ν ω s is measurable in ω for each measurable set s
  · intro s hs
    exact ν_eval_measurable hs
  -- 4. Bridge condition: indicator products equal kernel products
  · intro m k hk B hB_meas
    exact indicator_product_bridge_contractable hσ hContract m k hk B hB_meas

end Exchangeability.DeFinetti
