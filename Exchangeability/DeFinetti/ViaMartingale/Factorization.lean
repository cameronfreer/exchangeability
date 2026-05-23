/-
Copyright (c) 2025 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.Probability.ConditionalExpectation
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Exchangeability.Contractability
import Exchangeability.Probability.CondExp
import Exchangeability.Probability.CondIndep
import Exchangeability.Probability.Martingale
import Exchangeability.DeFinetti.ViaMartingale.ShiftOperations
import Exchangeability.DeFinetti.ViaMartingale.FutureFiltration
import Exchangeability.DeFinetti.ViaMartingale.CondExpConvergence
import Exchangeability.DeFinetti.ViaMartingale.IndicatorAlgebra
import Exchangeability.DeFinetti.ViaMartingale.PairLawEquality
import Exchangeability.DeFinetti.MartingaleHelpers
import Exchangeability.PathSpace.CylinderHelpers

/-!
# Factorization Lemmas for Martingale Proof

This file contains the conditional independence and factorization lemmas that form
the core of the martingale proof of de Finetti's theorem.

## Main results

* `block_coord_condIndep` - Conditional independence of past block and single coordinate
  given the far future: σ(X₀,...,X_{r-1}) ⊥⊥_{σ(θ_{m+1} X)} σ(X_r)
* `condexp_indicator_inter_of_condIndep` - Product formula for conditional expectations
  under conditional independence
* `finite_level_factorization` - Finite-level product formula for conditional expectations
* `tail_factorization_from_future` - Passing finite-level factorization to the tail

These establish that contractability implies the product structure needed for
de Finetti's theorem.
-/

noncomputable section
open scoped MeasureTheory Topology
open MeasureTheory ProbabilityTheory Filter
open Exchangeability.PathSpace Exchangeability.DeFinetti.MartingaleHelpers

namespace Exchangeability.DeFinetti.ViaMartingale

variable {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]

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

The proof goes through `condExp_Xr_indicator_eq_of_contractable`, which packages
the Kallenberg 1.3 input
```
E[1_{X_r ∈ B} | σ(U, W)] = E[1_{X_r ∈ B} | σ(W)]
```
with `U = firstRMap X r`, `W = shiftRV X (m+1)`. -/
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
  -- We use the "indicator projection" criterion for conditional independence.
  apply Exchangeability.Probability.condIndep_of_indicator_condexp_eq
  · exact firstRSigma_le_ambient X r hX_meas
  · intro s hs; rcases hs with ⟨t, ht, rfl⟩; exact (hX_meas r) ht

  -- For each H = (X r)⁻¹(B), prove the projection identity:
  -- μ[1_H | firstRSigma X r ⊔ futureFiltration X m] =ᵐ[μ] μ[1_H | futureFiltration X m]
  rintro H ⟨B, hB, rfl⟩

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
  exact condExp_Xr_indicator_eq_of_contractable hX hX_meas (Nat.le_of_lt hrm) hB


/-- **Product formula for conditional expectations under conditional independence.**

Given two sets `A` (measurable in `mF`) and `B` (measurable in `mH`), under conditional
independence given `m`, the conditional expectation of the intersection indicator factors:
```
μ[1_{A∩B} | m] = μ[1_A | m] · μ[1_B | m]   a.e.
```

Proven using `condexp_indicator_inter_bridge` from CondExp.lean. -/
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

/-- **Finite-level factorization builder.**

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
    have h_ind : indProd X 0 C = fun _ => 1 := funext fun _ => by simp [indProd]
    have h_rhs : (fun ω => ∏ i : Fin 0,
        μ[Set.indicator (C i) (fun _ => (1:ℝ)) ∘ (X 0) | futureFiltration X m] ω) = fun _ => 1 :=
      funext fun _ => by simp
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
      rw [Fin.prod_univ_castSucc]; rfl

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
        simpa only [Function.comp_apply] using congr_fun hg_indicator ω
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
        ext ω; simp only [Pi.mul_apply]
        simpa using congr_fun (indicator_mul_indicator_eq_indicator_inter A B 1 1) ω
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
          rw [← hf_indicator, ← hg_indicator]; rfl
        _ =ᵐ[μ] (fun ω => (μ[A.indicator (fun _ => (1:ℝ)) | futureFiltration X m] ω)
                          * (μ[B.indicator (fun _ => (1:ℝ)) | futureFiltration X m] ω)) := hfactor
        _ =ᵐ[μ] (fun ω => (μ[indProd X r Cinit | futureFiltration X m] ω)
                          * (μ[Set.indicator Clast (fun _ => (1:ℝ)) ∘ X r | futureFiltration X m] ω)) :=
          (condExp_congr_ae (.of_eq hf_indicator.symm)).mul (condExp_congr_ae (.of_eq hg_indicator.symm))
        _ =ᵐ[μ] (fun ω => (∏ i : Fin r,
                            μ[Set.indicator (Cinit i) (fun _ => (1:ℝ)) ∘ (X 0)
                              | futureFiltration X m] ω)
                          * (μ[Set.indicator Clast (fun _ => (1:ℝ)) ∘ X r | futureFiltration X m] ω)) :=
          hIH.mul .rfl
        _ =ᵐ[μ] (fun ω => (∏ i : Fin r,
                            μ[Set.indicator (Cinit i) (fun _ => (1:ℝ)) ∘ (X 0)
                              | futureFiltration X m] ω)
                          * μ[Set.indicator Clast (fun _ => (1:ℝ)) ∘ (X 0)
                              | futureFiltration X m] ω) :=
          EventuallyEq.rfl.mul hswap
        _ =ᵐ[μ] (fun ω => ∏ i : Fin (r+1),
                            μ[Set.indicator (C i) (fun _ => (1:ℝ)) ∘ (X 0)
                              | futureFiltration X m] ω) := by
          apply EventuallyEq.of_eq
          funext ω
          -- Reverse of hsplit: combine products using Fin.prod_univ_castSucc
          symm
          rw [Fin.prod_univ_castSucc]
          simp only [Cinit, Clast, Fin.last]

/-- **Tail factorization on finite cylinders.**

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
    simpa only [← tailSigmaFuture_eq_iInf, tailSigmaFuture_eq_tailSigma] using h_conv

  -- RHS convergence: product of convergent sequences
  have h_rhs_conv : ∀ᵐ ω ∂μ,
      Tendsto (fun m => ∏ i : Fin r,
                  μ[Set.indicator (C i) (fun _ => (1 : ℝ)) ∘ (X 0) | futureFiltration X m] ω)
              atTop
              (𝓝 (∏ i : Fin r,
                  μ[Set.indicator (C i) (fun _ => (1 : ℝ)) ∘ (X 0) | tailSigma X] ω)) := by
    -- Product of tendsto gives tendsto of product (finitely many factors)
    filter_upwards [ae_all_iff.mpr h_rev] with ω hω
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

end Exchangeability.DeFinetti.ViaMartingale
