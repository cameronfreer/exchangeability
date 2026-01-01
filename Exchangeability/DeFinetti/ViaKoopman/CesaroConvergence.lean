/-
Copyright (c) 2025 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Exchangeability.DeFinetti.ViaKoopman.Infrastructure
import Exchangeability.DeFinetti.ViaKoopman.CesaroHelpers
import Exchangeability.DeFinetti.ViaKoopman.CylinderFunctions
import Exchangeability.DeFinetti.ViaKoopman.KoopmanCommutation

/-! # L¹ Cesàro Convergence via Cylinder Functions

This file implements the L¹ convergence framework for the de Finetti proof:
- `condexpL2_ae_eq_condExp` - connects L² conditional expectation to classical CE
- `L1_cesaro_convergence_bounded` - bounded case convergence
- `L1_cesaro_convergence` - general integrable case via truncation
- `condexp_pair_factorization_MET` - pair factorization via MET

This is "Option B" from the proof plan, avoiding the projected MET approach.
-/

open Filter MeasureTheory

noncomputable section

namespace Exchangeability.DeFinetti.ViaKoopman

open MeasureTheory Filter Topology ProbabilityTheory
open Exchangeability.Ergodic
open Exchangeability.PathSpace
open scoped BigOperators RealInnerProductSpace

variable {α : Type*} [MeasurableSpace α]

-- Short notation for shift-invariant σ-algebra (used throughout this file)
local notation "mSI" => shiftInvariantSigma (α := α)

/-! ### Option B: L¹ Convergence via Cylinder Functions

These lemmas implement the bounded and general cases for L¹ convergence of Cesàro averages
using the cylinder function approach (Option B). This avoids MET and sub-σ-algebra typeclass issues. -/

set_option maxHeartbeats 8000000

section OptionB_L1Convergence

variable {μ : Measure (Ω[α])} [IsProbabilityMeasure μ] [StandardBorelSpace α]

-- Helper lemmas for Step 3b: connecting condexpL2 to condExp

/-- Our condexpL2 operator agrees a.e. with classical conditional expectation.

**Mathematical content:** This is a standard fact in measure theory. Our `condexpL2` is defined as:
```lean
condexpL2 := (lpMeas ℝ ℝ shiftInvariantSigma 2 μ).subtypeL.comp
             (MeasureTheory.condExpL2 ℝ ℝ shiftInvariantSigma_le)
```

The composition of mathlib's `condExpL2` with the subspace inclusion `subtypeL` should equal
the classical `condExp` a.e., since:
1. Mathlib's `condExpL2` equals `condExp` a.e. (by `MemLp.condExpL2_ae_eq_condExp`)
2. The subspace inclusion preserves a.e. classes

**Lean challenge:** Requires navigating Lp quotient types and finding the correct API to
convert between `Lp ℝ 2 μ` and `MemLp _ 2 μ` representations. The `Lp.memℒp` constant
doesn't exist in the current mathlib API. -/
lemma condexpL2_ae_eq_condExp (f : Lp ℝ 2 μ) :
    (condexpL2 (μ := μ) f : Ω[α] → ℝ) =ᵐ[μ] μ[f | shiftInvariantSigma] := by
  -- Get MemLp from Lp using Lp.memLp
  have hf : MemLp (f : Ω[α] → ℝ) 2 μ := Lp.memLp f
  -- Key: hf.toLp (↑↑f) = f in Lp (by Lp.toLp_coeFn)
  have h_toLp_eq : hf.toLp (f : Ω[α] → ℝ) = f := Lp.toLp_coeFn f hf
  -- condexpL2 unfolds to subtypeL.comp (condExpL2 ℝ ℝ shiftInvariantSigma_le)
  unfold condexpL2
  -- Rewrite f as hf.toLp ↑↑f using h_toLp_eq
  conv_lhs => arg 1; rw [← h_toLp_eq]
  -- Unfold the composition and coercion manually
  show ↑↑((lpMeas ℝ ℝ shiftInvariantSigma 2 μ).subtypeL ((condExpL2 ℝ ℝ shiftInvariantSigma_le) (hf.toLp ↑↑f)))    =ᶠ[ae μ] μ[↑↑f|shiftInvariantSigma]
  -- Now apply MemLp.condExpL2_ae_eq_condExp with explicit type parameters
  exact hf.condExpL2_ae_eq_condExp (E := ℝ) (𝕜 := ℝ) shiftInvariantSigma_le

-- Helper lemmas for Step 3a: a.e. equality through measure-preserving maps
--
-- These are standard measure-theoretic facts that Lean's elaborator struggles with
-- due to complexity of nested a.e. manipulations. Documented with full proofs.

/-- Pull a.e. equality back along a measure-preserving map.
    Standard fact: if f =ᵐ g and T preserves μ, then f ∘ T =ᵐ g ∘ T.
    Proof: Use QuasiMeasurePreserving.ae_eq_comp from mathlib. -/
lemma eventuallyEq_comp_measurePreserving {f g : Ω[α] → ℝ}
    (hT : MeasurePreserving shift μ μ) (hfg : f =ᵐ[μ] g) :
    (f ∘ shift) =ᵐ[μ] (g ∘ shift) :=
  hT.quasiMeasurePreserving.ae_eq_comp hfg

/-- Iterate of a measure-preserving map is measure-preserving.
    Proof: By induction; identity is measure-preserving, and composition preserves the property. -/
private lemma MeasurePreserving.iterate (hT : MeasurePreserving shift μ μ) (k : ℕ) :
    MeasurePreserving (shift^[k]) μ μ := by
  induction k with
  | zero =>
      simp only [Function.iterate_zero]
      exact MeasurePreserving.id μ
  | succ k ih =>
      simp only [Function.iterate_succ']
      exact hT.comp ih

/-- General evaluation formula for shift iteration. -/
private lemma iterate_shift_eval (k n : ℕ) (ω : Ω[α]) :
    (shift^[k] ω) n = ω (k + n) := by
  induction k generalizing n with
  | zero => simp
  | succ k ih =>
      rw [Function.iterate_succ']
      simp only [shift_apply, Function.comp_apply]
      rw [ih]
      ac_rfl

/-- Evaluate the k-th shift at 0: shift^[k] ω 0 = ω k. -/
private lemma iterate_shift_eval0 (k : ℕ) (ω : Ω[α]) :
    (shift^[k] ω) 0 = ω k := by
  rw [iterate_shift_eval]
  simp

/-! ### Option B Helper Lemmas

These lemmas extract Steps 4a-4c from the main theorem to reduce elaboration complexity.
Each lemma is self-contained with ~50-80 lines, well below timeout thresholds. -/

/-- On a probability space, L² convergence of Koopman–Birkhoff averages to `condexpL2`
    implies L¹ convergence of chosen representatives.  This version is robust to
    older mathlib snapshots (no `Subtype.aestronglyMeasurable`, no `tendsto_iff_*`,
    and `snorm` is fully qualified). -/
private lemma optionB_Step3b_L2_to_L1
    {μ : Measure (Ω[α])} [IsProbabilityMeasure μ]
    (hσ : MeasurePreserving shift μ μ)
    (fL2 : Lp ℝ 2 μ)
    (hfL2_tendsto :
      Tendsto (fun n => birkhoffAverage ℝ (koopman shift hσ) (fun f => f) n fL2)
              atTop (𝓝 (condexpL2 (μ := μ) fL2)))
    (B : ℕ → Ω[α] → ℝ)
    (Y : Ω[α] → ℝ)
    -- a.e. equalities available for n > 0
    (hB_eq_pos :
      ∀ n, 0 < n →
        (fun ω => birkhoffAverage ℝ (koopman shift hσ) (fun f => f) n fL2 ω) =ᵐ[μ] B n)
    (hY_eq :
      (fun ω => condexpL2 (μ := μ) fL2 ω) =ᵐ[μ] Y) :
    Tendsto (fun n => ∫ ω, |B n ω - Y ω| ∂μ) atTop (𝓝 0) := by
  classical
  -- Step 1: ‖(birkhoffAverage n fL2) - (condexpL2 fL2)‖ → 0  (via continuity)
  have hΦ : Continuous (fun x : Lp ℝ 2 μ => ‖x - condexpL2 (μ := μ) fL2‖) :=
    (continuous_norm.comp (continuous_sub_right _))
  have hL2_norm :
      Tendsto (fun n =>
        ‖birkhoffAverage ℝ (koopman shift hσ) (fun f => f) n fL2
           - condexpL2 (μ := μ) fL2‖) atTop (𝓝 0) := by
    -- Compose the continuous map hΦ with the convergence hfL2_tendsto
    have := (hΦ.tendsto (condexpL2 (μ := μ) fL2)).comp hfL2_tendsto
    simpa [sub_self, norm_zero]

  -- Step 2: build the *upper* inequality eventually (for n > 0 only).
  have h_upper_ev :
      ∀ᶠ n in atTop,
        ∫ ω, |B n ω - Y ω| ∂μ
          ≤ ‖birkhoffAverage ℝ (koopman shift hσ) (fun f => f) n fL2
               - condexpL2 (μ := μ) fL2‖ := by
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    -- a.e. identify `B n` and `Y` with the Lp representatives
    have h_ae :
        (fun ω => |B n ω - Y ω|) =ᵐ[μ]
          (fun ω =>
            |birkhoffAverage ℝ (koopman shift hσ) (fun f => f) n fL2 ω
             - condexpL2 (μ := μ) fL2 ω|) := by
      filter_upwards [hB_eq_pos n hn, hY_eq] with ω h1 h2
      simpa [h1, h2]

    -- measurability: both birkhoffAverage and condexpL2 are Lp elements, so AEMeasurable when coerced
    have h_meas :
        AEMeasurable
          (fun ω =>
            birkhoffAverage ℝ (koopman shift hσ) (fun f => f) n fL2 ω
            - condexpL2 (μ := μ) fL2 ω) μ := by
      -- Both terms are Lp elements, so AEStronglyMeasurable when coerced
      apply AEMeasurable.sub
      · -- birkhoffAverage ... fL2 is an Lp element
        -- When coerced to Ω → ℝ, it's AEStronglyMeasurable → AEMeasurable
        exact (Lp.aestronglyMeasurable _).aemeasurable
      · -- condexpL2 fL2 is an Lp element
        exact (Lp.aestronglyMeasurable _).aemeasurable

    -- L¹ ≤ L² via Hölder/Cauchy-Schwarz on a probability space
    have h_le :
        ∫ ω, |(birkhoffAverage ℝ (koopman shift hσ) (fun f => f) n fL2 ω
                - condexpL2 (μ := μ) fL2 ω)| ∂μ
          ≤ (eLpNorm
               (fun ω =>
                  birkhoffAverage ℝ (koopman shift hσ) (fun f => f) n fL2 ω
                  - condexpL2 (μ := μ) fL2 ω)
               2 μ).toReal := by
      -- On a probability space, L¹ ≤ L² by eLpNorm monotonicity
      -- eLpNorm f 1 ≤ eLpNorm f 2, so ∫|f| ≤ ‖f‖₂
      let f := fun ω => birkhoffAverage ℝ (koopman shift hσ) (fun f => f) n fL2 ω
                       - condexpL2 (μ := μ) fL2 ω
      have h_mono : eLpNorm f 1 μ ≤ eLpNorm f 2 μ := by
        apply eLpNorm_le_eLpNorm_of_exponent_le
        · norm_num
        · exact h_meas.aestronglyMeasurable
      -- Need MemLp f 2 μ and Integrable f μ to apply eLpNorm_one_le_eLpNorm_two_toReal
      -- birkhoffAverage and condexpL2 are both Lp elements, so their difference is MemLp 2
      have h_memLp2 : MemLp f 2 μ := by
        -- birkhoffAverage ... fL2 - condexpL2 fL2 is an Lp element
        -- So its coercion to a function is in MemLp
        let diff_Lp := birkhoffAverage ℝ (koopman shift hσ) (fun f => f) n fL2 - condexpL2 (μ := μ) fL2
        have h_diff_memLp := Lp.memLp diff_Lp
        -- f equals the coercion of diff_Lp a.e.
        have h_f_eq : f =ᵐ[μ] diff_Lp := by
          have h_coe := Lp.coeFn_sub (birkhoffAverage ℝ (koopman shift hσ) (fun f => f) n fL2) (condexpL2 (μ := μ) fL2)
          -- h_coe : ↑↑(a - b) =ᶠ ↑↑a - ↑↑b
          -- We need: f =ᶠ ↑↑diff_Lp, where f = ↑↑(birkhoffAverage ...) - ↑↑(condexpL2 ...)
          exact h_coe.symm
        exact MemLp.ae_eq h_f_eq.symm h_diff_memLp
      have h_integrable : Integrable f μ := by
        -- MemLp f 2 μ → MemLp f 1 μ on probability space → Integrable f μ
        have h_memLp1 : MemLp f 1 μ := by
          refine ⟨h_memLp2.aestronglyMeasurable, ?_⟩
          calc eLpNorm f 1 μ ≤ eLpNorm f 2 μ := by
                apply eLpNorm_le_eLpNorm_of_exponent_le
                · norm_num
                · exact h_memLp2.aestronglyMeasurable
             _ < ⊤ := h_memLp2.eLpNorm_lt_top
        exact memLp_one_iff_integrable.mp h_memLp1
      -- Apply eLpNorm_one_le_eLpNorm_two_toReal
      exact eLpNorm_one_le_eLpNorm_two_toReal f h_integrable h_memLp2

    -- Relate eLpNorm to Lp norm via Lp.norm_def
    have h_toNorm :
        (eLpNorm
          (fun ω =>
            birkhoffAverage ℝ (koopman shift hσ) (fun f => f) n fL2 ω
            - condexpL2 (μ := μ) fL2 ω)
          2 μ).toReal
        = ‖birkhoffAverage ℝ (koopman shift hσ) (fun f => f) n fL2
             - condexpL2 (μ := μ) fL2‖ := by
      -- The Lp norm of (a - b) equals (eLpNorm ↑↑(a-b) p μ).toReal
      -- Use Lp.norm_def and Lp.coeFn_sub to connect them
      let diff_Lp := birkhoffAverage ℝ (koopman shift hσ) (fun f => f) n fL2 - condexpL2 (μ := μ) fL2
      have h_norm : ‖diff_Lp‖ = (eLpNorm diff_Lp 2 μ).toReal := Lp.norm_def diff_Lp
      have h_coe := Lp.coeFn_sub (birkhoffAverage ℝ (koopman shift hσ) (fun f => f) n fL2) (condexpL2 (μ := μ) fL2)
      -- h_coe : ↑↑(a - b) =ᶠ ↑↑a - ↑↑b
      -- Rewrite using eLpNorm_congr_ae and then h_norm
      calc (eLpNorm (fun ω => birkhoffAverage ℝ (koopman shift hσ) (fun f => f) n fL2 ω
                               - condexpL2 (μ := μ) fL2 ω) 2 μ).toReal
          = (eLpNorm diff_Lp 2 μ).toReal := by
              congr 1
              apply eLpNorm_congr_ae
              exact h_coe.symm
        _ = ‖diff_Lp‖ := h_norm.symm
        _ = ‖birkhoffAverage ℝ (koopman shift hσ) (fun f => f) n fL2 - condexpL2 (μ := μ) fL2‖ := rfl

    -- conclude the inequality at this `n > 0`
    have h_eq_int :
        ∫ ω, |B n ω - Y ω| ∂μ
          = ∫ ω, |(birkhoffAverage ℝ (koopman shift hσ) (fun f => f) n fL2 ω
                    - condexpL2 (μ := μ) fL2 ω)| ∂μ :=
      integral_congr_ae h_ae
    exact (le_of_eq h_eq_int).trans (h_le.trans (le_of_eq h_toNorm))

  -- Step 3: lower bound is always `0 ≤ ∫ |B n - Y|`
  have h_lower_ev :
      ∀ᶠ n in atTop, 0 ≤ ∫ ω, |B n ω - Y ω| ∂μ :=
    Eventually.of_forall (by
      intro n; exact integral_nonneg (by intro ω; exact abs_nonneg _))

  -- Step 4: squeeze between 0 and the L²-norm difference (which → 0)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
  · exact tendsto_const_nhds
  · exact hL2_norm
  · exact h_lower_ev
  · exact h_upper_ev

/-- **Step 4b helper**: A_n and B_n differ negligibly.

For bounded g, shows |A_n ω - B_n ω| ≤ 2·Cg/(n+1) → 0 via dominated convergence. -/
private lemma optionB_Step4b_AB_close
    {μ : Measure (Ω[α])} [IsProbabilityMeasure μ]
    (g : α → ℝ) (hg_meas : Measurable g) (Cg : ℝ) (hCg_bd : ∀ x, |g x| ≤ Cg)
    (A B : ℕ → Ω[α] → ℝ)
    (hA_def : A = fun n ω => 1 / (↑n + 1) * (Finset.range (n + 1)).sum (fun j => g (ω j)))
    (hB_def : B = fun n ω => if n = 0 then 0 else 1 / ↑n * (Finset.range n).sum (fun j => g (ω j))) :
    Tendsto (fun n => ∫ ω, |A n ω - B n ω| ∂μ) atTop (𝓝 0) := by
  -- For each ω, bound |A n ω - B n ω|
  have h_bd : ∀ n > 0, ∀ ω, |A n ω - B n ω| ≤ 2 * Cg / (n + 1) := by
    intro n hn ω
    rw [hA_def, hB_def]; simp only [hn.ne', ↓reduceIte]
    -- A n ω = (1/(n+1)) * ∑_{k=0}^n g(ω k)
    -- B n ω = (1/n) * ∑_{k=0}^{n-1} g(ω k)
    -- Write ∑_{k=0}^n = ∑_{k=0}^{n-1} + g(ω n)
    rw [show Finset.range (n + 1) = Finset.range n ∪ {n} by
          ext k; simp [Finset.mem_range, Nat.lt_succ]; omega,
        Finset.sum_union (by simp : Disjoint (Finset.range n) {n}),
        Finset.sum_singleton]
    -- Now A n ω = (1/(n+1)) * (∑_{k<n} g(ω k) + g(ω n))
    -- Let S = ∑_{k<n} g(ω k)
    set S := (Finset.range n).sum fun j => g (ω j)
    -- A n ω - B n ω = S/(n+1) + g(ω n)/(n+1) - S/n
    --               = -S/(n(n+1)) + g(ω n)/(n+1)
    calc |1 / (↑n + 1) * (S + g (ω n)) - 1 / ↑n * S|
        = |S / (↑n + 1) + g (ω n) / (↑n + 1) - S / ↑n| := by ring
      _ = |-S / (↑n * (↑n + 1)) + g (ω n) / (↑n + 1)| := by field_simp; ring
      _ ≤ |-S / (↑n * (↑n + 1))| + |g (ω n) / (↑n + 1)| := by
            -- triangle inequality |x + y| ≤ |x| + |y|
            exact abs_add_le _ _
      _ = |S| / (↑n * (↑n + 1)) + |g (ω n)| / (↑n + 1) := by
            -- pull denominators out of |·| since denominators are ≥ 0
            have hn : 0 < (n : ℝ) + 1 := by positivity
            have hnp : 0 < (n : ℝ) * ((n : ℝ) + 1) := by positivity
            rw [abs_div, abs_div, abs_neg]
            · congr 1
              · rw [abs_of_pos hnp]
              · rw [abs_of_pos hn]
      _ ≤ |S| / (↑n * (↑n + 1)) + Cg / (↑n + 1) := by
            gcongr
            exact hCg_bd (ω n)
      _ ≤ (n * Cg) / (↑n * (↑n + 1)) + Cg / (↑n + 1) := by
          gcongr
          -- |S| ≤ n * Cg since |g(ω k)| ≤ Cg for all k
          calc |S|
              ≤ (Finset.range n).sum (fun j => |g (ω j)|) := by
                exact Finset.abs_sum_le_sum_abs _ _
            _ ≤ (Finset.range n).sum (fun j => Cg) := by
                apply Finset.sum_le_sum
                intro j _
                exact hCg_bd (ω j)
            _ = n * Cg := by
                rw [Finset.sum_const, Finset.card_range]
                ring
      _ = 2 * Cg / (↑n + 1) := by field_simp; ring
  -- Integrate the pointwise bound and squeeze to 0
  have h_upper : ∀ n > 0,
      ∫ ω, |A n ω - B n ω| ∂μ ≤ 2 * Cg / (n + 1) := by
    intro n hn
    -- AE bound
    have h_bd_ae : ∀ᵐ ω ∂μ, |A n ω - B n ω| ≤ 2 * Cg / (n + 1) :=
      ae_of_all _ (h_bd n hn)
    -- Both sides integrable (constant is integrable; the left is bounded by a constant on a prob space)
    have h_int_right : Integrable (fun _ => 2 * Cg / (n + 1)) μ := integrable_const _
    have h_int_left  : Integrable (fun ω => |A n ω - B n ω|) μ := by
      classical
      -- Show `Integrable (A n)` and `Integrable (B n)` first.
      have h_int_An : Integrable (A n) μ := by
        -- Each summand ω ↦ g (ω i) is integrable by boundedness + measurability.
        have h_i :
            ∀ i ∈ Finset.range (n+1),
              Integrable (fun ω => g (ω i)) μ := by
          intro i hi
          -- measurability of ω ↦ g (ω i)
          have hmeas : AEMeasurable (fun ω => g (ω i)) μ :=
            (hg_meas.comp (measurable_pi_apply i)).aemeasurable
          -- uniform bound by Cg (pointwise → a.e.)
          have hbd : ∃ C : ℝ, ∀ᵐ ω ∂μ, |g (ω i)| ≤ C :=
            ⟨Cg, ae_of_all _ (fun ω => hCg_bd (ω i))⟩
          exact MeasureTheory.integrable_of_ae_bound hmeas hbd
        -- sum is integrable, and scaling by a real keeps integrability
        have h_sum :
            Integrable (fun ω =>
              (Finset.range (n+1)).sum (fun i => g (ω i))) μ :=
          integrable_finset_sum (Finset.range (n+1)) (fun i hi => h_i i hi)
        -- A n is (1/(n+1)) • (sum …)
        have h_smul :
            Integrable (fun ω =>
              (1 / (n + 1 : ℝ)) •
              ( (Finset.range (n+1)).sum (fun i => g (ω i)) )) μ :=
          h_sum.smul (1 / (n + 1 : ℝ))
        -- rewrite to your definition of `A n`
        rw [hA_def]
        convert h_smul using 2

      have h_int_Bn : Integrable (B n) μ := by
        -- B n has a special n=0 case
        by_cases hn_zero : n = 0
        · -- n = 0: B 0 = 0
          rw [hB_def]
          simp [hn_zero]
        · -- n ≠ 0: B n uses Finset.range n
          have h_i :
              ∀ i ∈ Finset.range n,
                Integrable (fun ω => g (ω i)) μ := by
            intro i hi
            have hmeas : AEMeasurable (fun ω => g (ω i)) μ :=
              (hg_meas.comp (measurable_pi_apply i)).aemeasurable
            have hbd : ∃ C : ℝ, ∀ᵐ ω ∂μ, |g (ω i)| ≤ C :=
              ⟨Cg, ae_of_all _ (fun ω => hCg_bd (ω i))⟩
            exact MeasureTheory.integrable_of_ae_bound hmeas hbd
          have h_sum :
              Integrable (fun ω =>
                (Finset.range n).sum (fun i => g (ω i))) μ :=
            integrable_finset_sum (Finset.range n) (fun i hi => h_i i hi)
          have h_smul :
              Integrable (fun ω =>
                (1 / (n : ℝ)) •
                ( (Finset.range n).sum (fun i => g (ω i)) )) μ :=
            h_sum.smul (1 / (n : ℝ))
          rw [hB_def]
          convert h_smul using 2
          simp [hn_zero, smul_eq_mul]
      -- Now `|A n - B n|` is integrable.
      exact (h_int_An.sub h_int_Bn).abs
    -- Monotonicity of the integral under AE ≤
    calc ∫ ω, |A n ω - B n ω| ∂μ
        ≤ ∫ ω, 2 * Cg / (↑n + 1) ∂μ := integral_mono_ae h_int_left h_int_right h_bd_ae
      _ = 2 * Cg / (n + 1) := by simp

  -- Lower bound: integrals of nonnegative functions are ≥ 0.
  have h_lower : ∀ n, 0 ≤ ∫ ω, |A n ω - B n ω| ∂μ := by
    intro n
    exact integral_nonneg (fun ω => abs_nonneg _)

  -- Upper bound eventually: use your bound `h_upper` from Step 4b/4c
  have h_upper' :
      ∀ᶠ n in Filter.atTop,
        ∫ ω, |A n ω - B n ω| ∂μ ≤ (2 * Cg) / (n + 1 : ℝ) := by
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    exact h_upper n hn

  -- The RHS tends to 0.
  have h_tends_zero :
      Tendsto (fun n : ℕ => (2 * Cg) / (n + 1 : ℝ)) atTop (𝓝 0) := by
    -- (2*Cg) * (n+1)⁻¹ → 0
    simp only [div_eq_mul_inv]
    -- (n+1 : ℝ) → ∞, so its inverse → 0
    have h1 : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop
    -- Constant function 1 tends to 1
    have h_const : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
    have h2 : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
      h1.atTop_add h_const
    have h3 : Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp h2
    -- Now (2*Cg) * (n+1)⁻¹ → (2*Cg) * 0 = 0
    have h4 := h3.const_mul (2 * Cg)
    simp only [mul_zero] at h4
    exact h4

  -- Squeeze
  exact squeeze_zero' (Filter.Eventually.of_forall h_lower) h_upper' h_tends_zero

/-- **Step 4c helper**: Triangle inequality to combine convergences.

Given ∫|B_n - Y| → 0 and ∫|A_n - B_n| → 0, proves ∫|A_n - Y| → 0 via squeeze theorem. -/
private lemma optionB_Step4c_triangle
    {μ : Measure (Ω[α])} [IsProbabilityMeasure μ]
    (g : α → ℝ) (hg_meas : Measurable g) (hg_bd : ∃ Cg, ∀ x, |g x| ≤ Cg)
    (A B : ℕ → Ω[α] → ℝ) (Y : Ω[α] → ℝ) (G : Ω[α] → ℝ)
    (hA_def : A = fun n ω => 1 / (↑n + 1) * (Finset.range (n + 1)).sum (fun j => g (ω j)))
    (hB_def : B = fun n ω => if n = 0 then 0 else 1 / ↑n * (Finset.range n).sum (fun j => g (ω j)))
    (hG_int : Integrable G μ)
    (hY_int : Integrable Y μ)
    (hB_L1_conv : Tendsto (fun n => ∫ ω, |B n ω - Y ω| ∂μ) atTop (𝓝 0))
    (hA_B_close : Tendsto (fun n => ∫ ω, |A n ω - B n ω| ∂μ) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ ω, |A n ω - Y ω| ∂μ) atTop (𝓝 0) := by
  -- First prove integrability of |B n - Y| from L¹ convergence hypothesis
  have hBY_abs_integrable : ∀ n, Integrable (fun ω => |B n ω - Y ω|) μ := by
    intro n
    -- B n is bounded and measurable, so integrable
    obtain ⟨Cg, hCg⟩ := hg_bd
    have hB_int : Integrable (B n) μ := by
      by_cases hn : n = 0
      · rw [hB_def]; simp [hn]
      · -- B n is bounded by Cg
        have hB_bd : ∀ ω, |B n ω| ≤ Cg := by
          intro ω
          rw [hB_def]
          simp [hn]
          -- |(1/n) * ∑ g(ω j)| ≤ (1/n) * ∑ |g(ω j)| ≤ (1/n) * n*Cg = Cg
          have hsum : |Finset.sum (Finset.range n) (fun j => g (ω j))| ≤ (n : ℝ) * Cg := by
            calc |Finset.sum (Finset.range n) (fun j => g (ω j))|
                ≤ Finset.sum (Finset.range n) (fun j => |g (ω j)|) := Finset.abs_sum_le_sum_abs _ _
              _ ≤ Finset.sum (Finset.range n) (fun j => Cg) := by
                  gcongr with j _; exact hCg _
              _ = (n : ℝ) * Cg := by simp
          calc (n : ℝ)⁻¹ * |Finset.sum (Finset.range n) (fun j => g (ω j))|
            _ ≤ (n : ℝ)⁻¹ * ((n : ℝ) * Cg) := by gcongr
            _ = Cg := by field_simp
        -- Bounded + Measurable → Integrable on finite measure space
        have hB_meas : Measurable (B n) := by
          rw [hB_def]
          simp [hn]
          -- (1/n) * ∑_{j < n} g(ω j) is measurable
          refine Measurable.const_mul ?_ _
          refine Finset.measurable_sum (Finset.range n) (fun j _ => ?_)
          exact Measurable.comp hg_meas (measurable_pi_apply j)
        have hB_bd_ae : ∀ᵐ ω ∂μ, ‖B n ω‖ ≤ Cg := ae_of_all μ (fun ω => le_trans (Real.norm_eq_abs _).le (hB_bd ω))
        exact ⟨hB_meas.aestronglyMeasurable, HasFiniteIntegral.of_bounded hB_bd_ae⟩
    -- |B n - Y| is integrable as difference of integrable functions
    exact (hB_int.sub hY_int).abs

  -- Triangle inequality under the integral
  have h_triangle :
      ∀ n,
        ∫ ω, |A n ω - Y ω| ∂μ
          ≤ ∫ ω, |A n ω - B n ω| ∂μ + ∫ ω, |B n ω - Y ω| ∂μ := by
    intro n
    -- pointwise triangle: |(A-B)+(B-Y)| ≤ |A-B| + |B-Y|
    have hpt :
        ∀ ω, |(A n ω - B n ω) + (B n ω - Y ω)| ≤
              |A n ω - B n ω| + |B n ω - Y ω| := by
      intro ω; exact abs_add_le (A n ω - B n ω) (B n ω - Y ω)
    -- rewrite the LHS inside the absolute value
    have hre : (fun ω => |A n ω - Y ω|) =
               (fun ω => |(A n ω - B n ω) + (B n ω - Y ω)|) := by
      funext ω; ring_nf
    -- both RHS summands are integrable
    have hint1 : Integrable (fun ω => |A n ω - B n ω|) μ := by
      obtain ⟨Cg, hCg⟩ := hg_bd
      -- A n is bounded by Cg, so |A n - B n| is bounded by 2*Cg
      have hAB_bd : ∀ ω, |A n ω - B n ω| ≤ 2 * Cg := by
        intro ω
        by_cases hn : n = 0
        · rw [hA_def, hB_def]
          simp [hn]
          have hCg_nonneg : 0 ≤ Cg := by
            have := hCg (ω 0)
            exact abs_nonneg _ |>.trans this
          calc |g (ω 0)| ≤ Cg := hCg _
            _ ≤ 2 * Cg := by linarith [hCg_nonneg]
        · -- Both A n and B n are bounded by Cg
          have hA_bd : |A n ω| ≤ Cg := by
            rw [hA_def]
            simp
            have hsum : |Finset.sum (Finset.range (n + 1)) (fun j => g (ω j))| ≤ ((n : ℝ) + 1) * Cg := by
              calc |Finset.sum (Finset.range (n + 1)) (fun j => g (ω j))|
                  ≤ Finset.sum (Finset.range (n + 1)) (fun j => |g (ω j)|) := Finset.abs_sum_le_sum_abs _ _
                _ ≤ Finset.sum (Finset.range (n + 1)) (fun j => Cg) := by
                    gcongr with j _; exact hCg _
                _ = ((n : ℝ) + 1) * Cg := by simp
            have : |((n : ℝ) + 1)|⁻¹ = ((n : ℝ) + 1)⁻¹ := by rw [abs_of_nonneg]; positivity
            calc |((n : ℝ) + 1)|⁻¹ * |Finset.sum (Finset.range (n + 1)) (fun j => g (ω j))|
              _ = ((n : ℝ) + 1)⁻¹ * |Finset.sum (Finset.range (n + 1)) (fun j => g (ω j))| := by rw [this]
              _ ≤ ((n : ℝ) + 1)⁻¹ * (((n : ℝ) + 1) * Cg) := by gcongr
              _ = Cg := by field_simp
          have hB_bd : |B n ω| ≤ Cg := by
            rw [hB_def]
            simp [hn]
            have hsum : |Finset.sum (Finset.range n) (fun j => g (ω j))| ≤ (n : ℝ) * Cg := by
              calc |Finset.sum (Finset.range n) (fun j => g (ω j))|
                  ≤ Finset.sum (Finset.range n) (fun j => |g (ω j)|) := Finset.abs_sum_le_sum_abs _ _
                _ ≤ Finset.sum (Finset.range n) (fun j => Cg) := by
                    gcongr with j _; exact hCg _
                _ = (n : ℝ) * Cg := by simp
            calc (n : ℝ)⁻¹ * |Finset.sum (Finset.range n) (fun j => g (ω j))|
              _ ≤ (n : ℝ)⁻¹ * ((n : ℝ) * Cg) := by gcongr
              _ = Cg := by field_simp
          calc |A n ω - B n ω|
              ≤ |A n ω| + |B n ω| := abs_sub _ _
            _ ≤ Cg + Cg := by gcongr
            _ = 2 * Cg := by ring
      have hA_meas : Measurable (A n) := by
        rw [hA_def]
        simp
        refine Measurable.const_mul ?_ _
        refine Finset.measurable_sum (Finset.range (n + 1)) (fun j _ => ?_)
        exact Measurable.comp hg_meas (measurable_pi_apply j)
      have hB_meas : Measurable (B n) := by
        rw [hB_def]
        by_cases hn : n = 0
        · simp [hn]
        · simp [hn]
          refine Measurable.const_mul ?_ _
          refine Finset.measurable_sum (Finset.range n) (fun j _ => ?_)
          exact Measurable.comp hg_meas (measurable_pi_apply j)
      have hAB_bd_ae : ∀ᵐ ω ∂μ, ‖|A n ω - B n ω|‖ ≤ 2 * Cg :=
        ae_of_all μ (fun ω => by simp [Real.norm_eq_abs]; exact hAB_bd ω)
      exact ⟨(hA_meas.sub hB_meas).norm.aestronglyMeasurable, HasFiniteIntegral.of_bounded hAB_bd_ae⟩
    have hint2 : Integrable (fun ω => |B n ω - Y ω|) μ := hBY_abs_integrable n
    -- now integrate the pointwise inequality
    calc
      ∫ ω, |A n ω - Y ω| ∂μ
          = ∫ ω, |(A n ω - B n ω) + (B n ω - Y ω)| ∂μ := by simpa [hre]
      _ ≤ ∫ ω, (|A n ω - B n ω| + |B n ω - Y ω|) ∂μ := by
            refine integral_mono_of_nonneg ?_ ?_ ?_
            · exact ae_of_all μ (fun ω => by positivity)
            · exact hint1.add hint2
            · exact ae_of_all μ hpt
      _ = ∫ ω, |A n ω - B n ω| ∂μ + ∫ ω, |B n ω - Y ω| ∂μ := by
            simpa using integral_add hint1 hint2

  -- Finally, squeeze using `h_triangle`, your Step 4b result, and `hB_L1_conv`.
  refine Metric.tendsto_atTop.2 ?_   -- ε-criterion
  intro ε hε
  -- get N₁ from Step 4b: ∫|A n - B n| → 0
  obtain ⟨N₁, hN₁⟩ := (Metric.tendsto_atTop.mp hA_B_close) (ε/2) (by linarith)
  -- get N₂ from Step 4c: ∫|B n - Y| → 0
  obtain ⟨N₂, hN₂⟩ := (Metric.tendsto_atTop.mp hB_L1_conv) (ε/2) (by linarith)
  refine ⟨max N₁ N₂, ?_⟩
  intro n hn
  have hn₁ : N₁ ≤ n := le_of_max_le_left hn
  have hn₂ : N₂ ≤ n := le_of_max_le_right hn
  calc
    dist (∫ ω, |A n ω - Y ω| ∂μ) 0
        = |∫ ω, |A n ω - Y ω| ∂μ| := by simp [dist_zero_right]
    _ =  ∫ ω, |A n ω - Y ω| ∂μ := by
          have : 0 ≤ ∫ ω, |A n ω - Y ω| ∂μ :=
            integral_nonneg (by intro ω; positivity)
          simpa [abs_of_nonneg this]
    _ ≤  ∫ ω, |A n ω - B n ω| ∂μ + ∫ ω, |B n ω - Y ω| ∂μ := h_triangle n
    _ <  ε/2 + ε/2 := by
          apply add_lt_add
          · have := hN₁ n hn₁
            simp only [dist_zero_right] at this
            have h_nonneg : 0 ≤ ∫ ω, |A n ω - B n ω| ∂μ :=
              integral_nonneg (by intro ω; positivity)
            simpa [abs_of_nonneg h_nonneg] using this
          · have := hN₂ n hn₂
            simp only [dist_zero_right] at this
            have h_nonneg : 0 ≤ ∫ ω, |B n ω - Y ω| ∂μ :=
              integral_nonneg (by intro ω; positivity)
            simpa [abs_of_nonneg h_nonneg] using this
    _ =  ε := by ring

/-- **Option B bounded case implementation**: L¹ convergence for bounded functions.

For a bounded measurable function g : α → ℝ, the Cesàro averages A_n(ω) = (1/(n+1)) ∑_j g(ω j)
converge in L¹ to CE[g(ω₀) | mSI]. Uses the fact that g(ω 0) is a cylinder function. -/
private theorem optionB_L1_convergence_bounded
    (hσ : MeasurePreserving shift μ μ)
    (g : α → ℝ)
    (hg_meas : Measurable g) (hg_bd : ∃ Cg, ∀ x, |g x| ≤ Cg) :
    let A := fun n : ℕ => fun ω => (1 / ((n + 1) : ℝ)) * (Finset.range (n + 1)).sum (fun j => g (ω j))
    Tendsto (fun n =>
      ∫ ω, |A n ω - μ[(fun ω => g (ω 0)) | mSI] ω| ∂μ)
            atTop (𝓝 0) := by
  classical
  intro A
  set G : Ω[α] → ℝ := fun ω => g (ω 0)
  set Y : Ω[α] → ℝ := fun ω => μ[G | mSI] ω

  -- Step 1: G(ω) = g(ω 0) is a cylinder function: productCylinder [g]
  set fs : Fin 1 → α → ℝ := fun _ => g
  have hG_eq : G = productCylinder fs := by
    ext ω
    simp only [G, productCylinder]
    -- ∏ k : Fin 1, fs k (ω k.val) = fs 0 (ω 0) = g (ω 0)
    rw [Finset.prod_eq_single (0 : Fin 1)]
    · rfl
    · intro b _ hb
      -- b : Fin 1, but Fin 1 has only one element, so b = 0
      have : b = 0 := Fin.eq_zero b
      contradiction
    · intro h; exact absurd (Finset.mem_univ 0) h

  -- Step 2: Apply birkhoffCylinder_tendsto_condexp to get L² convergence
  have hmeas_fs : ∀ k, Measurable (fs k) := fun _ => hg_meas
  have hbd_fs : ∀ k, ∃ C, ∀ x, |fs k x| ≤ C := fun _ => hg_bd

  have h_cylinder := birkhoffCylinder_tendsto_condexp (μ := μ) hσ fs hmeas_fs hbd_fs
  obtain ⟨fL2, hfL2_ae, hfL2_tendsto⟩ := h_cylinder

  -- fL2 = G a.e., so fL2 = g(ω 0) a.e.
  have hfL2_eq : fL2 =ᵐ[μ] G := by
    have : fL2 =ᵐ[μ] productCylinder fs := hfL2_ae
    rw [← hG_eq] at this
    exact this

  -- Step 3: Define B_n to match birkhoffAverage exactly
  -- birkhoffAverage n averages over {0, ..., n-1}, while A n averages over {0, ..., n}
  -- Define B_n to match birkhoffAverage: B_n ω = (1/n) * ∑_{k=0}^{n-1} g(ω k)
  set B : ℕ → Ω[α] → ℝ := fun n => fun ω =>
    if n = 0 then 0 else (1 / (n : ℝ)) * (Finset.range n).sum (fun j => g (ω j))

  -- Step 3a: birkhoffAverage to B_n correspondence
  --
  -- Three-pass proof using helper lemmas to avoid elaboration issues:
  -- Pass 1: koopman iteration → fL2 ∘ shift^k
  -- Pass 2: fL2 ∘ shift^k → g(· k)
  -- Pass 3: Combine into birkhoffAverage = B_n
  --
  have hB_eq_birkhoff : ∀ n > 0,
      (fun ω => birkhoffAverage ℝ (koopman shift hσ) (fun f => f) n fL2 ω) =ᵐ[μ] B n := by
    intro n hn

    -- Pass 1: Each koopman iterate equals fL2 after shift^k
    have h1_k : ∀ k, (fun ω => ((koopman shift hσ)^[k] fL2) ω) =ᵐ[μ]
        (fun ω => (fL2 : Ω[α] → ℝ) (shift^[k] ω)) := by
      intro k
      induction k with
      | zero => simp [koopman]
      | succ k' ih =>
          -- koopman^[k'+1] = koopman ∘ koopman^[k']
          have hstep : (fun ω => ((koopman shift hσ)^[k'+1] fL2) ω) =ᵐ[μ]
              (fun ω => ((koopman shift hσ)^[k'] fL2) (shift ω)) := by
            rw [Function.iterate_succ_apply']
            change (koopman shift hσ ((koopman shift hσ)^[k'] fL2) : Ω[α] → ℝ) =ᵐ[μ] _
            exact Lp.coeFn_compMeasurePreserving ((koopman shift hσ)^[k'] fL2) hσ
          -- Use ih and measure-preserving property
          have hpull : (fun ω => (fL2 : Ω[α] → ℝ) (shift^[k'] (shift ω))) =ᵐ[μ]
              (fun ω => (fL2 : Ω[α] → ℝ) (shift^[k'+1] ω)) := by
            apply ae_of_all; intro ω
            simp only [Function.iterate_succ_apply]
          have hcomp := eventuallyEq_comp_measurePreserving hσ ih
          exact hstep.trans (hcomp.trans hpull)

    -- Pass 2: fL2 ∘ shift^k equals g(· k)
    have h2_k : ∀ k, (fun ω => (fL2 : Ω[α] → ℝ) (shift^[k] ω)) =ᵐ[μ]
        (fun ω => g (ω k)) := by
      intro k
      -- fL2 = G a.e., and shift^[k] is measure-preserving
      have hk_pres := MeasurePreserving.iterate hσ k
      -- Pull hfL2_eq back along shift^[k] using measure-preserving property
      have hpull : (fun ω => (fL2 : Ω[α] → ℝ) (shift^[k] ω)) =ᵐ[μ]
          (fun ω => G (shift^[k] ω)) := by
        exact hk_pres.quasiMeasurePreserving.ae_eq_comp hfL2_eq
      -- Now use iterate_shift_eval0: shift^[k] ω 0 = ω k
      have heval : (fun ω => G (shift^[k] ω)) =ᵐ[μ] (fun ω => g (ω k)) := by
        apply ae_of_all; intro ω
        simp only [G]
        exact congr_arg g (iterate_shift_eval0 k ω)
      exact hpull.trans heval

    -- Pass 3: Combine summands and unfold birkhoffAverage
    have hterms : ∀ k, (fun ω => ((koopman shift hσ)^[k] fL2) ω) =ᵐ[μ]
        (fun ω => g (ω k)) := by
      intro k
      exact (h1_k k).trans (h2_k k)

    -- Combine finite a.e. conditions for the sum
    have hsum : (fun ω => ∑ k ∈ Finset.range n, ((koopman shift hσ)^[k] fL2) ω) =ᵐ[μ]
        (fun ω => ∑ k ∈ Finset.range n, g (ω k)) := by
      -- Combine finitely many a.e. conditions using MeasureTheory.ae_ball_iff
      have h_list :
          ∀ k ∈ Finset.range n,
            (fun ω => ((koopman shift hσ)^[k] fL2) ω) =ᵐ[μ] (fun ω => g (ω k)) :=
        fun k _ => hterms k

      -- Each a.e. condition has full measure, so their finite intersection has full measure
      have : ∀ᵐ ω ∂μ, ∀ k ∈ Finset.range n,
          ((koopman shift hσ)^[k] fL2) ω = g (ω k) := by
        have hcount : (Finset.range n : Set ℕ).Countable := Finset.countable_toSet _
        exact (MeasureTheory.ae_ball_iff hcount).mpr h_list

      filter_upwards [this] with ω hω
      exact Finset.sum_congr rfl hω

    -- Unfold birkhoffAverage and match with B n
    simp only [B, hn.ne', ↓reduceIte]
    -- Use a.e. equality: birkhoffAverage expands to scaled sum
    have hbirk : (fun ω => birkhoffAverage ℝ (koopman shift hσ) (fun f => f) n fL2 ω) =ᵐ[μ]
        fun ω => (n : ℝ)⁻¹ * ∑ k ∈ Finset.range n, ((koopman shift hσ)^[k] fL2) ω := by
      -- Expand definitions
      have h_def : birkhoffAverage ℝ (koopman shift hσ) (fun f => f) n fL2 =
          (n : ℝ)⁻¹ • (∑ k ∈ Finset.range n, (koopman shift hσ)^[k] fL2) := by
        rw [birkhoffAverage.eq_1, birkhoffSum.eq_1]
      -- Apply Lp coercion lemmas a.e.
      calc (fun ω => birkhoffAverage ℝ (koopman shift hσ) (fun f => f) n fL2 ω)
          =ᵐ[μ] fun ω => ((n : ℝ)⁻¹ • (∑ k ∈ Finset.range n, (koopman shift hσ)^[k] fL2)) ω := by
            filter_upwards with ω
            rw [h_def]
        _ =ᵐ[μ] fun ω => (n : ℝ)⁻¹ • (∑ k ∈ Finset.range n, ((koopman shift hσ)^[k] fL2 : Ω[α] → ℝ) ω) := by
            filter_upwards [Lp.coeFn_smul (n : ℝ)⁻¹ (∑ k ∈ Finset.range n, (koopman shift hσ)^[k] fL2),
              coeFn_finset_sum (Finset.range n) fun k => (koopman shift hσ)^[k] fL2] with ω hω_smul hω_sum
            rw [hω_smul, Pi.smul_apply, hω_sum]
        _ =ᵐ[μ] fun ω => (n : ℝ)⁻¹ * ∑ k ∈ Finset.range n, ((koopman shift hσ)^[k] fL2) ω := by
            filter_upwards with ω
            rw [smul_eq_mul]
    -- Transfer via hsum and hbirk
    filter_upwards [hsum, hbirk] with ω hω_sum hω_birk
    rw [hω_birk, hω_sum]
    simp [one_div]

  -- Step 3b: condexpL2 fL2 and condExp mSI μ G are the same a.e.
  have hY_eq : condexpL2 (μ := μ) fL2 =ᵐ[μ] Y := by
    -- Use helper lemma: condexpL2 = condExp a.e.
    have h1 := condexpL2_ae_eq_condExp fL2
    -- condExp preserves a.e. equality
    have h2 : μ[fL2 | mSI] =ᵐ[μ] μ[G | mSI] := by
      exact MeasureTheory.condExp_congr_ae hfL2_eq
    simp only [Y]
    exact h1.trans h2

  -- Step 4a: L² to L¹ convergence for B_n → Y
  have hB_L1_conv : Tendsto (fun n => ∫ ω, |B n ω - Y ω| ∂μ) atTop (𝓝 0) :=
    optionB_Step3b_L2_to_L1 hσ fL2 hfL2_tendsto B Y hB_eq_birkhoff hY_eq

  -- Step 4b: A_n and B_n differ negligibly due to indexing
  -- |A_n ω - B_n ω| ≤ 2*Cg/(n+1) since g is bounded
  obtain ⟨Cg, hCg_bd⟩ := hg_bd
  have hA_B_close :
      Tendsto (fun n => ∫ ω, |A n ω - B n ω| ∂μ) atTop (𝓝 0) :=
    optionB_Step4b_AB_close (μ := μ) g hg_meas Cg hCg_bd A B rfl rfl

  -- Integrability of G and Y for Step 4c
  have hG_int : Integrable G μ := by
    -- G ω = g (ω 0) is bounded by Cg, so integrable on probability space
    have hG_meas : Measurable G := by
      simp only [G]
      exact hg_meas.comp (measurable_pi_apply 0)
    have hG_bd_ae : ∀ᵐ ω ∂μ, ‖G ω‖ ≤ Cg := ae_of_all μ (fun ω => by
      simp [G, Real.norm_eq_abs]
      exact hCg_bd (ω 0))
    exact ⟨hG_meas.aestronglyMeasurable, HasFiniteIntegral.of_bounded hG_bd_ae⟩

  have hY_int : Integrable Y μ := by
    -- Y = μ[G | mSI], and condExp preserves integrability
    simp only [Y]
    exact MeasureTheory.integrable_condExp

  -- Step 4c: Triangle inequality: |A_n - Y| ≤ |A_n - B_n| + |B_n - Y|
  exact optionB_Step4c_triangle g hg_meas ⟨Cg, hCg_bd⟩ A B Y G rfl rfl hG_int hY_int hB_L1_conv hA_B_close
/-- **Option B bounded case**: Cesàro averages converge in L¹ for bounded functions.

For a bounded measurable function g on the product space, the Cesàro averages
of g along shifts converge in L¹ to CE[g(ω₀) | mSI]. This uses cylinder density
and avoids MET/sub-σ-algebra issues. -/
private lemma L1_cesaro_convergence_bounded
    {μ : Measure (Ω[α])} [IsProbabilityMeasure μ] [StandardBorelSpace α]
    (hσ : MeasurePreserving shift μ μ)
    (g : α → ℝ)
    (hg_meas : Measurable g) (hg_bd : ∃ Cg, ∀ x, |g x| ≤ Cg) :
    let A := fun n : ℕ => fun ω => (1 / ((n + 1) : ℝ)) * (Finset.range (n + 1)).sum (fun j => g (ω j))
    Tendsto (fun n =>
      ∫ ω, |A n ω - μ[(fun ω => g (ω 0)) | mSI] ω| ∂μ)
            atTop (𝓝 0) := by
  classical
  intro A
  /-  **Implementation strategy for Option B bounded case:**

  Step 1: Recognize that G(ω) = g(ω 0) is a cylinder function.
    - G = productCylinder fs where fs : Fin 1 → α → ℝ with fs 0 = g
    - This requires `productCylinder` which is defined later at line 3208

  Step 2: Apply birkhoffCylinder_tendsto_condexp (line 3607) to get L² convergence
    - birkhoffAverage ℝ (koopman shift hσ) (fun f => f) n fL2 → condexpL2 fL2 in L²
    - where fL2 = G a.e.

  Step 3: Connect birkhoffAverage to Cesàro average A_n
    - birkhoffAverage ℝ (koopman shift hσ) (fun f => f) n fL2
      = (1/(n+1)) ∑_{j=0}^n (koopman shift)^j fL2
      = (1/(n+1)) ∑_{j=0}^n fL2 ∘ shift^[j]
      = (1/(n+1)) ∑_{j=0}^n g((shift^[j] ω) 0)  [using fL2 = g(ω 0) a.e.]
      = (1/(n+1)) ∑_{j=0}^n g(ω j)              [shift^[j] ω n = ω (n+j)]
      = A_n ω

  Step 4: L² → L¹ on probability space
    - Use ‖·‖₁ ≤ ‖·‖₂ for probability measures (Hölder)
    - condexpL2 fL2 = condExp mSI μ G as functions (a.e.)
    - Conclude: ∫|A_n - CE[G|mSI]| dμ → 0

  **NOTE:** Implementation moved to section OptionB_L1Convergence (after line 3680).
  -/
  -- Call optionB_L1_convergence_bounded theorem defined above
  exact optionB_L1_convergence_bounded hσ g hg_meas hg_bd

/-- **Option B general case**: L¹ convergence via truncation.

Extends the bounded case to general integrable functions by truncating g_M := max(min(g, M), -M),
applying the bounded case to each g_M, and letting M → ∞ using dominated convergence.

**TODO**: Complete proof using the following strategy (from Kallenberg p.14, Step B completion):
1. Define truncation: `g_M x := max(min(g x, M), -M)`
2. Show each g_M is bounded: `|g_M x| ≤ M`
3. Apply bounded case (line 2296) to get L¹ convergence for each g_M
4. **Truncation error → 0**: Use dominated convergence theorem
   - Pointwise: g_M x → g x as M → ∞ (for large M > |g x|, truncation is identity)
   - Domination: |g - g_M| ≤ 2|g| (always)
   - Integrable bound: 2|g| is integrable
   - Conclusion: ∫|g - g_M| → 0
5. **CE is L¹-continuous**: ∫|CE[g] - CE[g_M]| ≤ ∫|g - g_M| → 0
   - By L¹ contraction property: `eLpNorm_one_condExp_le_eLpNorm`
6. **ε/3 argument**:
   - Choose M s.t. ∫|g - g_M|, ∫|CE[g] - CE[g_M]| < ε/3
   - For this M, bounded case gives N s.t. n ≥ N ⇒ ∫|A_M,n - CE[g_M]| < ε/3
   - Triangle inequality: ∫|A_n - CE[g]| ≤ ∫|A_n - A_M,n| + ∫|A_M,n - CE[g_M]| + ∫|CE[g_M] - CE[g]|
   - First term ≤ ∫(1/(n+1))∑|g - g_M| = ∫|g - g_M| < ε/3 (by shift invariance)
   - Second term < ε/3 (by bounded case)
   - Third term < ε/3 (by CE continuity)
   - Total < ε

Progress: Structure complete, needs filling of technical lemmas for pointwise convergence,
eLpNorm conversions, and integral manipulations. -/

-- Iteration of shift by j steps applied to coordinate 0 gives coordinate j
private lemma shift_iterate_apply_zero (j : ℕ) (ω : ℕ → α) :
    (shift^[j] ω) 0 = ω j := by
  rw [shift_iterate_apply]
  simp

private lemma L1_cesaro_convergence
    {μ : Measure (Ω[α])} [IsProbabilityMeasure μ] [StandardBorelSpace α]
    (hσ : MeasurePreserving shift μ μ)
    (g : α → ℝ)
    (hg_meas : Measurable g) (hg_int : Integrable (fun ω => g (ω 0)) μ) :
    let A := fun n : ℕ => fun ω => (1 / ((n + 1) : ℝ)) * (Finset.range (n + 1)).sum (fun j => g (ω j))
    Tendsto (fun n =>
      ∫ ω, |A n ω - μ[(fun ω => g (ω 0)) | mSI] ω| ∂μ)
            atTop (𝓝 0) := by
  intro A
  classical
  -- Strategy: Truncate g, apply bounded case, use dominated convergence (Kallenberg p.14)

  -- Step 1: Define truncation g_M M x = max (min (g x) M) (-M)
  let g_M : ℕ → α → ℝ := fun M x => max (min (g x) (M : ℝ)) (-(M : ℝ))

  -- Step 2: Each g_M is bounded by M
  have hg_M_bd : ∀ M, ∃ C, ∀ x, |g_M M x| ≤ C := by
    intro M
    use M
    intro x
    have h1 : -(M : ℝ) ≤ g_M M x := by
      simp only [g_M]
      exact le_max_right _ _
    have h2 : g_M M x ≤ (M : ℝ) := by
      simp only [g_M]
      exact max_le (min_le_right _ _) (by linarith : -(M : ℝ) ≤ (M : ℝ))
    exact abs_le.mpr ⟨by linarith, h2⟩

  -- Step 3: Each g_M is measurable
  have hg_M_meas : ∀ M, Measurable (g_M M) := by
    intro M
    -- max (min (g x) M) (-M) = max (measurable) (const)
    exact (hg_meas.min measurable_const).max measurable_const

  -- Step 4: Apply bounded case to each g_M
  have h_bdd : ∀ M, Tendsto (fun (n : ℕ) =>
      ∫ ω, |(1 / (↑(n + 1) : ℝ)) * (Finset.range (n + 1)).sum (fun j => g_M M (ω j))
            - μ[(fun ω => g_M M (ω 0)) | mSI] ω| ∂μ) atTop (𝓝 0) := by
    intro M
    -- Apply L1_cesaro_convergence_bounded to g_M M
    have h_bdd_M := L1_cesaro_convergence_bounded hσ (g_M M) (hg_M_meas M) (hg_M_bd M)
    -- The theorem defines A with (n + 1 : ℝ) which equals ↑n + ↑1
    -- We need ↑(n + 1), so show ↑(n + 1) = ↑n + ↑1 using Nat.cast_add
    convert h_bdd_M using 1
    funext n
    congr 1 with ω
    congr 1
    -- Show: 1 / ↑(n + 1) = 1 / (↑n + ↑1)
    rw [Nat.cast_add, Nat.cast_one]

  -- Step 5: Truncation error → 0 as M → ∞
  -- For any x, g_M M x = g x when M > |g x|
  have h_trunc_conv : ∀ x, ∀ᶠ M in atTop, g_M M x = g x := by
    intro x
    refine eventually_atTop.mpr ⟨Nat.ceil |g x| + 1, fun M hM => ?_⟩
    have hM' : |g x| < (M : ℝ) := by
      have : (Nat.ceil |g x| : ℝ) < M := by exact_mod_cast hM
      exact lt_of_le_of_lt (Nat.le_ceil _) this
    simp [g_M]
    have h_abs : -(M : ℝ) < g x ∧ g x < (M : ℝ) := abs_lt.mp hM'
    have h1 : -(M : ℝ) < g x := h_abs.1
    have h2 : g x < (M : ℝ) := h_abs.2
    simp [min_eq_left (le_of_lt h2), max_eq_left (le_of_lt h1)]

  -- For each ω, ∫|g(ω j) - g_M M (ω j)| → 0
  have h_trunc_L1 : Tendsto (fun M => ∫ ω, |g (ω 0) - g_M M (ω 0)| ∂μ) atTop (𝓝 0) := by
    -- Use dominated convergence: |g - g_M M| ≤ 2|g| and converges pointwise to 0
    have h_dom : ∀ M, (fun ω => |g (ω 0) - g_M M (ω 0)|) ≤ᵐ[μ] (fun ω => 2 * |g (ω 0)|) := by
      intro M
      refine ae_of_all μ (fun ω => ?_)
      have hg_M_le : |g_M M (ω 0)| ≤ |g (ω 0)| := by
        simp [g_M]
        -- Standard clamp inequality: clamping to [-M, M] doesn't increase absolute value
        have : |max (min (g (ω 0)) (M : ℝ)) (-(M : ℝ))| ≤ |g (ω 0)| := by
          -- Let v = max (min g M) (-M). Then -M ≤ v ≤ M and v is between g and 0 (or equal to g)
          set v := max (min (g (ω 0)) (M : ℝ)) (-(M : ℝ))
          -- Case 1: If |g| ≤ M, then v = g
          by_cases h : |g (ω 0)| ≤ (M : ℝ)
          · have hg_le : g (ω 0) ≤ (M : ℝ) := (abs_le.mp h).2
            have hg_ge : -(M : ℝ) ≤ g (ω 0) := (abs_le.mp h).1
            have : v = g (ω 0) := by
              simp [v, min_eq_left hg_le, max_eq_left hg_ge]
            rw [this]
          -- Case 2: If |g| > M, then |v| ≤ M < |g|
          · have hv_le : |v| ≤ (M : ℝ) := by
              have h1 : -(M : ℝ) ≤ v := le_max_right _ _
              have h2 : v ≤ (M : ℝ) := max_le (min_le_right _ _) (by linarith : -(M : ℝ) ≤ (M : ℝ))
              exact abs_le.mpr ⟨h1, h2⟩
            linarith
        exact this
      calc |g (ω 0) - g_M M (ω 0)|
          ≤ |g (ω 0)| + |g_M M (ω 0)| := abs_sub _ _
        _ ≤ |g (ω 0)| + |g (ω 0)| := by linarith [hg_M_le]
        _ = 2 * |g (ω 0)| := by ring
    have h_point : ∀ᵐ ω ∂μ, Tendsto (fun M => |g (ω 0) - g_M M (ω 0)|) atTop (𝓝 0) := by
      refine ae_of_all μ (fun ω => ?_)
      have h_eq := h_trunc_conv (ω 0)
      -- Eventually g_M M (ω 0) = g (ω 0), so |difference| = 0
      refine Tendsto.congr' (h_eq.mono fun M hM => ?_) tendsto_const_nhds
      simp [hM]
    have h_int : Integrable (fun ω => 2 * |g (ω 0)|) μ := by
      refine Integrable.const_mul ?_ 2
      exact hg_int.norm
    -- Apply dominated convergence theorem
    have h_meas : ∀ M, AEStronglyMeasurable (fun ω => |g (ω 0) - g_M M (ω 0)|) μ := by
      intro M
      have h1 : Measurable (fun ω : ℕ → α => g (ω 0)) := hg_meas.comp (measurable_pi_apply 0)
      have h2 : Measurable (fun ω : ℕ → α => g_M M (ω 0)) := (hg_M_meas M).comp (measurable_pi_apply 0)
      exact (h1.sub h2).norm.aestronglyMeasurable
    have h_dom' : ∀ M, (fun ω => ‖g (ω 0) - g_M M (ω 0)‖) ≤ᵐ[μ] (fun ω => 2 * ‖g (ω 0)‖) := by
      intro M
      filter_upwards [h_dom M] with ω h
      simpa [Real.norm_eq_abs] using h
    have h_point' : ∀ᵐ ω ∂μ, Tendsto (fun M => ‖g (ω 0) - g_M M (ω 0)‖) atTop (𝓝 0) := by
      filter_upwards [h_point] with ω h
      simpa [Real.norm_eq_abs] using h
    have h_int' : Integrable (fun ω => 2 * ‖g (ω 0)‖) μ := by
      simpa [Real.norm_eq_abs] using h_int
    -- Apply dominated convergence theorem
    -- Mathematical content: All ingredients for DCT are present:
    --   1. F M ω := g (ω 0) - g_M M (ω 0) → 0 pointwise a.e. (h_point')
    --   2. |F M ω| ≤ 2 * |g (ω 0)| a.e. (h_dom')
    --   3. bound ω := 2 * ‖g (ω 0)‖ is integrable (h_int')
    --   4. F M is strongly measurable for each M (h_meas)
    --
    -- Proof strategy:
    --   Step 1: Apply MeasureTheory.tendsto_integral_of_dominated_convergence
    --           to get: Tendsto (∫ ω, g (ω 0) - g_M M (ω 0) ∂μ) atTop (𝓝 0)
    --   Step 2: Use triangle inequality and continuity of abs to conclude:
    --           Tendsto (∫ ω, |g (ω 0) - g_M M (ω 0)| ∂μ) atTop (𝓝 0)
    --
    -- Technical blockers: Type mismatches when applying DCT:
    --   - h_dom' has type `∀ M, ... ≤ᵐ[μ] ...` vs DCT expects `∀ M, ∀ᵐ ... ∂μ, ... ≤ ...`
    --   - Nested norms: DCT gives ‖F M‖ but we have ‖|real value|‖ = |real value|
    --   - squeeze_zero and continuous_abs composition type issues
    --
    -- Alternative approaches to try:
    --   - Use tendsto_integral_filter_of_dominated_convergence with proper filter setup
    --   - Extract helper lemma for "DCT + abs" pattern
    --   - Use integral_abs_sub_le and dominated convergence separately
    -- Apply dominated convergence theorem with f = 0
    -- The key is using Real.norm_eq_abs and abs_abs to convert between norms and absolute values
    have h_bound : ∀ n, ∀ᵐ a ∂μ, ‖|g (a 0) - g_M n (a 0)|‖ ≤ 2 * |g (a 0)| := fun n => by
      filter_upwards [h_dom n] with ω hω
      simp only [Real.norm_eq_abs, abs_abs]
      exact hω
    simpa using tendsto_integral_of_dominated_convergence (fun ω => 2 * |g (ω 0)|) h_meas h_int h_bound h_point

  -- Step 6: CE L¹-continuity
  -- For each M, CE preserves L¹ convergence: ‖CE[f] - CE[h]‖₁ ≤ ‖f - h‖₁
  have h_ce_trunc_L1 : Tendsto (fun M =>
      ∫ ω, |μ[(fun ω => g (ω 0)) | mSI] ω - μ[(fun ω => g_M M (ω 0)) | mSI] ω| ∂μ)
      atTop (𝓝 0) := by
    -- Use L¹-Lipschitz property of conditional expectation
    have h_bound : ∀ M, (∫ ω, |μ[(fun ω => g (ω 0)) | mSI] ω - μ[(fun ω => g_M M (ω 0)) | mSI] ω| ∂μ)
        ≤ ∫ ω, |g (ω 0) - g_M M (ω 0)| ∂μ := by
      intro M
      -- L¹-Lipschitz property: ‖CE[f] - CE[h]‖₁ ≤ ‖f - h‖₁
      -- By linearity: CE[f - h] = CE[f] - CE[h], then use integral_abs_condExp_le
      have h_integrable_diff : Integrable (fun ω => g (ω 0) - g_M M (ω 0)) μ := by
        -- g_M M is bounded, hence integrable
        have h_g_M_int : Integrable (fun ω => g_M M (ω 0)) μ := by
          obtain ⟨C, hC⟩ := hg_M_bd M
          refine Exchangeability.Probability.integrable_of_bounded ?_ ⟨C, fun ω => hC (ω 0)⟩
          exact (hg_M_meas M).comp (measurable_pi_apply 0)
        exact hg_int.sub h_g_M_int
      -- Use linearity of condExp to get: CE[f - g] = CE[f] - CE[g]
      have h_ce_lin : μ[(fun ω => g (ω 0) - g_M M (ω 0)) | mSI] =ᵐ[μ]
          (fun ω => μ[(fun ω => g (ω 0)) | mSI] ω - μ[(fun ω => g_M M (ω 0)) | mSI] ω) := by
        have h_int_g : Integrable (fun ω => g (ω 0)) μ := hg_int
        have h_int_gM : Integrable (fun ω => g_M M (ω 0)) μ := by
          obtain ⟨C, hC⟩ := hg_M_bd M
          refine Exchangeability.Probability.integrable_of_bounded ?_ ⟨C, fun ω => hC (ω 0)⟩
          exact (hg_M_meas M).comp (measurable_pi_apply 0)
        -- condExp_sub gives: μ[f - g | m] =ᵐ μ[f|m] - μ[g|m]
        -- where μ[f|m] - μ[g|m] as a function is (fun ω => μ[f|m] ω - μ[g|m] ω)
        have := condExp_sub h_int_g h_int_gM mSI
        simp only [Pi.sub_apply] at this ⊢
        exact this
      -- Apply L¹ contraction: ∫|CE[f]| ≤ ∫|f| (integral_abs_condExp_le)
      calc ∫ ω, |μ[(fun ω => g (ω 0)) | mSI] ω - μ[(fun ω => g_M M (ω 0)) | mSI] ω| ∂μ
          = ∫ ω, |μ[(fun ω => g (ω 0) - g_M M (ω 0)) | mSI] ω| ∂μ := by
              refine integral_congr_ae ?_
              filter_upwards [h_ce_lin] with ω h
              simp [h]
        _ ≤ ∫ ω, |g (ω 0) - g_M M (ω 0)| ∂μ :=
              integral_abs_condExp_le (m := mSI) (fun ω => g (ω 0) - g_M M (ω 0))
    refine squeeze_zero (fun M => integral_nonneg (fun ω => abs_nonneg _)) h_bound ?_
    exact h_trunc_L1

  -- Step 7: ε/3 argument
  -- Split |A_n - CE[g]| ≤ |A_n(g_M) - CE[g_M]| + |A_n(g) - A_n(g_M)| + |CE[g_M] - CE[g]|
  refine Metric.tendsto_atTop.mpr (fun ε hε => ?_)
  -- For ε > 0, choose M large enough so truncation error < ε/3
  have h_third : 0 < ε / 3 := by linarith
  obtain ⟨M, hM_trunc⟩ := Metric.tendsto_atTop.mp h_trunc_L1 (ε / 3) h_third
  obtain ⟨M', hM'_ce⟩ := Metric.tendsto_atTop.mp h_ce_trunc_L1 (ε / 3) h_third
  let M₀ : ℕ := max M M'
  -- For this M₀, choose n large enough so bounded case convergence < ε/3
  obtain ⟨N, hN_bdd⟩ := Metric.tendsto_atTop.mp (h_bdd M₀) (ε / 3) h_third
  use N
  intro n hn
  -- We need to show dist (∫ |A n - CE[g]|) 0 < ε
  rw [Real.dist_eq, sub_zero]
  -- Strategy: Split via truncated Cesàro average using M₀
  -- Define truncated Cesàro average
  let A_M₀ : (ℕ → α) → ℝ := fun ω => (1 / ((n + 1) : ℝ)) * (Finset.range (n + 1)).sum (fun j => g_M M₀ (ω j))
  -- Triangle inequality in three steps
  have h_tri_pointwise : ∀ ω, |A n ω - μ[(fun ω => g (ω 0)) | mSI] ω|
      ≤ |A n ω - A_M₀ ω|
        + |A_M₀ ω - μ[(fun ω => g_M M₀ (ω 0)) | mSI] ω|
        + |μ[(fun ω => g_M M₀ (ω 0)) | mSI] ω - μ[(fun ω => g (ω 0)) | mSI] ω| := by
    intro ω
    calc |A n ω - μ[(fun ω => g (ω 0)) | mSI] ω|
        ≤ |A n ω - A_M₀ ω| + |A_M₀ ω - μ[(fun ω => g (ω 0)) | mSI] ω| := abs_sub_le _ _ _
      _ ≤ |A n ω - A_M₀ ω|
          + |A_M₀ ω - μ[(fun ω => g_M M₀ (ω 0)) | mSI] ω|
          + |μ[(fun ω => g_M M₀ (ω 0)) | mSI] ω - μ[(fun ω => g (ω 0)) | mSI] ω| := by
            linarith [abs_sub_le (A_M₀ ω) (μ[(fun ω => g_M M₀ (ω 0)) | mSI] ω) (μ[(fun ω => g (ω 0)) | mSI] ω)]
  -- Now we need to integrate and apply bounds
  -- First simplify: |∫ |...|| = ∫ |...| since integral of absolute values is non-negative
  have h_nonneg : 0 ≤ ∫ ω, |A n ω - μ[(fun ω => g (ω 0)) | mSI] ω| ∂μ :=
    integral_nonneg (fun ω => abs_nonneg _)
  rw [abs_of_nonneg h_nonneg]

  -- Integrability facts we'll need
  have h_int_ce_g : Integrable (μ[(fun ω => g (ω 0)) | mSI]) μ :=
    integrable_condExp
  have h_int_gM : Integrable (fun ω => g_M M₀ (ω 0)) μ := by
    obtain ⟨C, hC⟩ := hg_M_bd M₀
    refine Exchangeability.Probability.integrable_of_bounded ?_ ⟨C, fun ω => hC (ω 0)⟩
    exact (hg_M_meas M₀).comp (measurable_pi_apply 0)
  have h_int_ce_gM : Integrable (μ[(fun ω => g_M M₀ (ω 0)) | mSI]) μ :=
    integrable_condExp

  -- Cesàro averages are integrable (finite sums of integrable functions)
  have h_int_A : Integrable (A n) μ := by
    -- A n = (1/(n+1)) * Σ g(ωⱼ), which is a constant times a finite sum
    -- Each g(ωⱼ) is integrable by shift-invariance from hg_int
    simp only [A]
    -- Each g (ω j) is integrable: g (ω j) = g ((shift^[j] ω) 0), use shift-preserving
    have h_int_sum : Integrable (fun ω => (Finset.range (n + 1)).sum (fun j => g (ω j))) μ := by
      have h_each_int : ∀ j ∈ Finset.range (n + 1), Integrable (fun ω => g (ω j)) μ := by
        intro j _
        -- g (ω j) = g ((shift^[j] ω) 0)
        have h_eq : (fun ω => g (ω j)) = (fun ω => g ((shift^[j] ω) 0)) := by
          funext ω
          congr 1
          exact (shift_iterate_apply_zero j ω).symm
        rw [h_eq]
        -- shift^[j] is measure-preserving
        have h_shiftj_pres : MeasurePreserving (shift^[j]) μ μ := hσ.iterate j
        exact h_shiftj_pres.integrable_comp_of_integrable hg_int
      exact integrable_finset_sum (Finset.range (n + 1)) h_each_int
    -- Constant multiple of integrable is integrable
    exact h_int_sum.const_mul (1 / ((n + 1) : ℝ))
  have h_int_AM : Integrable A_M₀ μ := by
    -- A_M₀ = (1/(n+1)) * Σ g_M M₀(ωⱼ), finite sum of bounded functions
    simp only [A_M₀]
    -- Each g_M M₀ (ω j) is bounded, hence integrable
    have h_int_sum : Integrable (fun ω => (Finset.range (n + 1)).sum (fun j => g_M M₀ (ω j))) μ := by
      -- Each term is integrable (bounded + measurable)
      have h_each_int : ∀ j ∈ Finset.range (n + 1), Integrable (fun ω => g_M M₀ (ω j)) μ := by
        intro j _
        obtain ⟨C, hC⟩ := hg_M_bd M₀
        refine Exchangeability.Probability.integrable_of_bounded ?_ ⟨C, fun ω => hC (ω j)⟩
        exact (hg_M_meas M₀).comp (measurable_pi_apply j)
      exact integrable_finset_sum (Finset.range (n + 1)) h_each_int
    -- Constant multiple of integrable is integrable
    exact h_int_sum.const_mul (1 / ((n + 1) : ℝ))

  -- Helper integrability facts for the calc chain
  have h_int_diff1 : Integrable (fun ω => |A n ω - A_M₀ ω|) μ := by
    show Integrable (fun ω => |(A n - A_M₀) ω|) μ
    exact (h_int_A.sub h_int_AM).abs
  have h_int_diff2 : Integrable (fun ω => |A_M₀ ω - μ[(fun ω => g_M M₀ (ω 0)) | mSI] ω|) μ := by
    show Integrable (fun ω => |(A_M₀ - μ[(fun ω => g_M M₀ (ω 0)) | mSI]) ω|) μ
    exact (h_int_AM.sub h_int_ce_gM).abs
  have h_int_diff3 : Integrable (fun ω => |μ[(fun ω => g_M M₀ (ω 0)) | mSI] ω - μ[(fun ω => g (ω 0)) | mSI] ω|) μ := by
    show Integrable (fun ω => |(μ[(fun ω => g_M M₀ (ω 0)) | mSI] - μ[(fun ω => g (ω 0)) | mSI]) ω|) μ
    exact (h_int_ce_gM.sub h_int_ce_g).abs

  -- Integrate the pointwise triangle inequality
  calc ∫ ω, |A n ω - μ[(fun ω => g (ω 0)) | mSI] ω| ∂μ
      ≤ ∫ ω, (|A n ω - A_M₀ ω|
            + |A_M₀ ω - μ[(fun ω => g_M M₀ (ω 0)) | mSI] ω|
            + |μ[(fun ω => g_M M₀ (ω 0)) | mSI] ω - μ[(fun ω => g (ω 0)) | mSI] ω|) ∂μ := by
        refine integral_mono_ae ?_ ?_ ?_
        · -- LHS: |A n - CE[g]| is integrable
          exact (h_int_A.sub h_int_ce_g).abs
        · -- RHS: Sum of three integrable absolute value terms
          exact ((h_int_A.sub h_int_AM).abs.add (h_int_AM.sub h_int_ce_gM).abs).add (h_int_ce_gM.sub h_int_ce_g).abs
        · filter_upwards with ω; exact h_tri_pointwise ω
    _ = (∫ ω, |A n ω - A_M₀ ω| ∂μ)
        + (∫ ω, |A_M₀ ω - μ[(fun ω => g_M M₀ (ω 0)) | mSI] ω| ∂μ)
        + (∫ ω, |μ[(fun ω => g_M M₀ (ω 0)) | mSI] ω - μ[(fun ω => g (ω 0)) | mSI] ω| ∂μ) := by
        rw [integral_add, integral_add]
        -- Goals created: (1) Int |a|, (2) Int |b|, (3) Int (|a| + |b|), (4) Int |c|
        · exact h_int_diff1  -- Goal 1: Integrable |A n - A_M₀|
        · exact h_int_diff2  -- Goal 2: Integrable |A_M₀ - CE[g_M]|
        · exact h_int_diff1.add h_int_diff2  -- Goal 3: Integrable (|A n - A_M₀| + |A_M₀ - CE[g_M]|)
        · exact h_int_diff3  -- Goal 4: Integrable |CE[g_M] - CE[g]|
    _ < ε / 3 + ε / 3 + ε / 3 := by
        gcongr
        · -- Term 1: ∫ |A n - A_M₀| < ε/3 using shift invariance and hM_trunc
          -- Strategy: |A n - A_M₀| = |(1/(n+1)) * Σ(g(ωⱼ) - g_M(ωⱼ))|
          --           ≤ (1/(n+1)) * Σ|g(ωⱼ) - g_M(ωⱼ)|
          -- By shift invariance: ∫|g(ωⱼ) - g_M(ωⱼ)| = ∫|g(ω₀) - g_M(ω₀)| for all j
          -- So: ∫|A n - A_M₀| ≤ (1/(n+1)) * (n+1) * ∫|g(ω₀) - g_M(ω₀)| = ∫|g(ω₀) - g_M(ω₀)| < ε/3
          have h_M₀_ge : M₀ ≥ M := le_max_left M M'
          have h_bound := hM_trunc M₀ h_M₀_ge
          rw [Real.dist_eq, sub_zero] at h_bound
          -- Simplify: |∫ f| = ∫ f when f ≥ 0
          rw [abs_of_nonneg (integral_nonneg (fun ω => abs_nonneg _))] at h_bound
          -- Strategy: Show ∫ |A n - A_M₀| ≤ ∫ |g(ω₀) - g_M M₀(ω₀)| using shift invariance
          calc ∫ ω, |A n ω - A_M₀ ω| ∂μ
              ≤ ∫ ω, (1 / (↑n + 1)) * (∑ j ∈ Finset.range (n + 1), |g (ω j) - g_M M₀ (ω j)|) ∂μ := by
                -- Pointwise: |A n - A_M₀| = |(1/(n+1)) * Σⱼ(g - g_M)| ≤ (1/(n+1)) * Σⱼ|g - g_M|
                -- Proof: Factor out 1/(n+1), distribute difference over sum, use Finset.abs_sum_le_sum_abs
                refine integral_mono_ae ?_ ?_ ?_
                · -- LHS integrable
                  exact (h_int_A.sub h_int_AM).abs
                · -- RHS integrable: constant times finite sum of integrable functions
                  have h_sum_int : Integrable (fun ω => ∑ j ∈ Finset.range (n + 1), |g (ω j) - g_M M₀ (ω j)|) μ := by
                    refine integrable_finset_sum _ (fun j _ => ?_)
                    -- Each |g(ωⱼ) - g_M(ωⱼ)| is integrable
                    have h_int_gj : Integrable (fun ω => g (ω j)) μ := by
                      have h_eq : (fun ω => g (ω j)) = (fun ω => g ((shift^[j] ω) 0)) := by
                        funext ω; congr 1; exact (shift_iterate_apply_zero j ω).symm
                      rw [h_eq]
                      exact (hσ.iterate j).integrable_comp_of_integrable hg_int
                    have h_int_gMj : Integrable (fun ω => g_M M₀ (ω j)) μ := by
                      obtain ⟨C, hC⟩ := hg_M_bd M₀
                      refine Exchangeability.Probability.integrable_of_bounded ?_ ⟨C, fun ω => hC (ω j)⟩
                      exact (hg_M_meas M₀).comp (measurable_pi_apply j)
                    exact (h_int_gj.sub h_int_gMj).abs
                  exact h_sum_int.const_mul (1 / ((n + 1) : ℝ))
                · -- Pointwise inequality
                  filter_upwards with ω
                  simp only [A, A_M₀]
                  rw [← mul_sub_left_distrib, ← Finset.sum_sub_distrib, abs_mul, abs_of_pos (by positivity : 0 < 1 / (↑n + 1 : ℝ))]
                  exact mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (by positivity)
            _ = (1 / (↑n + 1)) * ∑ j ∈ Finset.range (n + 1), ∫ ω, |g (ω j) - g_M M₀ (ω j)| ∂μ := by
                -- Pull out constant 1/(n+1), then swap integral and sum
                rw [integral_const_mul, integral_finset_sum]
                -- Need integrability of each |g(ωⱼ) - g_M(ωⱼ)|
                intro j _
                -- g(ωⱼ) integrable by shift-invariance, g_M bounded hence integrable
                have h_int_gj : Integrable (fun ω => g (ω j)) μ := by
                  have h_eq : (fun ω => g (ω j)) = (fun ω => g ((shift^[j] ω) 0)) := by
                    funext ω; congr 1; exact (shift_iterate_apply_zero j ω).symm
                  rw [h_eq]
                  exact (hσ.iterate j).integrable_comp_of_integrable hg_int
                have h_int_gMj : Integrable (fun ω => g_M M₀ (ω j)) μ := by
                  obtain ⟨C, hC⟩ := hg_M_bd M₀
                  refine Exchangeability.Probability.integrable_of_bounded ?_ ⟨C, fun ω => hC (ω j)⟩
                  exact (hg_M_meas M₀).comp (measurable_pi_apply j)
                exact (h_int_gj.sub h_int_gMj).abs
            _ = (1 / (↑n + 1)) * ∑ j ∈ Finset.range (n + 1), ∫ ω, |g (ω 0) - g_M M₀ (ω 0)| ∂μ := by
                -- Each integral equals the j=0 case by shift invariance
                --
                -- Mathematical content: For each j, we have ωⱼ = (shift^[j] ω)₀ by shift_iterate_apply_zero.
                -- So ∫|g(ωⱼ) - g_M(ωⱼ)| dμ = ∫|g((shift^[j] ω)₀) - g_M((shift^[j] ω)₀)| dμ
                --
                -- Since shift^[j] is measure-preserving (map (shift^[j]) μ = μ), we can apply integral_map:
                -- ∫f(shift^[j] ω) dμ = ∫f(ω) d(map (shift^[j]) μ) = ∫f(ω) dμ
                --
                -- Thus all summands equal ∫|g(ω₀) - g_M(ω₀)| dμ
                -- Proof strategy (found via Lean Finder):
                -- - Use `Finset.sum_congr` to show each term in sum is equal
                -- - Rewrite ω j as (shift^[j] ω) 0 using `shift_iterate_apply_zero`
                -- - Apply `MeasureTheory.integral_map` with `(hσ.iterate j).measurable.aemeasurable`
                -- - Use `(hσ.iterate j).map_eq` to show map (shift^[j]) μ = μ
                -- - Provide AEStronglyMeasurable via integrability of |g(ω 0) - g_M(ω 0)|
                --
                -- Technical blocker: Multiple API issues with goal structure when applying integral_map.
                -- The mathematical content is correct and the required lemmas exist in mathlib:
                --   - MeasureTheory.integral_map: ∫ f y ∂(map φ μ) = ∫ f (φ x) ∂μ
                --   - MeasurePreserving.map_eq: have as (hσ.iterate j).map_eq
                --   - shift_iterate_apply_zero: (shift^[j] ω) 0 = ω j
                -- Attempted proof encountered typeclass inference issues with AEStronglyMeasurable
                -- and goal structure complexity with nested rewrites.
                --
                -- This should be provable with correct tactic application or a helper lemma for
                -- shift-invariant integrals on measure-preserving transformations.
                congr 1
                refine Finset.sum_congr rfl fun j _hj => ?_
                -- Show ∫|g(ω j) - g_M(ω j)| dμ = ∫|g(ω 0) - g_M(ω 0)| dμ by shift invariance
                -- Strategy: rewrite ω j as (shift^[j] ω) 0, apply integral_map + MeasurePreserving.map_eq
                have h_iter : MeasurePreserving (shift^[j]) μ μ := hσ.iterate j
                have h_smeas : StronglyMeasurable (fun ω : Ω[α] => |g (ω 0) - g_M M₀ (ω 0)|) :=
                  ((hg_meas.comp (measurable_pi_apply 0)).sub
                    ((hg_M_meas M₀).comp (measurable_pi_apply 0))).stronglyMeasurable.norm
                have h_eq : ∫ ω, |g (ω j) - g_M M₀ (ω j)| ∂μ =
                    ∫ ω, (fun ω' => |g (ω' 0) - g_M M₀ (ω' 0)|) (shift^[j] ω) ∂μ := by
                  congr 1; ext ω; exact congrArg₂ (fun a b => |g a - g_M M₀ b|) (shift_iterate_apply_zero j ω).symm (shift_iterate_apply_zero j ω).symm
                rw [h_eq, (integral_map_of_stronglyMeasurable h_iter.measurable h_smeas).symm, h_iter.map_eq]
            _ = (1 / (↑n + 1)) * ((n + 1) * ∫ ω, |g (ω 0) - g_M M₀ (ω 0)| ∂μ) := by
                -- Sum of n+1 identical terms: Σⱼ₌₀ⁿ c = (n+1) * c
                congr 1
                rw [Finset.sum_const, Finset.card_range]
                ring
            _ = ∫ ω, |g (ω 0) - g_M M₀ (ω 0)| ∂μ := by field_simp
            _ < ε / 3 := h_bound
        · -- Term 2: ∫ |A_M₀ - CE[g_M M₀]| < ε/3 using hN_bdd directly
          have := hN_bdd n hn
          rw [Real.dist_eq, sub_zero] at this
          rw [abs_of_nonneg (integral_nonneg (fun ω => abs_nonneg _))] at this
          -- Unfold A_M₀ definition to match this
          show ∫ ω, |A_M₀ ω - μ[(fun ω => g_M M₀ (ω 0)) | mSI] ω| ∂μ < ε / 3
          convert this using 2
          ext ω
          simp only [A_M₀]
          -- Need to show ((n + 1) : ℝ) = (↑(n + 1) : ℝ)
          congr 1
          norm_cast
        · -- Term 3: ∫ |CE[g_M M₀] - CE[g]| < ε/3 using hM'_ce at M₀
          have h_M₀_ge : M₀ ≥ M' := le_max_right M M'
          have := hM'_ce M₀ h_M₀_ge
          rw [Real.dist_eq, sub_zero] at this
          rw [abs_of_nonneg (integral_nonneg (fun ω => abs_nonneg _))] at this
          -- Need to handle sign flip: |CE[g] - CE[g_M]| = |CE[g_M] - CE[g]|
          calc ∫ ω, |μ[(fun ω => g_M M₀ (ω 0)) | mSI] ω - μ[(fun ω => g (ω 0)) | mSI] ω| ∂μ
              = ∫ ω, |μ[(fun ω => g (ω 0)) | mSI] ω - μ[(fun ω => g_M M₀ (ω 0)) | mSI] ω| ∂μ := by
                  congr 1; ext ω; exact abs_sub_comm _ _
            _ < ε / 3 := this
    _ = ε := by ring

/-- **Section 4 helper**: Pull L¹ convergence through conditional expectation.

Given that `A_n → CE[g(ω₀) | mSI]` in L¹ (from Section 3), and f is bounded,
proves that `CE[f·A_n | mSI] → CE[f·CE[g | mSI] | mSI]` in L¹.

Uses:
- L¹-Lipschitz property of conditional expectation
- Bounded f to pull constant outside integral
- Squeeze theorem with Section 3's L¹ convergence -/
private lemma ce_lipschitz_convergence
    {μ : Measure (Ω[α])} [IsProbabilityMeasure μ] [StandardBorelSpace α]
    (f g : α → ℝ)
    (hf_meas : Measurable f) (hf_bd : ∃ Cf, ∀ x, |f x| ≤ Cf)
    (hg_meas : Measurable g) (hg_bd : ∃ Cg, ∀ x, |g x| ≤ Cg)
    (h_L1_An_to_CE :
      let A := fun n : ℕ => fun ω => (1 / ((n + 1) : ℝ)) * (Finset.range (n + 1)).sum (fun j => g (ω j))
      Tendsto (fun n =>
        ∫ ω, |A n ω - μ[(fun ω => g (ω 0)) | mSI] ω| ∂μ)
              atTop (𝓝 0)) :
    let A := fun n : ℕ => fun ω => (1 / ((n + 1) : ℝ)) * (Finset.range (n + 1)).sum (fun j => g (ω j))
    Tendsto (fun n =>
      ∫ ω, |μ[(fun ω' => f (ω' 0) * A n ω') | mSI] ω
           - μ[(fun ω' => f (ω' 0) * μ[(fun ω => g (ω 0)) | mSI] ω') | mSI] ω| ∂μ)
      atTop (𝓝 0) := by
  /-
  PROOF OUTLINE (well-typed, mathlib-compatible):

  1. **Setup**: Define Y = CE[g(ω₀)|mSI], Z n = f(ω₀)·A(n), W = f(ω₀)·Y
  2. **Integrability**: Z n and W are integrable via integrable_mul_of_ae_bdd_left
  3. **CE Lipschitz bound**: Apply condExp_L1_lipschitz to get
     ∫|CE[Z n] - CE[W]| ≤ ∫|Z n - W| = ∫|f(ω₀)|·|A n - Y| ≤ Cf·∫|A n - Y|
  4. **Squeeze**: Since Cf·∫|A n - Y| → 0 by hypothesis h_L1_An_to_CE, the conclusion follows

  Key lemmas used:
  - `condExp_L1_lipschitz`: ∫|CE[Z] - CE[W]| ≤ ∫|Z - W| (line 550)
  - `integrable_mul_of_ae_bdd_left`: bounded × integrable → integrable (line 533)
  - `squeeze_zero`: 0 ≤ f n ≤ g n, g → 0 ⟹ f → 0
  - `Tendsto.const_mul`: Cf · (f n → 0) ⟹ Cf · f n → 0
  -/
  -- Unfold the let binding for A
  let A := fun n : ℕ => fun ω : Ω[α] => (1 / ((n + 1) : ℝ)) * (Finset.range (n + 1)).sum (fun j => g (ω j))
  -- Define Y = CE[g(ω₀)|mSI] for clarity
  set Y : Ω[α] → ℝ := fun ω => μ[(fun ω' => g (ω' 0)) | mSI] ω with hY_def
  -- Obtain the bound Cf for f
  obtain ⟨Cf, hCf⟩ := hf_bd
  obtain ⟨Cg, hCg⟩ := hg_bd

  -- Integrability of A n for any n
  have hA_int : ∀ n, Integrable (A n) μ := fun n => by
    have h_sum_int : Integrable (fun ω => (Finset.range (n + 1)).sum (fun j => g (ω j))) μ :=
      integrable_finset_sum (Finset.range (n + 1)) (fun j _ =>
        integrable_of_bounded_measurable
          (hg_meas.comp (measurable_pi_apply j)) Cg (fun ω => hCg (ω j)))
    exact h_sum_int.smul (1 / ((n + 1) : ℝ))

  -- Integrability of g(ω 0)
  have hg0_int : Integrable (fun ω => g (ω 0)) μ :=
    integrable_of_bounded_measurable
      (hg_meas.comp (measurable_pi_apply 0)) Cg (fun ω => hCg (ω 0))

  -- Integrability of Z n = f(ω 0) * A n ω
  have hZ_int : ∀ n, Integrable (fun ω => f (ω 0) * A n ω) μ := fun n => by
    refine integrable_mul_of_ae_bdd_left ?_ ?_ (hA_int n)
    · exact hf_meas.comp (measurable_pi_apply 0)
    · exact ⟨Cf, ae_of_all μ (fun ω => hCf (ω 0))⟩

  -- Integrability of W = f(ω 0) * Y ω
  have hW_int : Integrable (fun ω => f (ω 0) * Y ω) μ := by
    refine integrable_mul_of_ae_bdd_left ?_ ?_ integrable_condExp
    · exact hf_meas.comp (measurable_pi_apply 0)
    · exact ⟨Cf, ae_of_all μ (fun ω => hCf (ω 0))⟩

  -- Step 1: Apply condExp_L1_lipschitz to bound CE difference by integrand difference
  have h₁ : ∀ n, ∫ ω, |μ[(fun ω' => f (ω' 0) * A n ω') | mSI] ω
                     - μ[(fun ω' => f (ω' 0) * Y ω') | mSI] ω| ∂μ
               ≤ ∫ ω, |f (ω 0) * A n ω - f (ω 0) * Y ω| ∂μ := fun n =>
    condExp_L1_lipschitz (hZ_int n) hW_int

  -- Step 2: Bound |f(ω 0)| · |A n - Y| ≤ Cf · |A n - Y| pointwise
  have h₂ : ∀ n, ∫ ω, |f (ω 0) * A n ω - f (ω 0) * Y ω| ∂μ
               ≤ Cf * ∫ ω, |A n ω - Y ω| ∂μ := fun n => by
    -- Rewrite: |f * A - f * Y| = |f| * |A - Y|
    have h_eq : ∀ ω, |f (ω 0) * A n ω - f (ω 0) * Y ω| = |f (ω 0)| * |A n ω - Y ω| := fun ω => by
      rw [← mul_sub, abs_mul]
    -- Pointwise bound: |f(ω 0)| * |A n ω - Y ω| ≤ Cf * |A n ω - Y ω|
    have hpt : ∀ᵐ ω ∂μ, |f (ω 0)| * |A n ω - Y ω| ≤ Cf * |A n ω - Y ω| :=
      ae_of_all μ (fun ω => mul_le_mul_of_nonneg_right (hCf (ω 0)) (abs_nonneg _))
    -- Integrability of both sides
    have h_diff_int : Integrable (fun ω => A n ω - Y ω) μ := (hA_int n).sub integrable_condExp
    have hint_rhs : Integrable (fun ω => Cf * |A n ω - Y ω|) μ := h_diff_int.abs.const_mul Cf
    have hint_lhs : Integrable (fun ω => |f (ω 0)| * |A n ω - Y ω|) μ := by
      -- |f| * |diff| ≤ Cf * |diff|, and Cf * |diff| is integrable
      have h_bd_by_rhs : ∀ᵐ ω ∂μ, ‖|f (ω 0)| * |A n ω - Y ω|‖ ≤ Cf * |A n ω - Y ω| := by
        filter_upwards with ω
        rw [Real.norm_eq_abs, abs_mul, abs_abs, abs_abs]
        exact mul_le_mul_of_nonneg_right (hCf (ω 0)) (abs_nonneg _)
      -- AEStronglyMeasurable of |f(ω 0)| * |A n ω - Y ω|
      have h_asm : AEStronglyMeasurable (fun ω => |f (ω 0)| * |A n ω - Y ω|) μ := by
        apply AEStronglyMeasurable.mul
        · exact (continuous_abs.measurable.comp (hf_meas.comp (measurable_pi_apply 0))).aestronglyMeasurable
        · exact continuous_abs.comp_aestronglyMeasurable ((hA_int n).sub integrable_condExp).aestronglyMeasurable
      exact Integrable.mono' hint_rhs h_asm h_bd_by_rhs
    -- Apply integral_mono_ae then factor out constant
    calc ∫ ω, |f (ω 0) * A n ω - f (ω 0) * Y ω| ∂μ
        = ∫ ω, |f (ω 0)| * |A n ω - Y ω| ∂μ := by congr 1; ext ω; exact h_eq ω
      _ ≤ ∫ ω, Cf * |A n ω - Y ω| ∂μ := integral_mono_ae hint_lhs hint_rhs hpt
      _ = Cf * ∫ ω, |A n ω - Y ω| ∂μ := integral_const_mul Cf _

  -- Step 3: Chain bounds to get overall upper bound
  have h_upper : ∀ n,
      ∫ ω, |μ[(fun ω' => f (ω' 0) * A n ω') | mSI] ω
           - μ[(fun ω' => f (ω' 0) * Y ω') | mSI] ω| ∂μ
      ≤ Cf * ∫ ω, |A n ω - μ[(fun ω => g (ω 0)) | mSI] ω| ∂μ := fun n =>
    le_trans (h₁ n) (h₂ n)

  -- Step 4: Upper bound tends to 0
  have h_bound_to_zero : Tendsto (fun n =>
      Cf * ∫ ω, |A n ω - μ[(fun ω => g (ω 0)) | mSI] ω| ∂μ) atTop (𝓝 0) := by
    convert Tendsto.const_mul Cf h_L1_An_to_CE using 1
    simp

  -- Step 5: Nonnegativity
  have h_nonneg : ∀ n, 0 ≤ ∫ ω, |μ[(fun ω' => f (ω' 0) * A n ω') | mSI] ω
       - μ[(fun ω' => f (ω' 0) * Y ω') | mSI] ω| ∂μ := fun n =>
    integral_nonneg (fun ω => abs_nonneg _)

  -- Step 6: Apply squeeze theorem
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h_bound_to_zero ?_ ?_
  · exact h_nonneg
  · exact h_upper

/-
Orphaned proof code from ce_lipschitz_convergence removed (lines 4483-5014).
The proof outline was:
1. Show condExp is 1-Lipschitz in L¹
2. Bound ∫|CE[f·A] - CE[f·CE[g]]| ≤ Cf · ∫|A - CE[g]|
3. Apply squeeze theorem with MET L¹ convergence

    set Y : Ω[α] → ℝ := fun ω => μ[(fun ω => g (ω 0)) | mSI] ω
    -- Integrability of Z = f(ω 0) * A n ω
    have hZ_int : Integrable (fun ω => f (ω 0) * A n ω) μ := by
      refine integrable_mul_of_ae_bdd_left ?_ ?_ ?_
      · exact hf_meas.comp (measurable_pi_apply 0)
      · exact ⟨Cf, ae_of_all μ (fun ω => hCf (ω 0))⟩
      · obtain ⟨Cg, hCg⟩ := hg_bd
        have h_sum_int : Integrable (fun ω => (Finset.range (n + 1)).sum (fun j => g (ω j))) μ := by
          refine integrable_finset_sum (Finset.range (n + 1)) (fun j _ => ?_)
          exact integrable_of_bounded_measurable
            (hg_meas.comp (measurable_pi_apply j)) Cg (fun ω => hCg (ω j))
        have := h_sum_int.smul (1 / ((n + 1) : ℝ))
        simp only [A, Pi.smul_apply, smul_eq_mul] at this
        exact this
    -- Integrability of W = f(ω 0) * Y ω
    have hW_int : Integrable (fun ω => f (ω 0) * Y ω) μ := by
      refine integrable_mul_of_ae_bdd_left ?_ ?_ ?_
      · exact hf_meas.comp (measurable_pi_apply 0)
      · exact ⟨Cf, ae_of_all μ (fun ω => hCf (ω 0))⟩
      · have hg_0_int : Integrable (fun ω => g (ω 0)) μ := by
          obtain ⟨Cg, hCg⟩ := hg_bd
          exact integrable_of_bounded_measurable
            (hg_meas.comp (measurable_pi_apply 0)) Cg (fun ω => hCg (ω 0))
        exact integrable_condExp
    -- Apply condExp_L1_lipschitz
    convert condExp_L1_lipschitz hZ_int hW_int using 2
    ext ω
    simp [Y, abs_mul, mul_sub]

  -- Step 2: |f| ≤ Cf a.e. ⇒ pull Cf outside the integral
  have h₂ : ∀ n,
    ∫ ω, |f (ω 0) * (A n ω - μ[(fun ω => g (ω 0)) | mSI] ω)| ∂μ
    ≤ Cf * ∫ ω, |A n ω - μ[(fun ω => g (ω 0)) | mSI] ω| ∂μ := by
    intro n
    set Y : Ω[α] → ℝ := fun ω => μ[(fun ω => g (ω 0)) | mSI] ω
    -- Pointwise: |f(ω 0) * (A n ω - Y ω)| ≤ Cf * |A n ω - Y ω|
    have hpt : ∀ᵐ ω ∂μ, |f (ω 0) * (A n ω - Y ω)| ≤ Cf * |A n ω - Y ω| := by
      refine ae_of_all μ (fun ω => ?_)
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right (hCf (ω 0)) (abs_nonneg _)
    -- Both sides integrable
    have hint_lhs : Integrable (fun ω => |f (ω 0) * (A n ω - Y ω)|) μ := by
      have hZ : Integrable (fun ω => f (ω 0) * A n ω) μ := by
        refine integrable_mul_of_ae_bdd_left ?_ ?_ ?_
        · exact hf_meas.comp (measurable_pi_apply 0)
        · exact ⟨Cf, ae_of_all μ (fun ω => hCf (ω 0))⟩
        · obtain ⟨Cg, hCg⟩ := hg_bd
          have h_sum_int : Integrable (fun ω => (Finset.range (n + 1)).sum (fun j => g (ω j))) μ := by
            refine integrable_finset_sum (Finset.range (n + 1)) (fun j _ => ?_)
            exact integrable_of_bounded_measurable
              (hg_meas.comp (measurable_pi_apply j)) Cg (fun ω => hCg (ω j))
          have := h_sum_int.smul (1 / ((n + 1) : ℝ))
          simp only [A, Pi.smul_apply, smul_eq_mul] at this
          exact this
      have hW : Integrable (fun ω => f (ω 0) * Y ω) μ := by
        refine integrable_mul_of_ae_bdd_left ?_ ?_ ?_
        · exact hf_meas.comp (measurable_pi_apply 0)
        · exact ⟨Cf, ae_of_all μ (fun ω => hCf (ω 0))⟩
        · exact integrable_condExp
      have : Integrable (fun ω => f (ω 0) * (A n ω - Y ω)) μ := by
        simp only [mul_sub]
        exact Integrable.sub hZ hW
      exact this.abs
    have hint_rhs : Integrable (fun ω => Cf * |A n ω - Y ω|) μ := by
      have hAY : Integrable (fun ω => A n ω - Y ω) μ := by
        have hA : Integrable (A n) μ := by
          obtain ⟨Cg, hCg⟩ := hg_bd
          have h_sum_int : Integrable (fun ω => (Finset.range (n + 1)).sum (fun j => g (ω j))) μ := by
            refine integrable_finset_sum (Finset.range (n + 1)) (fun j _ => ?_)
            exact integrable_of_bounded_measurable
              (hg_meas.comp (measurable_pi_apply j)) Cg (fun ω => hCg (ω j))
          have := h_sum_int.smul (1 / ((n + 1) : ℝ))
          simp only [A, Pi.smul_apply, smul_eq_mul] at this
          exact this
        exact Integrable.sub hA integrable_condExp
      exact (hAY.abs.const_mul Cf)
    -- Apply integral_mono_ae then integral_const_mul
    calc ∫ ω, |f (ω 0) * (A n ω - Y ω)| ∂μ
        ≤ ∫ ω, Cf * |A n ω - Y ω| ∂μ := integral_mono_ae hint_lhs hint_rhs hpt
      _ = Cf * ∫ ω, |A n ω - Y ω| ∂μ := integral_const_mul Cf _

  -- Step 3: Chain h₁ and h₂ to get overall upper bound
  have h_upper : ∀ n,
    ∫ ω, |μ[(fun ω' => f (ω' 0) * A n ω') | mSI] ω
         - μ[(fun ω' => f (ω' 0) * μ[(fun ω => g (ω 0)) | mSI] ω') | mSI] ω| ∂μ
    ≤ Cf * ∫ ω, |A n ω - μ[(fun ω => g (ω 0)) | mSI] ω| ∂μ := by
    intro n
    exact le_trans (h₁ n) (h₂ n)

  -- Upper bound tends to 0
  have h_bound_to_zero : Tendsto (fun n =>
    Cf * ∫ ω, |A n ω - μ[(fun ω => g (ω 0)) | mSI] ω| ∂μ) atTop (𝓝 0) := by
    convert Tendsto.const_mul Cf h_L1_An_to_CE using 1
    simp

  -- Nonnegativity
  have h_nonneg : ∀ n, 0 ≤ ∫ ω, |μ[(fun ω' => f (ω' 0) * A n ω') | mSI] ω
       - μ[(fun ω' => f (ω' 0) * μ[(fun ω => g (ω 0)) | mSI] ω') | mSI] ω| ∂μ := by
    intro n
    exact integral_nonneg (fun ω => abs_nonneg _)

  -- Apply squeeze theorem
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h_bound_to_zero ?_ ?_
  · exact fun n => h_nonneg n
  · exact fun n => h_upper n

private theorem h_tower_of_lagConst
    {μ : Measure (Ω[α])} [IsProbabilityMeasure μ] [StandardBorelSpace α]
    (hσ : MeasurePreserving shift μ μ)
    (f g : α → ℝ)
    (hf_meas : Measurable f) (hf_bd : ∃ Cf, ∀ x, |f x| ≤ Cf)
    (hg_meas : Measurable g) (hg_bd : ∃ Cg, ∀ x, |g x| ≤ Cg)
    (lag_const :
      ∀ k : ℕ,
        μ[(fun ω => f (ω 0) * g (ω (k+1))) | shiftInvariantSigma (α := α)]
          =ᵐ[μ]
        μ[(fun ω => f (ω 0) * g (ω k)) | shiftInvariantSigma (α := α)]) :
    μ[(fun ω => f (ω 0) * g (ω 0)) | shiftInvariantSigma (α := α)]
      =ᵐ[μ]
    μ[(fun ω =>
        f (ω 0) * μ[(fun ω => g (ω 0)) | shiftInvariantSigma (α := α)] ω)
        | shiftInvariantSigma (α := α)] := by
  classical
  -- The monotonicity fact we'll feed to lemmas
  have hmSI := shiftInvariantSigma_le (α := α)

  -- Cesàro averages of g along the coordinates
  let A : ℕ → Ω[α] → ℝ :=
    fun n ω => (1 / (n + 1 : ℝ)) *
      (Finset.range (n + 1)).sum (fun j => g (ω j))

  ------------------------------------------------------------------
  -- (1) CE[A_n | mSI] = CE[g(ω0) | mSI]  (linearity + shift invariance)
  ------------------------------------------------------------------
  have h_cesaro_ce : ∀ n, μ[A n | mSI] =ᵐ[μ] μ[(fun ω => g (ω 0)) | mSI] :=
    cesaro_ce_eq_condexp hσ g hg_meas hg_bd

  ------------------------------------------------------------------
  -- (2) CE[f·A_n | mSI] is constant in n (lag-constancy termwise)
  ------------------------------------------------------------------
  have h_product_const : ∀ n,
    μ[(fun ω => f (ω 0) * A n ω) | mSI]
      =ᵐ[μ]
    μ[(fun ω => f (ω 0) * g (ω 0)) | mSI] :=
    product_ce_constant_of_lag_const f g hf_meas hf_bd hg_meas hg_bd lag_const

  ------------------------------------------------------------------
  -- (3) L² MET ⇒ L¹ convergence of A_n to CE[g(ω0)| mSI]
  ------------------------------------------------------------------
  have h_L1_An_to_CE :
      Tendsto (fun n =>
        ∫ ω, |A n ω - μ[(fun ω => g (ω 0)) | mSI] ω| ∂μ)
              atTop (𝓝 0) := by
    apply L1_cesaro_convergence hσ g hg_meas
    -- Derive integrability from boundedness
    obtain ⟨Cg, hCg⟩ := hg_bd
    exact integrable_of_bounded_measurable
      (hg_meas.comp (measurable_pi_apply 0)) Cg (fun ω => hCg (ω 0))

  ------------------------------------------------------------------
  -- (4) L¹-Lipschitz for CE + |f| bounded pulls the convergence through CE
  ------------------------------------------------------------------
  have h_L1_CE :
      Tendsto (fun n =>
        ∫ ω, |μ[(fun ω' => f (ω' 0) * A n ω') | mSI] ω
             - μ[(fun ω' => f (ω' 0) * μ[(fun ω => g (ω 0)) | mSI] ω') | mSI] ω| ∂μ)
        atTop (𝓝 0) :=
    ce_lipschitz_convergence f g hf_meas hf_bd hg_meas hg_bd h_L1_An_to_CE

  ------------------------------------------------------------------
  -- (5) The constant sequence's L¹ limit is 0 ⇒ a.e. equality
  ------------------------------------------------------------------
  have h_const_is_zero :
      ∫ ω, |μ[(fun ω => f (ω 0) * g (ω 0)) | mSI] ω
            - μ[(fun ω => f (ω 0) * μ[(fun ω => g (ω 0)) | mSI] ω) | mSI] ω| ∂μ = 0 := by
    -- The LHS integrand is constant in n (by h_product_const)
    -- The RHS (h_L1_CE) says the same integral → 0
    -- So the constant equals 0
    have h_rewrite : ∀ n,
      ∫ ω, |μ[(fun ω => f (ω 0) * g (ω 0)) | mSI] ω
            - μ[(fun ω => f (ω 0) * μ[(fun ω => g (ω 0)) | mSI] ω) | mSI] ω| ∂μ
      =
      ∫ ω, |μ[(fun ω' => f (ω' 0) * A n ω') | mSI] ω
            - μ[(fun ω' => f (ω' 0) * μ[(fun ω => g (ω 0)) | mSI] ω') | mSI] ω| ∂μ := by
      intro n
      refine integral_congr_ae ?_
      filter_upwards [h_product_const n] with ω hω
      simp [hω]
    -- Constant sequence
    have h_const : Tendsto (fun _ : ℕ =>
      ∫ ω, |μ[(fun ω => f (ω 0) * g (ω 0)) | mSI] ω
            - μ[(fun ω => f (ω 0) * μ[(fun ω => g (ω 0)) | mSI] ω) | mSI] ω| ∂μ)
      atTop
      (𝓝 (∫ ω, |μ[(fun ω => f (ω 0) * g (ω 0)) | mSI] ω
                  - μ[(fun ω => f (ω 0) * μ[(fun ω => g (ω 0)) | mSI] ω) | mSI] ω| ∂μ)) :=
      tendsto_const_nhds
    -- Apply uniqueness: h_const says constant sequence, h_L1_CE says → 0, so constant = 0
    have : (fun n => ∫ ω, |μ[(fun ω => f (ω 0) * g (ω 0)) | mSI] ω
              - μ[(fun ω => f (ω 0) * μ[(fun ω => g (ω 0)) | mSI] ω) | mSI] ω| ∂μ)
         = (fun n => ∫ ω, |μ[(fun ω' => f (ω' 0) * A n ω') | mSI] ω
              - μ[(fun ω' => f (ω' 0) * μ[(fun ω => g (ω 0)) | mSI] ω') | mSI] ω| ∂μ) := by
      funext n
      exact h_rewrite n
    rw [this] at h_const
    exact tendsto_nhds_unique h_const h_L1_CE

  -- turn `∫ |h| = 0` into a.e. equality
  have h_abs_zero :
      (fun ω =>
        |μ[(fun ω => f (ω 0) * g (ω 0)) | mSI] ω
        - μ[(fun ω => f (ω 0) * μ[(fun ω => g (ω 0)) | mSI] ω) | mSI] ω|) =ᵐ[μ] 0 := by
    -- Standard: if ∫|h| = 0 and h ≥ 0 and h integrable, then h = 0 a.e.
    have hint : Integrable (fun ω =>
      |μ[(fun ω => f (ω 0) * g (ω 0)) | mSI] ω
      - μ[(fun ω => f (ω 0) * μ[(fun ω => g (ω 0)) | mSI] ω) | mSI] ω|) μ := by
      apply Integrable.abs
      apply Integrable.sub <;> exact integrable_condExp
    exact integral_eq_zero_iff_of_nonneg_ae (ae_of_all _ (fun _ => abs_nonneg _)) hint |>.mp h_const_is_zero

  -- done: a.e. equality of the two conditional expectations
  filter_upwards [h_abs_zero] with ω hω
  exact sub_eq_zero.mp (abs_eq_zero.mp hω)
-/

/-- **Tower property from index 1** (avoids k=0 lag constancy).

This is the corrected version that proves:
  CE[f·g₁ | mSI] =ᵐ CE[f·CE[g₀|mSI] | mSI]

Key insight: We use Cesàro averages starting from index 1 (A'_n) to avoid the false k=0 case.
The proof structure:
1. CE[A'_n | mSI] = CE[g₀ | mSI] (shift invariance: CE[g_j|mSI] = CE[g₀|mSI])
2. CE[f·A'_n | mSI] = CE[f·g₁ | mSI] for all n (lag constancy with k ≥ 1 only)
3. A'_n → CE[g₀|mSI] in L¹ (MET)
4. CE Lipschitz: CE[f·A'_n] → CE[f·CE[g₀|mSI]]
5. Squeeze: constant sequence converges to 0 -/
private theorem h_tower_of_lagConst_from_one
    {μ : Measure (Ω[α])} [IsProbabilityMeasure μ] [StandardBorelSpace α]
    (hσ : MeasurePreserving shift μ μ)
    (hExch : ∀ π : Equiv.Perm ℕ, Measure.map (Exchangeability.reindex π) μ = μ)
    (f g : α → ℝ)
    (hf_meas : Measurable f) (hf_bd : ∃ Cf, ∀ x, |f x| ≤ Cf)
    (hg_meas : Measurable g) (hg_bd : ∃ Cg, ∀ x, |g x| ≤ Cg) :
    μ[(fun ω => f (ω 0) * g (ω 1)) | shiftInvariantSigma (α := α)]
      =ᵐ[μ]
    μ[(fun ω =>
        f (ω 0) * μ[(fun ω => g (ω 0)) | shiftInvariantSigma (α := α)] ω)
        | shiftInvariantSigma (α := α)] := by
  classical
  have hmSI := shiftInvariantSigma_le (α := α)

  -- Cesàro averages from index 1: A'_n = (1/n) * Σ_{j=1}^n g(ω_j)
  let A' : ℕ → Ω[α] → ℝ := fun n ω =>
    if n = 0 then 0 else (1 / (n : ℝ)) * (Finset.range n).sum (fun j => g (ω (j + 1)))
  set Y : Ω[α] → ℝ := fun ω => μ[(fun ω' => g (ω' 0)) | mSI] ω

  obtain ⟨Cf, hCf⟩ := hf_bd
  obtain ⟨Cg, hCg⟩ := hg_bd

  -- (1) CE[f·A'_n | mSI] = CE[f·g₁ | mSI] for all n ≥ 1
  have h_product_const : ∀ n, 0 < n →
      μ[(fun ω => f (ω 0) * A' n ω) | mSI]
        =ᵐ[μ]
      μ[(fun ω => f (ω 0) * g (ω 1)) | mSI] := by
    intro n hn
    have hA' : A' n = fun ω => (1 / (n : ℝ)) * (Finset.range n).sum (fun j => g (ω (j + 1))) := by
      ext ω
      simp only [A', if_neg (Nat.ne_of_gt hn)]
    rw [show (fun ω => f (ω 0) * A' n ω)
           = (fun ω => f (ω 0) * ((1 / (n : ℝ)) * (Finset.range n).sum (fun j => g (ω (j + 1))))) by
         ext ω; rw [hA']]
    exact product_ce_constant_of_lag_const_from_one hExch f g hf_meas ⟨Cf, hCf⟩ hg_meas ⟨Cg, hCg⟩ n hn

  -- (2) A'_n → Y in L¹ (MET via shift composition)
  -- A'_{n+1}(ω) = (1/(n+1)) * Σ_{j=0}^n g(shift(ω)_j) = A_n(shift(ω))
  -- Since shift preserves μ and A_n → Y in L¹, A'_{n+1} → Y in L¹
  have h_L1_A'_to_Y : Tendsto (fun n =>
      ∫ ω, |A' (n + 1) ω - Y ω| ∂μ) atTop (𝓝 0) := by
    -- A'_{n+1}(ω) = (1/(n+1)) * Σ_{j=0}^n g(ω_{j+1})
    -- But ω_{j+1} = (shift ω)_j, so A'_{n+1}(ω) = A_n(shift ω)
    -- Let A_n(ω) = (1/(n+1)) * Σ_{j=0}^n g(ω_j)
    let A : ℕ → Ω[α] → ℝ := fun n ω =>
      (1 / ((n + 1) : ℝ)) * (Finset.range (n + 1)).sum (fun j => g (ω j))
    -- By L1_cesaro_convergence: A_n → Y in L¹
    have hg_int : Integrable (fun ω => g (ω 0)) μ :=
      integrable_of_bounded_measurable
        (hg_meas.comp (measurable_pi_apply 0)) Cg (fun ω => hCg (ω 0))
    have h_A_to_Y := L1_cesaro_convergence hσ g hg_meas hg_int
    -- A'_{n+1}(ω) = A_n(shift ω)
    have h_eq : ∀ n ω, A' (n + 1) ω = A n (shift ω) := by
      intro n ω
      simp only [A', if_neg (Nat.succ_ne_zero n), A]
      -- LHS: (1/(n+1)) * Σ_{j < n+1} g(ω_{j+1})
      -- RHS: (1/(n+1)) * Σ_{j < n+1} g((shift ω)_j)
      -- These are equal since (shift ω)_j = ω_{j+1}
      simp only [Nat.cast_add, Nat.cast_one, shift_apply]
    -- Change of variables: ∫|A'_{n+1} - Y| = ∫|A_n ∘ shift - Y ∘ shift|
    -- But Y is shift-invariant! So Y ∘ shift =ᵐ Y
    have hY_inv : (fun ω => Y (shift ω)) =ᵐ[μ] Y := by
      -- Y = CE[g(ω_0)|mSI], and CE is mSI-measurable
      -- shift preserves mSI, so Y ∘ shift =ᵃᵉ Y
      -- Use the lemma from InvariantSigma.lean that says:
      -- AEStronglyMeasurable[mSI] f μ → (f ∘ shift =ᵃᵉ f)
      have hY_aesm : AEStronglyMeasurable[mSI] Y μ :=
        stronglyMeasurable_condExp.aestronglyMeasurable
      exact shiftInvariantSigma_aestronglyMeasurable_ae_shift_eq hσ hY_aesm
    -- Now use measure preservation
    have h_mp : ∀ n, ∫ ω, |A n (shift ω) - Y ω| ∂μ = ∫ ω, |A n ω - Y ω| ∂μ := by
      intro n
      have h1 : (fun ω => |A n (shift ω) - Y ω|)
                =ᵐ[μ] (fun ω => |A n (shift ω) - Y (shift ω)|) := by
        filter_upwards [hY_inv] with ω hω
        simp [hω]
      rw [integral_congr_ae h1]
      -- ∫ f ∘ shift dμ = ∫ f dμ by measure preservation
      -- Using integral_map: ∫ h d(μ.map shift) = ∫ (h ∘ shift) dμ
      -- Since hσ.map_eq : μ.map shift = μ, we get ∫ h dμ = ∫ (h ∘ shift) dμ
      have hh_asm : AEStronglyMeasurable (fun ω => |A n ω - Y ω|) μ := by
        have hA_meas : Measurable (A n) := by
          apply Measurable.mul
          · exact measurable_const
          · apply Finset.measurable_sum
            intro j _
            exact hg_meas.comp (measurable_pi_apply j)
        have h_diff : AEStronglyMeasurable (fun ω => A n ω - Y ω) μ :=
          hA_meas.aestronglyMeasurable.sub integrable_condExp.aestronglyMeasurable
        exact continuous_abs.comp_aestronglyMeasurable h_diff
      -- By integral_map: ∫ f d(μ.map g) = ∫ (f ∘ g) dμ (reversed is what we need)
      have hh_asm' : AEStronglyMeasurable (fun ω => |A n ω - Y ω|) (μ.map shift) := by
        rw [hσ.map_eq]; exact hh_asm
      have h_int_map := integral_map hσ.measurable.aemeasurable hh_asm'
      -- Rewrite: ∫ (h ∘ shift) dμ = ∫ h d(μ.map shift) = ∫ h dμ
      rw [h_int_map.symm, hσ.map_eq]
    -- Conclude
    simp_rw [h_eq, h_mp]
    exact h_A_to_Y

  -- (3) CE Lipschitz: CE[f·A'_n] → CE[f·Y]
  have h_L1_CE : Tendsto (fun n =>
      ∫ ω, |μ[(fun ω' => f (ω' 0) * A' (n + 1) ω') | mSI] ω
           - μ[(fun ω' => f (ω' 0) * Y ω') | mSI] ω| ∂μ) atTop (𝓝 0) := by
    -- Use ce_lipschitz_convergence with A' shifted by 1
    have h_int : Integrable (fun ω => g (ω 0)) μ :=
      integrable_of_bounded_measurable (hg_meas.comp (measurable_pi_apply 0)) Cg (fun ω => hCg (ω 0))
    -- A'_{n+1} has the form (1/(n+1)) * Σ_{j=0}^n g(shift ω)_j = A_n(shift ω)
    -- Need to relate to ce_lipschitz_convergence format
    -- ce_lipschitz_convergence needs: A_n defined as (1/(n+1)) * Σ g(ω_j)
    -- We have: A'_{n+1} = A_n ∘ shift
    -- Apply the bound: ∫|CE[f·A'_{n+1}] - CE[f·Y]| ≤ Cf · ∫|A'_{n+1} - Y|
    -- Since A'_{n+1} - Y → 0 in L¹, the conclusion follows
    have h_bd : ∀ n, ∫ ω, |μ[(fun ω' => f (ω' 0) * A' (n + 1) ω') | mSI] ω
                        - μ[(fun ω' => f (ω' 0) * Y ω') | mSI] ω| ∂μ
                  ≤ Cf * ∫ ω, |A' (n + 1) ω - Y ω| ∂μ := by
      intro n
      -- Integrability of f(ω_0) * A'_{n+1}
      have hA'_int : ∀ n, 0 < n → Integrable (A' n) μ := by
        intro m hm
        simp only [A', if_neg (Nat.ne_of_gt hm)]
        have h_sum : Integrable (fun ω => (Finset.range m).sum (fun j => g (ω (j + 1)))) μ :=
          integrable_finset_sum (Finset.range m) (fun j _ =>
            integrable_of_bounded_measurable
              (hg_meas.comp (measurable_pi_apply (j + 1))) Cg (fun ω => hCg (ω (j + 1))))
        exact h_sum.smul (1 / (m : ℝ))
      have hfA_int : Integrable (fun ω => f (ω 0) * A' (n + 1) ω) μ := by
        refine integrable_mul_of_ae_bdd_left ?_ ?_ (hA'_int (n + 1) (Nat.succ_pos n))
        · exact hf_meas.comp (measurable_pi_apply 0)
        · exact ⟨Cf, ae_of_all μ (fun ω => hCf (ω 0))⟩
      have hfY_int : Integrable (fun ω => f (ω 0) * Y ω) μ := by
        refine integrable_mul_of_ae_bdd_left ?_ ?_ integrable_condExp
        · exact hf_meas.comp (measurable_pi_apply 0)
        · exact ⟨Cf, ae_of_all μ (fun ω => hCf (ω 0))⟩
      -- CE Lipschitz
      have h1 : ∫ ω, |μ[(fun ω' => f (ω' 0) * A' (n + 1) ω') | mSI] ω
                    - μ[(fun ω' => f (ω' 0) * Y ω') | mSI] ω| ∂μ
              ≤ ∫ ω, |f (ω 0) * A' (n + 1) ω - f (ω 0) * Y ω| ∂μ :=
        condExp_L1_lipschitz hfA_int hfY_int
      -- Factor bound
      have h2 : ∫ ω, |f (ω 0) * A' (n + 1) ω - f (ω 0) * Y ω| ∂μ
              ≤ Cf * ∫ ω, |A' (n + 1) ω - Y ω| ∂μ := by
        have h_eq : ∀ ω, |f (ω 0) * A' (n + 1) ω - f (ω 0) * Y ω| = |f (ω 0)| * |A' (n + 1) ω - Y ω| := by
          intro ω; rw [← mul_sub, abs_mul]
        have hpt : ∀ᵐ ω ∂μ, |f (ω 0)| * |A' (n + 1) ω - Y ω| ≤ Cf * |A' (n + 1) ω - Y ω| :=
          ae_of_all μ (fun ω => mul_le_mul_of_nonneg_right (hCf (ω 0)) (abs_nonneg _))
        have hdiff_int : Integrable (fun ω => A' (n + 1) ω - Y ω) μ :=
          (hA'_int (n + 1) (Nat.succ_pos n)).sub integrable_condExp
        have hint_lhs : Integrable (fun ω => |f (ω 0)| * |A' (n + 1) ω - Y ω|) μ := by
          have h_asm : AEStronglyMeasurable (fun ω => |f (ω 0)| * |A' (n + 1) ω - Y ω|) μ := by
            apply AEStronglyMeasurable.mul
            · exact (continuous_abs.measurable.comp (hf_meas.comp (measurable_pi_apply 0))).aestronglyMeasurable
            · exact continuous_abs.comp_aestronglyMeasurable hdiff_int.aestronglyMeasurable
          -- Use norm = abs for real numbers, and |a * b| = |a| * |b| for a, b ≥ 0
          have hpt_norm : ∀ᵐ ω ∂μ, ‖|f (ω 0)| * |A' (n + 1) ω - Y ω|‖ ≤ Cf * |A' (n + 1) ω - Y ω| := by
            filter_upwards [hpt] with ω hω
            rw [Real.norm_eq_abs, abs_mul, abs_abs, abs_abs]
            exact hω
          exact Integrable.mono' (hdiff_int.abs.const_mul Cf) h_asm hpt_norm
        have hint_rhs : Integrable (fun ω => Cf * |A' (n + 1) ω - Y ω|) μ :=
          hdiff_int.abs.const_mul Cf
        calc ∫ ω, |f (ω 0) * A' (n + 1) ω - f (ω 0) * Y ω| ∂μ
            = ∫ ω, |f (ω 0)| * |A' (n + 1) ω - Y ω| ∂μ := by congr 1; ext ω; exact h_eq ω
          _ ≤ ∫ ω, Cf * |A' (n + 1) ω - Y ω| ∂μ := integral_mono_ae hint_lhs hint_rhs hpt
          _ = Cf * ∫ ω, |A' (n + 1) ω - Y ω| ∂μ := integral_const_mul Cf _
      exact le_trans h1 h2
    -- Squeeze
    have h_bound_to_zero : Tendsto (fun n =>
        Cf * ∫ ω, |A' (n + 1) ω - Y ω| ∂μ) atTop (𝓝 0) := by
      convert Tendsto.const_mul Cf h_L1_A'_to_Y using 1
      simp
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h_bound_to_zero ?_ ?_
    · exact fun n => integral_nonneg (fun ω => abs_nonneg _)
    · exact h_bd

  -- (4) Squeeze: constant sequence (= CE[f·g₁]) with L¹ limit 0 implies a.e. equality
  have h_const_is_target : ∀ n, 0 < n →
      μ[(fun ω => f (ω 0) * A' n ω) | mSI]
        =ᵐ[μ]
      μ[(fun ω => f (ω 0) * g (ω 1)) | mSI] := h_product_const

  -- The L¹ integral of |CE[f·A'_{n+1}] - CE[f·Y]| → 0
  -- But CE[f·A'_{n+1}] =ᵃᵉ CE[f·g₁] for all n
  -- So the L¹ integral of |CE[f·g₁] - CE[f·Y]| → 0
  -- A constant sequence with limit 0 must be 0 a.e.
  have h_ae_eq : μ[(fun ω => f (ω 0) * g (ω 1)) | mSI]
                   =ᵐ[μ]
                 μ[(fun ω => f (ω 0) * Y ω) | mSI] := by
    -- Show ∫|CE[f·g₁] - CE[f·Y]| = 0
    have h_zero : ∫ ω, |μ[(fun ω' => f (ω' 0) * g (ω' 1)) | mSI] ω
                      - μ[(fun ω' => f (ω' 0) * Y ω') | mSI] ω| ∂μ = 0 := by
      -- The sequence ∫|CE[f·A'_{n+1}] - CE[f·Y]| → 0
      -- But each CE[f·A'_{n+1}] =ᵃᵉ CE[f·g₁]
      -- So ∫|CE[f·g₁] - CE[f·Y]| ≤ ∫|CE[f·A'_{n+1}] - CE[f·Y]| for each n (up to null sets)
      have h_eq_ae : ∀ n, ∫ ω, |μ[(fun ω' => f (ω' 0) * g (ω' 1)) | mSI] ω
                           - μ[(fun ω' => f (ω' 0) * Y ω') | mSI] ω| ∂μ
                       = ∫ ω, |μ[(fun ω' => f (ω' 0) * A' (n + 1) ω') | mSI] ω
                           - μ[(fun ω' => f (ω' 0) * Y ω') | mSI] ω| ∂μ := by
        intro n
        have h := h_const_is_target (n + 1) (Nat.succ_pos n)
        refine integral_congr_ae ?_
        filter_upwards [h] with ω hω
        simp [hω]
      -- The RHS → 0, so for any ε > 0, there exists N such that RHS < ε
      -- Since the LHS = RHS for all n, the LHS ≤ ε for all ε > 0, hence LHS = 0
      have h_le : ∀ ε > 0, ∫ ω, |μ[(fun ω' => f (ω' 0) * g (ω' 1)) | mSI] ω
                              - μ[(fun ω' => f (ω' 0) * Y ω') | mSI] ω| ∂μ < ε := by
        intro ε hε
        rw [Metric.tendsto_atTop] at h_L1_CE
        obtain ⟨N, hN⟩ := h_L1_CE ε hε
        specialize hN N le_rfl
        rw [Real.dist_0_eq_abs, abs_of_nonneg (integral_nonneg (fun _ => abs_nonneg _))] at hN
        rw [h_eq_ae N]
        exact hN
      have h_nonneg : 0 ≤ ∫ ω, |μ[(fun ω' => f (ω' 0) * g (ω' 1)) | mSI] ω
                           - μ[(fun ω' => f (ω' 0) * Y ω') | mSI] ω| ∂μ :=
        integral_nonneg (fun _ => abs_nonneg _)
      -- 0 ≤ x and (∀ ε > 0, x < ε) implies x = 0
      exact le_antisymm (le_of_forall_pos_lt_add (fun ε hε => by linarith [h_le ε hε])) h_nonneg
    -- ∫|X - Y| = 0 implies X =ᵃᵉ Y for integrable X, Y
    have h_int1 : Integrable (μ[(fun ω' => f (ω' 0) * g (ω' 1)) | mSI]) μ := integrable_condExp
    have h_int2 : Integrable (μ[(fun ω' => f (ω' 0) * Y ω') | mSI]) μ := integrable_condExp
    have h_diff_int : Integrable (fun ω => μ[(fun ω' => f (ω' 0) * g (ω' 1)) | mSI] ω
                                         - μ[(fun ω' => f (ω' 0) * Y ω') | mSI] ω) μ :=
      h_int1.sub h_int2
    -- Use integral_eq_zero_iff_of_nonneg_ae: ∫|f| = 0 ↔ f =ᵃᵉ 0 (for nonneg f)
    have h_nonneg : (0 : Ω[α] → ℝ) ≤ᵐ[μ] fun ω => |μ[(fun ω' => f (ω' 0) * g (ω' 1)) | mSI] ω
                                            - μ[(fun ω' => f (ω' 0) * Y ω') | mSI] ω| :=
      ae_of_all μ (fun ω => abs_nonneg _)
    have h_abs_eq_zero : (fun ω => |μ[(fun ω' => f (ω' 0) * g (ω' 1)) | mSI] ω
                                   - μ[(fun ω' => f (ω' 0) * Y ω') | mSI] ω|) =ᵐ[μ] 0 :=
      (integral_eq_zero_iff_of_nonneg_ae h_nonneg h_diff_int.abs).mp h_zero
    -- |X - Y| =ᵃᵉ 0 implies X - Y =ᵃᵉ 0, hence X =ᵃᵉ Y
    filter_upwards [h_abs_eq_zero] with ω hω
    have : μ[(fun ω' => f (ω' 0) * g (ω' 1)) | mSI] ω
         - μ[(fun ω' => f (ω' 0) * Y ω') | mSI] ω = 0 := abs_eq_zero.mp hω
    linarith

  exact h_ae_eq

set_option maxHeartbeats 1000000

/-- **Pair factorization via MET + Exchangeability** (Kallenberg's approach).

For EXCHANGEABLE measures μ on path space, the conditional expectation of f(ω₀)·g(ω₁)
given the shift-invariant σ-algebra factors into the product of the individual
conditional expectations.

**Proof strategy** (CORRECTED - avoids false k=0 lag constancy):
1. Apply tower property directly on g₁ (via Cesàro from index 1):
   CE[f(ω₀)·g(ω₁)|ℐ] = CE[f(ω₀)·CE[g(ω₀)|ℐ]|ℐ]
   (uses h_tower_of_lagConst_from_one which only needs k ≥ 1 lag constancy)
2. Apply pull-out property: CE[f(ω₀)·CE[g(ω₀)|ℐ]|ℐ] = CE[g(ω₀)|ℐ]·CE[f(ω₀)|ℐ]
   (CE[g(ω₀)|ℐ] is ℐ-measurable)

**Key insight**: This requires EXCHANGEABILITY (via `hExch`), not just stationarity.
The original k=0 lag constancy approach was FALSE. See Infrastructure.lean for details.
-/
lemma condexp_pair_factorization_MET
    {μ : Measure (Ω[α])} [IsProbabilityMeasure μ] [StandardBorelSpace α] [Nonempty α]
    (hσ : MeasurePreserving shift μ μ)
    (hExch : ∀ π : Equiv.Perm ℕ, Measure.map (Exchangeability.reindex π) μ = μ)
    (f g : α → ℝ)
    (hf_meas : Measurable f) (hf_bd : ∃ C, ∀ x, |f x| ≤ C)
    (hg_meas : Measurable g) (hg_bd : ∃ C, ∀ x, |g x| ≤ C) :
  μ[(fun ω => f (ω 0) * g (ω 1)) | shiftInvariantSigma (α := α)]
    =ᵐ[μ]
  (fun ω => μ[fun ω => f (ω 0) | shiftInvariantSigma (α := α)] ω
          * μ[fun ω => g (ω 0) | shiftInvariantSigma (α := α)] ω) := by
  -- Note: mSI is already defined as a local notation for shiftInvariantSigma (α := α)
  -- Step 1: Tower property via Cesàro from index 1 (CORRECTED - avoids k=0!)
  -- CE[f(ω₀)·g(ω₁)|ℐ] = CE[f(ω₀)·CE[g(ω₀)|ℐ]|ℐ]
  -- Uses h_tower_of_lagConst_from_one which only requires k ≥ 1 lag constancy
  have h_tower : μ[(fun ω => f (ω 0) * g (ω 1)) | mSI]
      =ᵐ[μ] μ[(fun ω => f (ω 0) * μ[(fun ω => g (ω 0)) | mSI] ω) | mSI] :=
    h_tower_of_lagConst_from_one hσ hExch f g hf_meas hf_bd hg_meas hg_bd

  -- Step 2: Pull-out property (CE[g(ω₀)|ℐ] is ℐ-measurable)
  -- CE[f(ω₀)·CE[g(ω₀)|ℐ]|ℐ] = CE[g(ω₀)|ℐ]·CE[f(ω₀)|ℐ]
  have h_pullout : μ[(fun ω => f (ω 0) * μ[(fun ω => g (ω 0)) | mSI] ω) | mSI]
      =ᵐ[μ] (fun ω => μ[(fun ω => g (ω 0)) | mSI] ω * μ[(fun ω => f (ω 0)) | mSI] ω) := by
    set Z := μ[(fun ω => g (ω 0)) | mSI]
    have hZ_meas : Measurable[mSI] Z := stronglyMeasurable_condExp.measurable
    obtain ⟨Cg, hCg⟩ := hg_bd
    have hZ_bd : ∃ C, ∀ᵐ ω ∂μ, |Z ω| ≤ C := by
      use Cg
      have hg_int : Integrable (fun ω => g (ω 0)) μ := by
        constructor
        · exact (hg_meas.comp (measurable_pi_apply 0)).aestronglyMeasurable
        · exact HasFiniteIntegral.of_bounded (ae_of_all μ (fun ω => hCg (ω 0)))
      have hCg_nn : 0 ≤ Cg := le_trans (abs_nonneg _) (hCg (Classical.choice ‹Nonempty α›))
      have hCg_ae' : ∀ᵐ ω ∂μ, |g (ω 0)| ≤ Cg.toNNReal := by
        filter_upwards with ω
        rw [Real.coe_toNNReal _ hCg_nn]
        exact hCg (ω 0)
      have := ae_bdd_condExp_of_ae_bdd (m := mSI) hCg_ae'
      filter_upwards [this] with ω hω; rwa [Real.coe_toNNReal _ hCg_nn] at hω
    obtain ⟨Cf, hCf⟩ := hf_bd
    have hY_int : Integrable (fun ω => f (ω 0)) μ := by
      constructor
      · exact (hf_meas.comp (measurable_pi_apply 0)).aestronglyMeasurable
      · exact HasFiniteIntegral.of_bounded (ae_of_all μ (fun ω => hCf (ω 0)))
    have h := condExp_mul_pullout hZ_meas hZ_bd hY_int
    calc μ[(fun ω => f (ω 0) * Z ω) | mSI]
        =ᵐ[μ] μ[(fun ω => Z ω * f (ω 0)) | mSI] := by
          have : (fun ω => f (ω 0) * Z ω) = (fun ω => Z ω * f (ω 0)) := by ext ω; ring
          rw [this]
      _ =ᵐ[μ] (fun ω => Z ω * μ[(fun ω => f (ω 0)) | mSI] ω) := h

  -- Combine all steps
  calc μ[(fun ω => f (ω 0) * g (ω 1)) | mSI]
      =ᵐ[μ] μ[(fun ω => f (ω 0) * μ[(fun ω => g (ω 0)) | mSI] ω) | mSI] := h_tower
    _ =ᵐ[μ] (fun ω => μ[(fun ω => g (ω 0)) | mSI] ω * μ[(fun ω => f (ω 0)) | mSI] ω) := h_pullout
    _ =ᵐ[μ] (fun ω => μ[(fun ω => f (ω 0)) | mSI] ω * μ[(fun ω => g (ω 0)) | mSI] ω) := by
        filter_upwards with ω; ring

-- Kernel independence lemmas are in section "Filled proofs of kernel independence lemmas"
-- below, after coord_indicator_via_ν is defined. The lemmas are:
--   kernel_indep_pair_01, kernel_indep_pair, kernel_indep_finset

end OptionB_L1Convergence

end Exchangeability.DeFinetti.ViaKoopman
