/-
Copyright (c) 2025 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Exchangeability.DeFinetti.ViaKoopman.Infrastructure
import Exchangeability.DeFinetti.ViaKoopman.CesaroHelpers
import Exchangeability.DeFinetti.ViaKoopman.CylinderFunctions
import Exchangeability.DeFinetti.ViaKoopman.KoopmanCommutation

/-! # L² to L¹ Cesàro Convergence Helpers

This file contains helper lemmas for L² to L¹ Cesàro convergence:
- `condexpL2_ae_eq_condExp` - connects L² conditional expectation to classical CE
- `optionB_Step3b_L2_to_L1` - L² convergence implies L¹ convergence
- `optionB_Step4b_AB_close` - A_n and B_n differ negligibly
- `optionB_Step4c_triangle` - triangle inequality combining convergences
- `optionB_L1_convergence_bounded` - bounded case convergence implementation

This is part of "Option B" from the proof plan, avoiding the projected MET approach.
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


section OptionB_L2ToL1

variable {μ : Measure (Ω[α])} [IsProbabilityMeasure μ] [StandardBorelSpace α]

-- Helper lemmas for Step 3b: connecting condexpL2 to condExp

omit [StandardBorelSpace α] in
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

omit [IsProbabilityMeasure μ] [StandardBorelSpace α] in
/-- Pull a.e. equality back along a measure-preserving map.
    Standard fact: if f =ᵐ g and T preserves μ, then f ∘ T =ᵐ g ∘ T.
    Proof: Use QuasiMeasurePreserving.ae_eq_comp from mathlib. -/
lemma eventuallyEq_comp_measurePreserving {f g : Ω[α] → ℝ}
    (hT : MeasurePreserving shift μ μ) (hfg : f =ᵐ[μ] g) :
    (f ∘ shift) =ᵐ[μ] (g ∘ shift) :=
  hT.quasiMeasurePreserving.ae_eq_comp hfg

omit [MeasurableSpace α] [StandardBorelSpace α] in
/-- General evaluation formula for shift iteration. File-private — only caller
is `iterate_shift_eval0'` directly below. -/
private lemma iterate_shift_eval' (k n : ℕ) (ω : Ω[α]) :
    (shift^[k] ω) n = ω (k + n) := by
  induction k generalizing n with
  | zero => simp
  | succ k ih =>
      rw [Function.iterate_succ']
      simp only [shift_apply, Function.comp_apply]
      rw [ih]
      ac_rfl

omit [MeasurableSpace α] [StandardBorelSpace α] in
/-- Evaluate the k-th shift at 0: shift^[k] ω 0 = ω k. File-private — only
in-file caller. -/
private lemma iterate_shift_eval0' (k : ℕ) (ω : Ω[α]) :
    (shift^[k] ω) 0 = ω k := by
  rw [iterate_shift_eval']
  simp

/-! ### Option B Helper Lemmas

These lemmas extract Steps 4a-4c from the main theorem to reduce elaboration complexity.
Each lemma is self-contained with ~50-80 lines, well below timeout thresholds. -/

omit [StandardBorelSpace α] in
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
      simp [h1, h2]

    -- measurability: both birkhoffAverage and condexpL2 are Lp elements, so AEMeasurable when coerced
    have h_meas :
        AEMeasurable
          (fun ω =>
            birkhoffAverage ℝ (koopman shift hσ) (fun f => f) n fL2 ω
            - condexpL2 (μ := μ) fL2 ω) μ :=
      AEMeasurable.sub (Lp.aestronglyMeasurable _).aemeasurable
        (Lp.aestronglyMeasurable _).aemeasurable

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
    Eventually.of_forall (fun _ => integral_nonneg (fun _ => abs_nonneg _))

  -- Step 4: squeeze between 0 and the L²-norm difference (which → 0)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds hL2_norm h_lower_ev h_upper_ev

omit [StandardBorelSpace α] in
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
          ext k; simp [Finset.mem_range]; omega,
        Finset.sum_union (by simp : Disjoint (Finset.range n) {n}),
        Finset.sum_singleton]
    -- Now A n ω = (1/(n+1)) * (∑_{k<n} g(ω k) + g(ω n))
    -- Let S = ∑_{k<n} g(ω k)
    set S := (Finset.range n).sum fun j => g (ω j)
    -- A n ω - B n ω = S/(n+1) + g(ω n)/(n+1) - S/n
    --               = -S/(n(n+1)) + g(ω n)/(n+1)
    calc |1 / (↑n + 1) * (S + g (ω n)) - 1 / ↑n * S|
        = |S / (↑n + 1) + g (ω n) / (↑n + 1) - S / ↑n| := by ring_nf
      _ = |-S / (↑n * (↑n + 1)) + g (ω n) / (↑n + 1)| := by field_simp; ring_nf
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
            _ ≤ (Finset.range n).sum (fun j => Cg) :=
                Finset.sum_le_sum fun j _ => hCg_bd (ω j)
            _ = n * Cg := by rw [Finset.sum_const, Finset.card_range]; ring
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
  have h_lower : ∀ n, 0 ≤ ∫ ω, |A n ω - B n ω| ∂μ :=
    fun n => integral_nonneg fun ω => abs_nonneg _

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

omit [StandardBorelSpace α] in
/-- **Step 4c helper**: Triangle inequality to combine convergences.

Given ∫|B_n - Y| → 0 and ∫|A_n - B_n| → 0, proves ∫|A_n - Y| → 0 via squeeze theorem. -/
private lemma optionB_Step4c_triangle
    {μ : Measure (Ω[α])} [IsProbabilityMeasure μ]
    (g : α → ℝ) (hg_meas : Measurable g) (hg_bd : ∃ Cg, ∀ x, |g x| ≤ Cg)
    (A B : ℕ → Ω[α] → ℝ) (Y : Ω[α] → ℝ) (G : Ω[α] → ℝ)
    (hA_def : A = fun n ω => 1 / (↑n + 1) * (Finset.range (n + 1)).sum (fun j => g (ω j)))
    (hB_def : B = fun n ω => if n = 0 then 0 else 1 / ↑n * (Finset.range n).sum (fun j => g (ω j)))
    (_hG_int : Integrable G μ)
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
          have hsum : |Finset.sum (Finset.range n) (fun j => g (ω j))| ≤ (n : ℝ) * Cg :=
            calc |Finset.sum (Finset.range n) (fun j => g (ω j))|
                ≤ Finset.sum (Finset.range n) (fun j => |g (ω j)|) := Finset.abs_sum_le_sum_abs _ _
              _ ≤ Finset.sum (Finset.range n) (fun j => Cg) := by gcongr with j _; exact hCg _
              _ = (n : ℝ) * Cg := by simp
          calc (n : ℝ)⁻¹ * |Finset.sum (Finset.range n) (fun j => g (ω j))|
            _ ≤ (n : ℝ)⁻¹ * ((n : ℝ) * Cg) := by gcongr
            _ = Cg := by field_simp
        -- Bounded + Measurable → Integrable on finite measure space
        have hB_meas : Measurable (B n) := by
          rw [hB_def]
          simp [hn]
          fun_prop
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
              |A n ω - B n ω| + |B n ω - Y ω| := fun ω => abs_add_le _ _
    -- rewrite the LHS inside the absolute value
    have hre : (fun ω => |A n ω - Y ω|) =
               (fun ω => |(A n ω - B n ω) + (B n ω - Y ω)|) := funext fun _ => by ring_nf
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
            have hsum : |Finset.sum (Finset.range (n + 1)) (fun j => g (ω j))| ≤ ((n : ℝ) + 1) * Cg :=
              calc |Finset.sum (Finset.range (n + 1)) (fun j => g (ω j))|
                  ≤ Finset.sum (Finset.range (n + 1)) (fun j => |g (ω j)|) := Finset.abs_sum_le_sum_abs _ _
                _ ≤ Finset.sum (Finset.range (n + 1)) (fun j => Cg) := by gcongr with j _; exact hCg _
                _ = ((n : ℝ) + 1) * Cg := by simp
            have : |((n : ℝ) + 1)|⁻¹ = ((n : ℝ) + 1)⁻¹ := by rw [abs_of_nonneg]; positivity
            calc |((n : ℝ) + 1)|⁻¹ * |Finset.sum (Finset.range (n + 1)) (fun j => g (ω j))|
              _ = ((n : ℝ) + 1)⁻¹ * |Finset.sum (Finset.range (n + 1)) (fun j => g (ω j))| := by rw [this]
              _ ≤ ((n : ℝ) + 1)⁻¹ * (((n : ℝ) + 1) * Cg) := by gcongr
              _ = Cg := by field_simp
          have hB_bd : |B n ω| ≤ Cg := by
            rw [hB_def]
            simp [hn]
            have hsum : |Finset.sum (Finset.range n) (fun j => g (ω j))| ≤ (n : ℝ) * Cg :=
              calc |Finset.sum (Finset.range n) (fun j => g (ω j))|
                  ≤ Finset.sum (Finset.range n) (fun j => |g (ω j)|) := Finset.abs_sum_le_sum_abs _ _
                _ ≤ Finset.sum (Finset.range n) (fun j => Cg) := by gcongr with j _; exact hCg _
                _ = (n : ℝ) * Cg := by simp
            calc (n : ℝ)⁻¹ * |Finset.sum (Finset.range n) (fun j => g (ω j))|
              _ ≤ (n : ℝ)⁻¹ * ((n : ℝ) * Cg) := by gcongr
              _ = Cg := by field_simp
          calc |A n ω - B n ω|
              ≤ |A n ω| + |B n ω| := abs_sub _ _
            _ ≤ Cg + Cg := by gcongr
            _ = 2 * Cg := by ring
      have hA_meas : Measurable (A n) := by rw [hA_def]; simp; fun_prop
      have hB_meas : Measurable (B n) := by
        rw [hB_def]
        by_cases hn : n = 0
        · simp [hn]
        · simp [hn]
          fun_prop
      have hAB_bd_ae : ∀ᵐ ω ∂μ, ‖|A n ω - B n ω|‖ ≤ 2 * Cg :=
        ae_of_all μ (fun ω => by simp [Real.norm_eq_abs]; exact hAB_bd ω)
      exact ⟨(hA_meas.sub hB_meas).norm.aestronglyMeasurable, HasFiniteIntegral.of_bounded hAB_bd_ae⟩
    have hint2 : Integrable (fun ω => |B n ω - Y ω|) μ := hBY_abs_integrable n
    -- now integrate the pointwise inequality
    calc
      ∫ ω, |A n ω - Y ω| ∂μ
          = ∫ ω, |(A n ω - B n ω) + (B n ω - Y ω)| ∂μ := by simp [hre]
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
          simp [abs_of_nonneg this]
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

omit [StandardBorelSpace α] in
/-- **Option B bounded case implementation**: L¹ convergence for bounded functions.

For a bounded measurable function g : α → ℝ, the Cesàro averages A_n(ω) = (1/(n+1)) ∑_j g(ω j)
converge in L¹ to CE[g(ω₀) | mSI]. Uses the fact that g(ω 0) is a cylinder function. -/
theorem optionB_L1_convergence_bounded
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
      have hk_pres := hσ.iterate k
      -- Pull hfL2_eq back along shift^[k] using measure-preserving property
      have hpull : (fun ω => (fL2 : Ω[α] → ℝ) (shift^[k] ω)) =ᵐ[μ]
          (fun ω => G (shift^[k] ω)) := by
        exact hk_pres.quasiMeasurePreserving.ae_eq_comp hfL2_eq
      -- Now use iterate_shift_eval0': shift^[k] ω 0 = ω k
      have heval : (fun ω => G (shift^[k] ω)) =ᵐ[μ] (fun ω => g (ω k)) :=
        ae_of_all _ fun ω => congr_arg g (iterate_shift_eval0' k ω)
      exact hpull.trans heval

    -- Pass 3: Combine summands and unfold birkhoffAverage
    have hterms : ∀ k, (fun ω => ((koopman shift hσ)^[k] fL2) ω) =ᵐ[μ]
        (fun ω => g (ω k)) := fun k => (h1_k k).trans (h2_k k)

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

end OptionB_L2ToL1

end Exchangeability.DeFinetti.ViaKoopman
