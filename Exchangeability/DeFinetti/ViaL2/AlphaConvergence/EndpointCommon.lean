/-
Copyright (c) 2025 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Exchangeability.DeFinetti.ViaL2.AlphaIicCE

/-!
# Shared helper for the `alphaIicCE` endpoint limits

Both `alphaIicCE_ae_tendsto_zero_atBot` (`EndpointAtBot`) and
`alphaIicCE_ae_tendsto_one_atTop` (`EndpointAtTop`) need the same generic
measure-theoretic fact:

If a uniformly bounded sequence `f : ℕ → Ω → ℝ` converges pointwise a.e. (to
some `L`) and also converges to a *constant* `c` in L¹, then the pointwise
limit equals `c` a.e., so `f n ω → c` a.e.

This is the "L¹-limit-of-a-constant-identifies-the-pointwise-limit" lemma,
extracted into one private helper so the endpoint files can each derive
pointwise convergence to their target without duplicating the
dominated-convergence + `integral_eq_zero_iff_of_nonneg_ae` machinery.
-/

noncomputable section

namespace Exchangeability.DeFinetti.ViaL2

open MeasureTheory Filter Topology

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **A.e. pointwise limit equals the L¹-limit constant.**

If a uniformly bounded sequence `f : ℕ → Ω → ℝ` converges pointwise a.e. to
`L : Ω → ℝ` and also converges to a constant `c` in L¹ (in the sense that
`∫ |f n - c| → 0`), then `L = c` a.e., so `f n ω → c` for a.e. `ω`.

The proof routes through dominated convergence: `|f n - c|` is uniformly
bounded by `C + |c|`, converges pointwise a.e. to `|L - c|`, and has integrals
tending to `0`, so `∫ |L - c| = 0`. Since `|L - c| ≥ 0`, that forces `L = c`
a.e. -/
lemma ae_tendsto_const_of_ae_convergent_of_L1_const
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {f : ℕ → Ω → ℝ} {L : Ω → ℝ} {c C : ℝ}
    (hf_meas : ∀ n, AEStronglyMeasurable (f n) μ)
    (hf_bound : ∀ n, ∀ᵐ ω ∂μ, ‖f n ω‖ ≤ C)
    (hf_ae : ∀ᵐ ω ∂μ, Tendsto (fun n => f n ω) atTop (𝓝 (L ω)))
    (hf_L1 : Tendsto (fun n => ∫ ω, |f n ω - c| ∂μ) atTop (𝓝 0)) :
    ∀ᵐ ω ∂μ, Tendsto (fun n => f n ω) atTop (𝓝 c) := by
  -- |f n - c| is AEStronglyMeasurable, uniformly bounded by C + |c|, and
  -- pointwise a.e. → |L - c|.  On ℝ, `|·| = ‖·‖`, so we use `.norm` plus a
  -- `funext` rewrite.
  have h_const_meas : AEStronglyMeasurable (fun _ : Ω => c) μ := aestronglyMeasurable_const
  have h_abs_meas : ∀ n, AEStronglyMeasurable (fun ω => |f n ω - c|) μ := by
    intro n
    have h_eq : (fun ω => |f n ω - c|) = (fun ω => ‖f n ω - c‖) := by
      funext ω; exact (Real.norm_eq_abs _).symm
    rw [h_eq]
    exact ((hf_meas n).sub h_const_meas).norm
  have h_pointwise_bound : ∀ (x : ℝ), ‖x‖ ≤ C → |x - c| ≤ C + |c| := fun x hx => by
    have hx' : |x| ≤ C := by rwa [← Real.norm_eq_abs]
    linarith [abs_sub x c, abs_nonneg x, abs_nonneg c]
  have h_abs_bound : ∀ n, ∀ᵐ ω ∂μ, ‖|f n ω - c|‖ ≤ C + |c| := by
    intro n
    filter_upwards [hf_bound n] with ω hω
    rw [Real.norm_eq_abs, abs_abs]
    exact h_pointwise_bound _ hω
  have h_abs_conv : ∀ᵐ ω ∂μ,
      Tendsto (fun n => |f n ω - c|) atTop (𝓝 (|L ω - c|)) := by
    filter_upwards [hf_ae] with ω hω
    exact (hω.sub tendsto_const_nhds).abs
  -- DCT gives ∫ |f n - c| → ∫ |L - c|; combined with hf_L1 this forces
  -- ∫ |L - c| = 0.
  have h_DCT :=
    tendsto_integral_of_dominated_convergence (fun _ : Ω => C + |c|)
      h_abs_meas (integrable_const (C + |c|)) h_abs_bound h_abs_conv
  have h_int_zero : ∫ ω, |L ω - c| ∂μ = 0 := tendsto_nhds_unique h_DCT hf_L1
  -- L is AEStronglyMeasurable (a.e. limit of AEStronglyMeasurable functions);
  -- |L - c| is integrable (bounded by C + |c|) and nonneg, so the integral
  -- being zero forces |L - c| = 0 a.e., i.e. L = c a.e.
  have hL_meas : AEStronglyMeasurable L μ :=
    aestronglyMeasurable_of_tendsto_ae atTop hf_meas hf_ae
  have h_abs_diff_meas : AEStronglyMeasurable (fun ω => |L ω - c|) μ := by
    have h_eq : (fun ω => |L ω - c|) = (fun ω => ‖L ω - c‖) := by
      funext ω; exact (Real.norm_eq_abs _).symm
    rw [h_eq]
    exact (hL_meas.sub h_const_meas).norm
  have h_L_bound : ∀ᵐ ω ∂μ, ‖L ω‖ ≤ C := by
    -- L is the a.e. limit of f, and each |f n| ≤ C a.e., so |L| ≤ C a.e.
    have h_bound_all : ∀ᵐ ω ∂μ, ∀ n, ‖f n ω‖ ≤ C := ae_all_iff.mpr hf_bound
    filter_upwards [hf_ae, h_bound_all] with ω h_ae_ω h_bound_ω
    exact le_of_tendsto h_ae_ω.norm (Filter.Eventually.of_forall h_bound_ω)
  have h_abs_diff_bound : ∀ᵐ ω ∂μ, ‖|L ω - c|‖ ≤ C + |c| := by
    filter_upwards [h_L_bound] with ω hω
    rw [Real.norm_eq_abs, abs_abs]
    exact h_pointwise_bound _ hω
  have h_abs_diff_int : Integrable (fun ω => |L ω - c|) μ :=
    Integrable.of_bound h_abs_diff_meas (C + |c|) h_abs_diff_bound
  have h_abs_nonneg : (0 : Ω → ℝ) ≤ᵐ[μ] (fun ω => |L ω - c|) :=
    ae_of_all _ (fun _ => abs_nonneg _)
  have h_abs_zero : (fun ω => |L ω - c|) =ᵐ[μ] 0 := by
    rw [← integral_eq_zero_iff_of_nonneg_ae h_abs_nonneg h_abs_diff_int]
    exact h_int_zero
  -- Combine: hf_ae gives Tendsto _ (𝓝 (L ω)); h_abs_zero gives L ω = c a.e.
  filter_upwards [hf_ae, h_abs_zero] with ω h_ae h_eq
  have : L ω = c := sub_eq_zero.mp (abs_eq_zero.mp h_eq)
  simpa [this] using h_ae

end Exchangeability.DeFinetti.ViaL2
