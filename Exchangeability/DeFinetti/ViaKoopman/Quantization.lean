/-
Copyright (c) 2025 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

import Mathlib.Tactic

open Filter

/-!
# Dyadic Quantization for Real Numbers

This file provides a quantization function that maps real numbers to a dyadic grid
with specified bounds and precision, along with error bounds and convergence properties.

## Main Definitions

* `MeasureTheory.quantize`: Quantize a real number to a dyadic grid with bounds ±C and precision ε

## Main Results

* `MeasureTheory.quantize_err_le`: The quantization error is bounded by the grid spacing ε
* `MeasureTheory.quantize_abs_le`: Quantized values are bounded by C + 1 when ε ≤ 1
* `MeasureTheory.quantize_tendsto`: Quantization converges pointwise as ε → 0
-/

noncomputable section

namespace MeasureTheory

/-- Quantize a real number to a dyadic grid with bounds ±C and precision ε. -/
def quantize (C ε : ℝ) (x : ℝ) : ℝ :=
  let v := max (-C) (min C x)
  ⌊v / ε⌋ * ε

/-- The quantization error is bounded by the grid spacing. -/
lemma quantize_err_le {C ε x : ℝ} (hε : 0 < ε) :
    |quantize C ε x - max (-C) (min C x)| ≤ ε := by
  unfold quantize
  set v := max (-C) (min C x)
  have h_floor : (⌊v / ε⌋ : ℝ) ≤ v / ε := Int.floor_le (v / ε)
  have h_ceil : v / ε < (⌊v / ε⌋ : ℝ) + 1 := Int.lt_floor_add_one (v / ε)
  have h1 : (⌊v / ε⌋ : ℝ) * ε ≤ v := by
    calc (⌊v / ε⌋ : ℝ) * ε ≤ (v / ε) * ε := by nlinarith [hε]
       _ = v := by field_simp
  have h2 : v < ((⌊v / ε⌋ : ℝ) + 1) * ε := by
    calc v = (v / ε) * ε := by field_simp
       _ < ((⌊v / ε⌋ : ℝ) + 1) * ε := by nlinarith [hε, h_ceil]
  have h3 : v - (⌊v / ε⌋ : ℝ) * ε < ε := by linarith
  rw [abs_sub_le_iff]
  constructor
  · linarith
  · linarith

/-- Quantized values are bounded by C + 1 when ε ≤ 1. -/
lemma quantize_abs_le {C ε x : ℝ} (hC : 0 ≤ C) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    |quantize C ε x| ≤ C + 1 := by
  classical
  set v := max (-C) (min C x) with hv
  -- |v| ≤ C
  have hv_le : |v| ≤ C := abs_le.mpr ⟨by linarith [le_max_left (-C) (min C x)],
    max_le (by linarith) (min_le_left _ _)⟩
  -- Triangle inequality: |q| ≤ |v| + |q - v| ≤ C + ε ≤ C + 1
  have : |quantize C ε x| ≤ |v| + ε :=
    calc |quantize C ε x|
        = |(quantize C ε x - v) + v| := by ring_nf
      _ ≤ |quantize C ε x - v| + |v| := abs_add_le _ _
      _ ≤ ε + |v| := by linarith [quantize_err_le (C := C) (ε := ε) (x := x) hε]
      _ = |v| + ε := by ring
  linarith [hv_le, this, hε1]

/-- Quantization converges pointwise as ε → 0.

Since |quantize C ε x - v| ≤ ε where v = max (-C) (min C x), the quantized value
converges to v as ε → 0+. -/
lemma quantize_tendsto {C x : ℝ} (_hC : 0 ≤ C) :
    Tendsto (fun ε => quantize C ε x) (nhdsWithin 0 (Set.Ioi (0 : ℝ))) (nhds (max (-C) (min C x))) := by
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro δ hδ
  -- For any δ > 0, choose ε_0 = δ. Then for 0 < ε < δ, |quantize - v| ≤ ε < δ.
  use δ, hδ
  intro ε hε_pos hε_dist
  -- hε_pos : ε ∈ Set.Ioi 0, i.e., 0 < ε
  -- hε_dist : dist ε 0 < δ
  rw [Real.dist_eq] at hε_dist ⊢
  simp only [sub_zero] at hε_dist
  calc |quantize C ε x - max (-C) (min C x)|
      ≤ ε := quantize_err_le hε_pos
    _ < δ := by rwa [abs_of_pos hε_pos] at hε_dist

end MeasureTheory
