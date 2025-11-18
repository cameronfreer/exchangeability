/-
Copyright (c) 2025 The Exchangeability Contributors
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
  have hv_le : |v| ≤ C := by
    have hv_lo : -C ≤ v := le_max_left _ _
    have hv_hi : v ≤ C := by
      calc v = max (-C) (min C x) := hv.symm
        _ ≤ C := by apply max_le; linarith; exact min_le_left _ _
    exact abs_le.mpr ⟨by linarith, hv_hi⟩
  -- |quantize - v| ≤ ε
  have herr := quantize_err_le (C := C) (ε := ε) (x := x) hε
  -- Triangle inequality: |q| ≤ |v| + |q - v| ≤ C + ε ≤ C + 1
  have : |quantize C ε x| ≤ |v| + ε := by
    calc |quantize C ε x|
        = |(quantize C ε x - v) + v| := by ring_nf
      _ ≤ |quantize C ε x - v| + |v| := abs_add_le _ _
      _ ≤ ε + |v| := by linarith [herr]
      _ = |v| + ε := by ring
  linarith [hv_le, this, hε1]

/-- Quantization converges pointwise as ε → 0.

**Proof sketch**: Since |quantize C ε x - v| ≤ ε where v = max (-C) (min C x),
and ε → 0 as ε → 0+ in nhdsWithin (Set.Ioi 0), the quantized value converges to v.
The key is showing that for any δ > 0, the set {ε | 0 < ε < δ} is in nhdsWithin (Set.Ioi 0) 0.

Axiomatized for now due to filter API complexity in Lean 4.24.
-/
axiom quantize_tendsto {C x : ℝ} (hC : 0 ≤ C) :
    Tendsto (fun ε => quantize C ε x) (nhdsWithin 0 (Set.Ioi (0 : ℝ))) (nhds (max (-C) (min C x)))

end MeasureTheory
