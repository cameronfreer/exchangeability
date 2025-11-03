# Upcrossing Proof Reconstruction Notes

## Summary from Previous Session

The work on `Exchangeability/Probability/Martingale.lean` had nearly completed the main upcrossing sorry with the following structure:

### Completed: h_bound (lines 176-211)

Key techniques used:
- `abs_sub _ _`: For |x - a| ≤ |x| + |a|
- `ENNReal.ofReal_add`: To split sums
- `lintegral_add_right _ measurable_const`: For integral manipulation
- `eLpNorm_one_eq_lintegral_enorm`: Converting between eLpNorm and lintegral
- `Real.enorm_eq_ofReal_abs`: Conversion from ofReal to enorm
- `memLp_one_iff_integrable.mpr` and `MemLp.eLpNorm_ne_top`: For finiteness

### Main Upcrossing Proof Structure (lines 309-364)

The proof was restructured to use explicit intermediate results instead of a single calc chain:

```lean
have h_integral_finite : ∫⁻ ω, upcrossings (↑a) (↑b) (fun n => μ[f | 𝔽 n]) ω ∂μ < ⊤ := by
  have eq1 : ∫⁻ ω, upcrossings (↑a) (↑b) (fun n => μ[f | 𝔽 n]) ω ∂μ
             = ∫⁻ ω, (⨆ N, (upcrossingsBefore (↑a) (↑b) (fun n => μ[f | 𝔽 n]) N ω : ℝ≥0∞)) ∂μ := by
    simp only [MeasureTheory.upcrossings]

  have eq2 : ∫⁻ ω, (⨆ N, (upcrossingsBefore (↑a) (↑b) (fun n => μ[f | 𝔽 n]) N ω : ℝ≥0∞)) ∂μ
             = ⨆ N, ∫⁻ ω, (upcrossingsBefore (↑a) (↑b) (fun n => μ[f | 𝔽 n]) N ω : ℝ≥0∞) ∂μ := by
    apply lintegral_iSup'
    · intro N
      let ℱ : Filtration ℕ (inferInstance : MeasurableSpace Ω) := {
        seq := fun _ => (inferInstance : MeasurableSpace Ω)
        mono' := fun _ _ _ => le_refl _
        le' := fun _ => le_refl _
      }
      have : Adapted ℱ (fun n => μ[f | 𝔽 n]) := fun n => stronglyMeasurable_condExp.mono (h_le n)
      exact (measurable_coe_nnreal_ennreal.comp (this.measurable_upcrossingsBefore hab')).aemeasurable
    · apply ae_of_all; intro ω N M hNM
      exact ENNReal.coe_le_coe.2 (upcrossingsBefore_mono _ _ hNM)

  have le1 : ⨆ N, ∫⁻ ω, (upcrossingsBefore (↑a) (↑b) (fun n => μ[f | 𝔽 n]) N ω : ℝ≥0∞) ∂μ ≤ C := by
    apply iSup_le; intro N
    calc ∫⁻ ω, (upcrossingsBefore (↑a) (↑b) (fun n => μ[f | 𝔽 n]) N ω : ℝ≥0∞) ∂μ
        ≤ ∫⁻ ω, upcrossings (↑a) (↑b) (fun n => revCEFinite (μ := μ) f 𝔽 N n) ω ∂μ := by
            apply lintegral_mono; intro ω
            sorry  -- LINE 341: Final remaining sorry
      _ ≤ C := hC N

  have le2 : C < ⊤ := by
    have h_pos : 0 < b - (a : ℝ) := by
      rw [sub_pos]
      exact Rat.cast_lt.2 hab
    refine ENNReal.div_lt_top ?_ ?_
    · refine ENNReal.add_lt_top.2 ⟨?_, ENNReal.ofReal_lt_top⟩
      rw [ENNReal.ofReal_toReal]
      · exact (memLp_one_iff_integrable.mpr hf).eLpNorm_lt_top
      · exact (memLp_one_iff_integrable.mpr hf).eLpNorm_ne_top
    · exact (ENNReal.ofReal_pos.2 h_pos).ne'

  rw [eq1, eq2]
  exact lt_of_le_of_lt le1 le2
```

### Measurability Proof (lines 368-379)

```lean
apply ae_lt_top
· let ℱ : Filtration ℕ (inferInstance : MeasurableSpace Ω) := {
    seq := fun _ => (inferInstance : MeasurableSpace Ω)
    mono' := fun _ _ _ => le_refl _
    le' := fun _ => le_refl _
  }
  have h_adapted : Adapted ℱ (fun n => μ[f | 𝔽 n]) := by
    intro n
    exact stronglyMeasurable_condExp.mono (h_le n)
  exact h_adapted.measurable_upcrossings hab'
exact h_integral_finite.ne
```

## Final Remaining Sorry (Line 341)

The last technical detail is proving:
```lean
(upcrossingsBefore (↑a) (↑b) (fun n => μ[f | 𝔽 n]) N ω : ℝ≥0∞)
  ≤ upcrossings (↑a) (↑b) (fun n => revCEFinite (μ := μ) f 𝔽 N n) ω
```

### Key Insight

Since `revCEFinite f 𝔽 N n = μ[f | 𝔽 (N-n)]`, the reversed sequence at horizon N contains exactly the values `μ[f | 𝔽 k]` for k ∈ {0,...,N}, just in reverse order.

Since `upcrossings = ⨆ M, upcrossingsBefore M`, we can use:
```lean
upcrossingsBefore (original, N) ≤ upcrossings (reversed) = ⨆ M, upcrossingsBefore (reversed, M)
```

And apply `le_iSup` at index N:
```lean
simp only [MeasureTheory.upcrossings]
exact le_iSup (fun M => (upcrossingsBefore (↑a) (↑b) (fun n => revCEFinite (μ := μ) f 𝔽 N n) M ω : ℝ≥0∞)) N
```

## Why This Works

Even though the reversed sequence might have fewer upcrossings than the original at index N specifically, the supremum over all indices M captures all possible upcrossings, which must include at least those seen in any finite prefix of length N.

The reversed sequence evaluates the same conditional expectations, just in different order, so the upcrossing count over the full reversed sequence (the supremum) bounds the upcrossing count in the original sequence up to any finite time.
