# CondExp.lean API Overview

## Quick Reference Card

### When to use this API

Use `Exchangeability.Probability` lemmas when you need:

| Task | Lemma | Import |
|------|-------|--------|
| Prove `(indicator B 1) ∘ X` is integrable | `integrable_indicator_comp` | `Exchangeability.Probability.CondExp` |
| Establish conditional independence | `condIndep_of_indicator_condexp_eq` | `Exchangeability.Probability.CondExp` |
| Transfer CE from distributional equality | `condexp_indicator_eq_of_pair_law_eq` | `Exchangeability.Probability.CondExp` |
| Manage sub-σ-algebra instances | `condExpWith` | `Exchangeability.Probability.CondExp` |
| Show trimmed measures are σ-finite | `sigmaFinite_trim` | `Exchangeability.Probability.CondExp` |

### Examples

#### Before (7 lines)
```lean
have hf_int_raw : Integrable (fun ω => Set.indicator B (fun _ => (1 : ℝ)) (X r ω)) μ := by
  apply Integrable.indicator
  · exact integrable_const (1 : ℝ)
  · exact (hX_meas r) hB
have hf_int : Integrable f μ := by
  simpa [hf_def] using hf_int_raw
```

#### After (1 line)
```lean
have hf_int : Integrable f μ := by
  simpa [hf_def] using Exchangeability.Probability.integrable_indicator_comp (hX_meas r) hB
```

### Full Lemma Signatures

```lean
namespace Exchangeability.Probability

-- Integrability
lemma integrable_indicator_comp
    {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {X : Ω → α} (hX : Measurable X)
    {B : Set α} (hB : MeasurableSet B) :
    Integrable ((Set.indicator B (fun _ => (1 : ℝ))) ∘ X) μ

-- Conditional Independence
lemma condIndep_of_indicator_condexp_eq
    {Ω : Type*} {mΩ : MeasurableSpace Ω} [StandardBorelSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {mF mG mH : MeasurableSpace Ω}
    (hmF : mF ≤ mΩ) (hmG : mG ≤ mΩ) (hmH : mH ≤ mΩ)
    (h : ∀ H, MeasurableSet[mH] H →
      μ[H.indicator (fun _ => (1 : ℝ)) | mF ⊔ mG]
        =ᵐ[μ] μ[H.indicator (fun _ => (1 : ℝ)) | mG]) :
    ProbabilityTheory.CondIndep mG mF mH hmG μ

lemma condExp_indicator_mul_indicator_of_condIndep
    {Ω : Type*} {m₀ : MeasurableSpace Ω} [StandardBorelSpace Ω]
    {m mF mH : MeasurableSpace Ω} {μ : @Measure Ω m₀}
    [IsFiniteMeasure μ]
    (hm  : m  ≤ m₀) (hmF : mF ≤ m₀) (hmH : mH ≤ m₀)
    (hCI : ProbabilityTheory.CondIndep m mF mH hm μ)
    {A B : Set Ω} (hA : MeasurableSet[mF] A) (hB : MeasurableSet[mH] B) :
  μ[(A ∩ B).indicator (fun _ => (1 : ℝ)) | m]
    =ᵐ[μ]
  (μ[A.indicator (fun _ => (1 : ℝ)) | m]
   * μ[B.indicator (fun _ => (1 : ℝ)) | m])

-- Distributional Equality
lemma condexp_indicator_eq_of_pair_law_eq
    {Ω α β : Type*} [mΩ : MeasurableSpace Ω] [MeasurableSpace α] [mβ : MeasurableSpace β]
    {μ : Measure Ω} [IsFiniteMeasure μ]
    (Y Y' : Ω → α) (Z : Ω → β)
    (hY : Measurable Y) (hY' : Measurable Y') (hZ : Measurable Z)
    (hpair : Measure.map (fun ω => (Y ω, Z ω)) μ
           = Measure.map (fun ω => (Y' ω, Z ω)) μ)
    {B : Set α} (hB : MeasurableSet B) :
  μ[(Set.indicator B (fun _ => (1:ℝ))) ∘ Y | MeasurableSpace.comap Z mβ]
    =ᵐ[μ]
  μ[(Set.indicator B (fun _ => (1:ℝ))) ∘ Y' | MeasurableSpace.comap Z mβ]

-- Sub-σ-algebra Infrastructure
noncomputable def condExpWith
    {Ω : Type*} {m₀ : MeasurableSpace Ω}
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (m : MeasurableSpace Ω) (_hm : m ≤ m₀)
    (f : Ω → ℝ) : Ω → ℝ

lemma isFiniteMeasure_trim
    {Ω : Type*} {m₀ : MeasurableSpace Ω}
    (μ : Measure Ω) [IsFiniteMeasure μ]
    {m : MeasurableSpace Ω} (hm : m ≤ m₀) :
    IsFiniteMeasure (μ.trim hm)

lemma sigmaFinite_trim
    {Ω : Type*} {m₀ : MeasurableSpace Ω}
    (μ : Measure Ω) [IsFiniteMeasure μ]
    {m : MeasurableSpace Ω} (hm : m ≤ m₀) :
    SigmaFinite (μ.trim hm)

end Exchangeability.Probability
```

## File Organization

```
Exchangeability/Probability/
├── CondExpBasic.lean    -- Basic utilities
├── CondProb.lean        -- Conditional probability definitions
└── CondExp.lean         -- 🌟 THIS FILE: High-level API for de Finetti proofs

Exchangeability/DeFinetti/
├── ViaMartingale.lean   -- Main consumer (4 uses of integrable_indicator_comp)
├── ViaL2.lean           -- Consumer
├── ViaKoopman.lean      -- Consumer
└── CommonEnding.lean    -- Consumer
```

## Design Principles

**Extract when**:
1. ✅ Appears 3+ times across proof files
2. ✅ Has 5+ lines of boilerplate
3. ✅ Requires careful typeclass management
4. ✅ Encodes reusable probabilistic insight

**Keep in main proofs**:
1. ✅ Domain-specific constructions
2. ✅ Proof-specific calculations
3. ✅ High-level proof architecture

## Recent Updates (Oct 15, 2025)

✅ Enhanced documentation with usage tracking  
✅ Applied `integrable_indicator_comp` to 4 locations in ViaMartingale.lean  
✅ Removed 24 lines of boilerplate  
✅ All builds pass, no new sorries  

See `CONDEXP_REFACTORING_SUMMARY.md` for details.
