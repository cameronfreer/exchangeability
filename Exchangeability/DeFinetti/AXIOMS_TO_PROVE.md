# Axioms Needed for h_tower_of_lagConst

Here are the exact axiom statements needed to complete the h_tower proof. All are standard properties that should be in mathlib or easily provable.

## Axiom 1: Conditional Expectation - Scalar Multiplication

**Location**: Lines 1013, 1115 (Blocks 1 & 2)

```lean
/-- Conditional expectation commutes with scalar multiplication. -/
axiom condExp_const_mul
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {m : MeasurableSpace Ω} (hm : m ≤ mΩ)
    (c : ℝ) (f : Ω → ℝ) :
    μ[(fun ω => c * f ω) | m] =ᵐ[μ] (fun ω => c * μ[f | m] ω)
```

**What it says**: CE[c·f|m] = c·CE[f|m]

**Why standard**: This is linearity of conditional expectation (scalar part)

**Usage in proof**:
- Block 1: Pull `1/(n+1)` out of CE when computing CE[A_n|m]
- Block 2: Pull `1/(n+1)` out of CE when computing CE[f·A_n|m]

---

## Axiom 2: Conditional Expectation - Finite Sum

**Location**: Lines 1024, 1127 (Blocks 1 & 2)

```lean
/-- Conditional expectation commutes with finite sums. -/
axiom condExp_sum_finset
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {m : MeasurableSpace Ω} (hm : m ≤ mΩ)
    {ι : Type*} (s : Finset ι) (f : ι → Ω → ℝ) :
    μ[(fun ω => s.sum (fun i => f i ω)) | m]
      =ᵐ[μ] (fun ω => s.sum (fun i => μ[f i | m] ω))
```

**What it says**: CE[Σᵢ fᵢ|m] = Σᵢ CE[fᵢ|m]

**Why standard**: This is linearity of conditional expectation (sum part)

**Usage in proof**:
- Block 1: Push CE through `Σⱼ₌₀ⁿ g(ωⱼ)` to get `Σⱼ₌₀ⁿ CE[g(ωⱼ)|m]`
- Block 2: Push CE through `Σⱼ₌₀ⁿ f(ω₀)·g(ωⱼ)` to get `Σⱼ₌₀ⁿ CE[f(ω₀)·g(ωⱼ)|m]`

---

## Axiom 3: Integrable from Bounded + Measurable

**Location**: Line 1033 (Block 1)

```lean
/-- Bounded measurable functions are integrable on finite measure spaces. -/
axiom integrable_of_bounded_measurable
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {f : Ω → ℝ} (hf_meas : Measurable f) (C : ℝ) (hf_bd : ∀ ω, |f ω| ≤ C) :
    Integrable f μ
```

**What it says**: Bounded + measurable + finite measure ⇒ integrable

**Why standard**: This is a fundamental fact in measure theory

**Usage in proof**:
- Needed to show `(fun ω => g (ω j))` is integrable
- Required to apply `condexp_precomp_iterate_eq`
- Context: `g : α → ℝ` is measurable and `∃ Cg, ∀ x, |g x| ≤ Cg`

**Specific application**:
```lean
have hg_j_int : Integrable (fun ω => g (ω j)) μ := by
  obtain ⟨Cg, hCg⟩ := hg_bd
  exact integrable_of_bounded_measurable
    (hg_meas.comp (measurable_pi_apply j))  -- g ∘ πⱼ is measurable
    Cg                                       -- bound
    (fun ω => hCg (ω j))                    -- |g(ωⱼ)| ≤ Cg
```

---

## Axiom 4: Mean Ergodic Theorem (Function Level)

**Location**: Line 1217 (Block 3)

```lean
/-- Cesàro averages of a shift-invariant function converge to conditional
expectation in L². This is the function-level version of the Mean Ergodic Theorem. -/
axiom birkhoffAverage_tendsto_condexp_L2
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (T : Ω → Ω) (hT_meas : Measurable T) (hT_pres : MeasurePreserving T μ μ)
    {m : MeasurableSpace Ω} (hm : m ≤ _)
    (h_inv : ∀ s, MeasurableSet[m] s → T ⁻¹' s = s)
    (f : Ω → ℝ) (hf_int : Integrable f μ) :
    Tendsto (fun n =>
      MeasureTheory.snorm
        (fun ω => (1 / (n + 1 : ℝ)) * (Finset.range (n + 1)).sum (fun j => f (T^[j] ω))
                  - μ[f | m] ω)
        2 μ)
      atTop (𝓝 0)
```

**What it says**: Cesàro averages `Aₙ(f) = (1/(n+1)) Σⱼ₌₀ⁿ f(Tʲω)` converge to `CE[f|I]` in L² norm, where `I` is the T-invariant σ-algebra

**Why needed**: This is the core of the Mean Ergodic Theorem approach

**Usage in proof**:
- Applied with `T = shift`, `f = (fun ω => g (ω 0))`, `m = shiftInvariantSigma`
- Shows `A_n → CE[g(ω₀)|m]` in L², which is Block 3 step 1

**Note**: Mathlib likely has this at the Lp level. May need to bridge from `Lp 2` to function-level.

---

## Axiom 5: Hölder Inequality (L¹ ≤ L² on probability spaces)

**Location**: Line 1223 (Block 3)

```lean
/-- On probability spaces, the L¹ norm is bounded by the L² norm. -/
axiom snorm_one_le_snorm_two_toReal
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (f : Ω → ℝ) :
    (∫ ω, |f ω| ∂μ) ≤ (MeasureTheory.snorm f 2 μ).toReal
```

**What it says**: ‖f‖₁ ≤ ‖f‖₂ when μ is a probability measure

**Why standard**: This is Hölder inequality for p=1, q=2 on probability spaces

**Usage in proof**:
- Bound L¹ convergence by L² convergence: `∫|A_n - Y| ≤ ‖A_n - Y‖₂`
- Combined with Axiom 4 and squeeze theorem to get L¹ convergence

**Note**: This should be in mathlib as `MeasureTheory.snorm_one_le_snorm_of_prob` or similar

---

## Axiom 6: ENNReal.toReal Continuity at 0

**Location**: Line 1234 (Block 3)

```lean
/-- The toReal function on ENNReal is continuous at 0. -/
axiom ennreal_tendsto_toReal_zero
    {α : Type*} (f : α → ℝ≥0∞) (a : Filter α) :
    Tendsto f a (𝓝 0) → Tendsto (fun x => (f x).toReal) a (𝓝 0)
```

**What it says**: If `xₙ → 0` in ENNReal, then `xₙ.toReal → 0` in ℝ

**Why standard**: This is a basic continuity property of toReal

**Usage in proof**:
- Convert L² convergence `snorm → 0` (ENNReal) to `snorm.toReal → 0` (ℝ)
- Needed because squeeze theorem works in ℝ, not ENNReal

**Note**: Mathlib has `ENNReal.continuous_toReal` and `ENNReal.tendsto_toReal`. May just need correct application.

---

## Summary

**Total**: 6 axioms needed

**Categorization**:
- **2 axioms**: Conditional expectation linearity (scalar + sum)
- **1 axiom**: Bounded → integrable
- **3 axioms**: Mean Ergodic Theorem machinery (L² MET + Hölder + ENNReal)

**Expected difficulty**:
- **Easy** (Axioms 1, 2, 5, 6): Should exist in mathlib, just need to find
- **Medium** (Axiom 3): Should be provable from `Measure.integrable_of_bounded`
- **Hard** (Axiom 4): Either in mathlib at Lp level (need bridge) or genuinely deep theorem

**Recommendation order**:
1. Start with Axiom 3 (bounded → integrable) - most self-contained
2. Then Axioms 1 & 2 (CE linearity) - should have mathlib versions
3. Then Axiom 5 (Hölder) - should be `snorm_one_le_snorm_two` or similar
4. Then Axiom 6 (ENNReal) - may just be `ENNReal.tendsto_toReal`
5. Finally Axiom 4 (MET) - hardest, may need axiomatization

## Application Notes

Once these are proved, replace the corresponding `sorry` statements:

- **Axiom 1**: Lines 1013, 1115 - replace sorry with `exact condExp_const_mul hm c f`
- **Axiom 2**: Lines 1024, 1127 - replace sorry with `exact condExp_sum_finset hm s f`
- **Axiom 3**: Line 1033 - replace sorry with `exact integrable_of_bounded_measurable ... `
- **Axiom 4**: Line 1217 - replace sorry with application of `birkhoffAverage_tendsto_condexp_L2`
- **Axiom 5**: Line 1223 - replace sorry with application of `snorm_one_le_snorm_two_toReal`
- **Axiom 6**: Line 1234 - replace sorry with application of `ennreal_tendsto_toReal_zero`
