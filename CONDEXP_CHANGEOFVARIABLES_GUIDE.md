# Guide to Proving `condexp_changeOfVariables`

## The Goal

**Location:** `Exchangeability/Bridge/CesaroToCondExp.lean:301-335`

Prove:
```lean
lemma condexp_changeOfVariables
    {α β : Type*} [MeasurableSpace α] {m₀ : MeasurableSpace β}
    (μ : Measure α) (f : α → β) (hf : @Measurable α β _ m₀ f)
    (m' : MeasurableSpace β) (hm' : m' ≤ m₀)
    {g : β → ℝ}
    (hg : Integrable g (@Measure.map α β _ m₀ f μ)) :
    ((@Measure.map α β _ m₀ f μ)[g | m']) ∘ f
      =ᵐ[μ] μ[g ∘ f | MeasurableSpace.comap f m']
```

## Mathematical Proof Outline

Let `ν := Measure.map f μ`. We'll show:
- Both sides are `comap f m'`-measurable
- Both sides are integrable w.r.t. μ
- For all `A ∈ m'`, the set integrals agree

Then apply uniqueness of conditional expectation.

## Key Mathlib Lemmas You'll Need

### 1. Integrability Under Pushforward
```lean
-- From: Mathlib/MeasureTheory/Function/L1Space/Integrable.lean
theorem integrable_map_measure {f : α → β} (hf : AEMeasurable f μ)
    {g : β → E} :
    Integrable g (Measure.map f μ) ↔ Integrable (g ∘ f) μ
```
**Use for:** Converting `Integrable g ν` to `Integrable (g ∘ f) μ`

### 2. Change of Variables for Integrals
```lean
-- From: Mathlib/MeasureTheory/Integral/Bochner/Basic.lean
theorem integral_map {f : α → β} (hf : AEMeasurable f μ)
    {g : β → E} (hg : Integrable g (Measure.map f μ)) :
    ∫ y, g y ∂(Measure.map f μ) = ∫ x, g (f x) ∂μ
```
**Use for:** Converting `∫_A ν[g|m'] dν` to `∫_{f⁻¹(A)} (ν[g|m'] ∘ f) dμ`

### 3. Characterizing Property of Conditional Expectation
```lean
-- From: Mathlib/MeasureTheory/Function/ConditionalExpectation/Basic.lean
theorem setIntegral_condExp {f : α → E} (hf : Integrable f μ)
    (hs : MeasurableSet[m] s) :
    ∫ x in s, (μ[f | m]) x ∂μ = ∫ x in s, f x ∂μ
```
**Use for:** Converting `∫_A ν[g|m'] dν` to `∫_A g dν`

### 4. Uniqueness of Conditional Expectation
```lean
-- From: Mathlib/MeasureTheory/Function/ConditionalExpectation/Basic.lean
theorem ae_eq_condExp_of_forall_setIntegral_eq
    {f g : α → E}
    (hf : Integrable f μ)
    (hfm : Measurable[m] f)
    (hg : Integrable g μ)
    (hgm : Measurable[m] g)
    (hfg : ∀ s, MeasurableSet[m] s → μ s < ∞ →
           ∫ x in s, f x ∂μ = ∫ x in s, g x ∂μ) :
    f =ᵐ[μ] (μ[g | m])
```
**Use for:** Final uniqueness argument

## Proof Steps

### Step 1: Integrability of `g ∘ f`
```lean
have hgf_int : Integrable (g ∘ f) μ := by
  rw [← integrable_map_measure hf.aemeasurable]
  exact hg
```

**Challenge:** The typeclass instance for `Measure.map f μ` needs to match.

### Step 2: Measurability of LHS
```lean
have hLHS_meas : @Measurable α ℝ (MeasurableSpace.comap f m') _ ((ν)[g | m'] ∘ f) := by
  -- ν[g | m'] is m'-measurable
  -- Composition with measurable f gives comap f m'-measurability
  sorry
```

**Challenge:** Need to show conditional expectation is measurable w.r.t. sub-σ-algebra.

### Step 3: Integral Equality Chain
```lean
have h_eq : ∀ (A : Set β), @MeasurableSet β m' A → μ (f ⁻¹' A) < ∞ →
    ∫ ω in f⁻¹' A, (ν[g | m'] ∘ f) ω ∂μ = ∫ ω in f⁻¹' A, (g ∘ f) ω ∂μ := by
  intro A hA hμA
  calc ∫ ω in f⁻¹' A, (ν[g | m'] ∘ f) ω ∂μ
      = ∫ y in A, ν[g | m'] y ∂ν := by
          -- Use integral_map
          sorry
    _ = ∫ y in A, g y ∂ν := by
          -- Use setIntegral_condExp
          sorry
    _ = ∫ ω in f⁻¹' A, (g ∘ f) ω ∂μ := by
          -- Use integral_map again
          sorry
```

**Challenge:** Each integral_map requires careful instance management.

### Step 4: Apply Uniqueness
```lean
exact ae_eq_condExp_of_forall_setIntegral_eq hgf_int hLHS_meas ... h_eq
```

## The Typeclass Challenge

The main difficulty is that:
- `ν = Measure.map f μ` has type `@Measure β m₀`
- But `ν[g | m']` is conditional expectation w.r.t. sub-σ-algebra `m' ≤ m₀`
- Each application of `integral_map` needs:
  ```lean
  @integral_map α β _ m' μ f hf g hg
  ```
  But Lean infers `m₀` instead of `m'`

## Potential Approaches

### Approach 1: Explicit `@` Applications
Use `@integral_map` with all instances explicitly specified:
```lean
@integral_map α β _ m' (Measure.map f μ) ...
```

### Approach 2: Local Instances
Add local instances to guide typeclass resolution:
```lean
letI : MeasurableSpace β := m'
-- Now work in this context
```

### Approach 3: Lemma Variants
Prove helper lemmas for the specific typeclass pattern:
```lean
lemma integral_map_subSigma ... := ...
```

### Approach 4: Mathlib PR
The cleanest solution is to add proper API to mathlib for conditional expectation under measure maps.

## Testing Your Proof

Once you have a candidate proof, verify it works in the application:
- `condexp_pullback_along_pathify` (line 354) should complete
- Main theorem `h_L1` (line 455) should then be provable

## Resources

- **Mathlib docs:** https://leanprover-community.github.io/mathlib4_docs/
- **Zulip #mathlib4:** Ask if similar lemma already exists
- **Conditional expectation file:** `.lake/packages/mathlib/Mathlib/MeasureTheory/Function/ConditionalExpectation/Basic.lean`
- **Integration file:** `.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`

## Why This Matters

Once this lemma is proved:
1. **Bridge 4** (`condexp_pullback_along_pathify`) completes immediately
2. **Main theorem `h_L1`** becomes straightforward (50-100 lines)
3. **ViaL2.lean axiom** can be removed
4. **First deep ergodic-theoretic connection** in the project is established

This is a fundamental lemma that likely belongs in mathlib's conditional expectation API.
