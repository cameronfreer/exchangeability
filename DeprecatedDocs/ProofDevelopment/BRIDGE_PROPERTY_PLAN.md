# Bridge Property & Monotone Class Implementation Plan

## Overview

We have 3 related sorries in ViaL2.lean that implement the bridge property using the π-system → monotone class pattern:

1. **Line 3148**: Base case - agreement on generators (half-lines `Iic t`)
2. **Line 3159**: Extension via monotone class theorem to all bounded Borel functions
3. **Line 3207**: Bridge property for cylinder sets (product of indicators)

## Mathematical Strategy

### π-System → Dynkin System → Monotone Class Pattern

The standard approach:
1. Define a **generator** 𝒢 (π-system): indicators of half-lines `{Iic t | t ∈ ℝ}`
2. Define the **good class** C: `{f | ∀ᵐ ω, α_f(ω) = ∫ f dν(ω)}`
3. Prove C contains 𝒢 (base case)
4. Prove C is closed under linear combinations
5. Prove C is closed under monotone limits (monotone class property)
6. Apply mathlib's monotone class theorem: C contains all bounded measurable functions

## Implementation Steps

### Step 1: Base Case (Line 3148)

**Goal**: `∀ t, ∀ᵐ ω, alphaIic t ω = ν(ω)(Iic t)`

**Proof outline**:
```lean
intro t
-- Key facts to connect:
-- (1) Definition: ν(ω) = Measure.ofStieltjesFunction (cdf_from_alpha X ... ω)
-- (2) Property: (Measure.ofStieltjesFunction F) (Iic t) = ofReal (F t - F bot)
-- (3) For probability CDFs: F bot = 0, so ν(ω)(Iic t) = ofReal (cdf_from_alpha ω t)
-- (4) Definition: cdf_from_alpha ω t = ⨅ q∈{q:ℚ | t < q}, alphaIic q ω
-- (5) Connection: For continuity points, alphaIic t ω ≈ cdf_from_alpha ω t

-- Two approaches:
-- A) Direct: Show alphaIic t ω = ofReal (cdf_from_alpha ω t) a.e.
-- B) Via limits: Use L¹ convergence and extract pointwise a.e. subsequence

-- For now, use approach A with continuity points having full measure
sorry
```

**Mathlib lemmas to use**:
- `Measure.ofStieltjesFunction.apply_Iic`: relates ν(Iic t) to CDF value
- Properties of `⨅` (infimum) for connecting cdf_from_alpha to alphaIic
- L¹ convergence → a.e. convergence for subsequences

### Step 2: Monotone Class Extension (Line 3159)

**Goal**: Extend from half-lines to all bounded Borel functions

**Proof outline**:
```lean
-- Define the good class
let C : Set (ℝ → ℝ) := {f | Measurable f ∧ 
  (∃ M, ∀ x, |f x| ≤ M) ∧
  (∀ᵐ ω ∂μ, alpha_f ω = ∫ x, f x ∂(ν ω))}

-- Step 2a: C contains generators (half-line indicators)
have h_generators : ∀ t, (Set.Iic t).indicator (fun _ => (1:ℝ)) ∈ C := by
  intro t
  refine ⟨measurable_const.indicator measurableSet_Iic, ⟨1, ?_⟩, ?_⟩
  · intro x; by_cases h : x ≤ t <;> simp [Set.indicator, h]
  · exact base t  -- uses the base case from Step 1

-- Step 2b: C contains linear combinations
have h_linear : ∀ f g ∈ C, ∀ (a b : ℝ), (fun x => a * f x + b * g x) ∈ C := by
  -- Use linearity of both α_f and ∫ · dν
  sorry

-- Step 2c: C is closed under monotone limits
have h_monotone : ∀ (fn : ℕ → ℝ → ℝ), 
  (∀ n, fn n ∈ C) → 
  (∀ x, Monotone (fun n => fn n x)) →
  (∃ M, ∀ n x, |fn n x| ≤ M) →
  (fun x => ⨆ n, fn n x) ∈ C := by
  -- Use monotone convergence theorem for both sides
  sorry

-- Step 2d: Apply mathlib's monotone class theorem
-- C contains π-system → C is monotone class → C contains σ-algebra
refine ⟨alpha, hα_meas, hα_L1, hα_conv, ?_⟩
intro f hf_meas hf_bdd
-- Use monotone class machinery to show f ∈ C
sorry
```

**Mathlib API to use**:
- `MeasureTheory.generateFrom_induction` or similar
- `MeasureTheory.pi_lambda_ind` for π-λ systems
- Monotone convergence theorem: `lintegral_iSup` and `integral_iSup`

### Step 3: Bridge Property by Induction (Line 3207)

**Goal**: `E[∏ᵢ 1_{Bᵢ}(X_{k(i)})] = E[∏ᵢ ν(·)(Bᵢ)]`

**Current structure** (already sketched):
```lean
induction m with
| zero => simp  -- done
| succ m IH =>
  -- The code already has a good outline, just needs formalization:
  
  -- Key steps:
  -- 1. Separate last factor: ∏_{i≤m} = (∏_{i<m}) · (last factor)
  -- 2. Apply directing_measure_integral to get α_{1_B} = ν(·)(B)
  -- 3. Use tower property: E[H · 1_B(X_k)] = E[H · E[1_B(X_k) | σ(earlier coords)]]
  -- 4. By tail-measurability and contractability: E[1_B(X_k) | σ(...)] = ν(·)(B)
  -- 5. Apply IH to the product of m factors
  
  sorry
```

**What needs to be added**:
```lean
-- Formalize the "last factor separation"
have h_prod_split : ∏ i : Fin m.succ, f i = (∏ i : Fin m, f (Fin.castSucc i)) * f (Fin.last m) := by
  rw [Fin.prod_univ_succAbove]
  
-- Apply directing_measure_integral for each indicator
have h_alpha_eq_nu : ∀ i, ∀ᵐ ω ∂μ, 
  alpha_{1_{B i}} ω = (directing_measure ... ω) (B i) := by
  intro i
  exact directing_measure_integral ... (Set.indicator (B i) ...) ...
  
-- Tower property / conditional expectation
-- This requires measurability w.r.t. different σ-fields
have h_tower : ... := by
  -- Apply conditional expectation tower property
  -- Use tail-measurability from contractability
  sorry

-- Combine with IH
calc ∫⁻ ω, ∏ i : Fin m.succ, ... ∂μ
    = ... by rw [h_prod_split]
  _ = ... by rw [h_tower]
  _ = ... by rw [IH]
```

## Implementation Priority

1. **Start with Step 1** (base case) - this is foundational
2. **Then Step 2** (monotone class) - uses Step 1
3. **Finally Step 3** (bridge by induction) - uses Steps 1 & 2

## Mathlib References

Key modules to import/use:
- `Mathlib.MeasureTheory.Constructions.Pi` - for π-systems
- `Mathlib.MeasureTheory.Function.AEEqOfIntegral` - for a.e. equality from integrals
- `Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic` - for tower property
- `Mathlib.Order.Filter.AtTopBot` - for infimum over rationals

## Testing Strategy

After implementing each step:
1. Check that the sorry is removed and the proof compiles
2. Verify no new type errors or broken dependencies
3. Run `lake build Exchangeability.DeFinetti.ViaL2` to ensure everything still works
4. Check that the final `l2_approach_provides_directing_measure` compiles

## Next Actions

Would you like me to:
1. Implement Step 1 first (base case for half-lines)?
2. Add the monotone class infrastructure for Step 2?
3. Formalize the induction steps for Step 3?
