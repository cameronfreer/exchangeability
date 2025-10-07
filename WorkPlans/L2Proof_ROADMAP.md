# L2Proof.lean Implementation Roadmap

This document provides a detailed roadmap for completing the sorries in `L2Proof.lean`, based on Kallenberg's "Second proof" of de Finetti's theorem.

## Big Picture

We **do not need** Step 1 (uniform covariance structure). The L² contractability bound from `L2Approach.lean` (Lemma 1.2) is sufficient to show empirical averages are Cauchy in L² (hence L¹ on probability spaces), and completeness of L¹ gives the limits αₙ.

## Implementation Checklist

### ✅ Already Done

1. **Postponed `contractable_covariance_structure`** - not needed for main proof
2. **Removed `Lp_complete` custom wrapper** - use mathlib's `CompleteSpace (Lp E p μ)`
3. **Restructured `weighted_sums_converge_L1`** with correct proof outline
4. **Fixed unicode issues** - replaced α, ν with `alpha`, `nu`, etc.
5. **Simplified `alpha_is_reverse_martingale`** - defers to Step 5

### 🚧 Needs Implementation

#### Step 2: `weighted_sums_converge_L1` (Priority: HIGH)

**Structure (already in place):**
```lean
let A : ℕ → ℕ → Ω → ℝ := fun n m ω => (1 / (m : ℝ)) * ∑ k : Fin m, f (X (n + k.val + 1) ω)
```

**Sorries to fill:**

1. **`hA_cauchy_L2`**: Apply `l2_contractability_bound` to uniform distributions
   - Use the existing `l2_contractability_bound` from `L2Approach.lean`
   - Specialize to uniform weights `p = uniform on {n+1,...,n+m}`
   - This gives Cauchy in L² for fixed n

2. **`hA_cauchy_L1`**: Use `snorm_mono_exponent`
   - On probability spaces: `‖·‖₁ ≤ ‖·‖₂`
   - Lemma: `snorm_mono_exponent` with `1 ≤ 2` and `[IsProbabilityMeasure μ]`

3. **`h_exist_α`**: Use `CompleteSpace (Lp ℝ 1 μ)`
   - Build Cauchy sequence in `Lp ℝ 1 μ` using `MemLp.toLp`
   - Apply `CauchySeq.tendsto_of_complete`
   - Extract representative with `MemLp.of_toLp_eq` or similar

4. **`hα_cauchy_L1`**: 3ε triangle inequality (MECHANICAL)
   - Fix ε > 0
   - Pick M so `A n m` is ε/3-close to `α n` for all n ≥ N₁, m ≥ M
   - Pick M' ≥ M so `A n M'` and `A n' M'` are ε/3-close using L² bound
   - Triangle: `|α n - α n'| ≤ |α n - A n M'| + |A n M' - A n' M'| + |A n' M' - α n'|`
   - Each term < ε/3, so total < ε

5. **`hα_limit`**: Use `CompleteSpace (Lp ℝ 1 μ)` again
   - Same pattern as h_exist_α, now for sequence n ↦ α n

6. **Convert `snorm` to `∫ |·|`**: Final packaging
   - Use `snorm_one_eq_lintegral_nnnorm` or similar
   - Simplify with `Real.rpow_one`

#### Step 3: `subsequence_criterion_convergence_in_probability` (Priority: MEDIUM)

**Mathlib lemmas to use:**
- `TendstoInMeasure.subseq_tendsto_ae` - main result
- `tendstoInMeasure_of_tendsto_L1` or Markov's inequality manually

**Implementation:**
```lean
have h_in_measure : TendstoInMeasure μ (fun n => ξ n) ξ_limit := by
  exact tendstoInMeasure_of_prob (ξ := ξ) (ξ_limit := ξ_limit) h_prob_conv
rcases h_in_measure.subseq_tendsto_ae with ⟨φ, hmono, h_ae⟩
exact ⟨φ, hmono, h_ae⟩
```

If `tendstoInMeasure_of_prob` doesn't exist, use Markov inline:
```lean
have : ∀ ε > 0, μ {ω | |ξ n ω - ξ_limit ω| ≥ ε} ≤ (1/ε) * ∫ ω, |ξ n ω - ξ_limit ω| ∂μ
```

#### Step 4: `reverse_martingale_subsequence_convergence` (Priority: MEDIUM)

**Chain:** L¹ convergence → convergence in probability → a.s. subsequence

```lean
have h_prob : TendstoInMeasure μ (fun n => alpha n) alpha_inf := by
  exact tendstoInMeasure_of_tendsto_L1 h_L1_conv
rcases h_prob.subseq_tendsto_ae with ⟨φ, hmono, h_ae⟩
exact ⟨φ, hmono, h_ae⟩
```

#### Step 5: `contractability_conditional_expectation` (Priority: HIGH)

**Strategy:** Use dominated convergence + contractability to show tail events have matching integrals

**Key steps:**
1. Use contractability to relate `∫ f(X i) · 1_A` across different indices i
2. Apply `tendsto_integral_of_dominated_convergence` with bound from `hf_bdd`
3. Pass limit inside integral for each tail event A

**OR use uniqueness directly:**
```lean
apply ae_eq_condexp_of_forall_set_integral_eq
```
with the hypothesis that for all tail events `A ∈ 𝓖∞`:
```lean
∫ ω in A, f (X i ω) ∂μ = ∫ ω in A, alpha_inf ω ∂μ
```

#### Step 6: `alpha_is_conditional_expectation` (Priority: HIGH)

**Build directing measure from conditional expectations**

1. Define tail σ-algebras: `𝓖 n := σ(X_{n+1}, X_{n+2}, ...)`
2. From Step 5: `alpha n =ᵐ[μ] condexp μ (𝓖 n) (f ∘ X (n+1))`
3. Define `nu(ω)` as conditional law of X given tail
4. Show `alpha n ω = ∫ f d(nu ω)` a.e.

**Plumbing needed:**
- `directingMeasureFromTail` or similar from CommonEnding
- Disintegration kernel construction
- `condexp_evaluates_with_kernel` property

#### Step 7: `deFinetti_second_proof` (Priority: HIGH)

**Connect to CommonEnding:**

```lean
rcases alpha_is_conditional_expectation X hX_contract hX_meas
  (f := id) (hf_meas := measurable_id) (alpha := ?alpha) with ⟨nu, hνprob, hνmeas, hα⟩
let K : Kernel Ω ℝ := CommonEnding.kernelOfDirectingMeasure nu hνprob
have h_cond_iid : ConditionallyIID μ X K :=
  CommonEnding.complete_from_directing_measure μ X hX_meas hX_contract K ...
exact ⟨K, ..., h_cond_iid⟩
```

#### Step 8: `deFinetti_from_exchangeable` (Priority: LOW)

**Already essentially done:**
```lean
have hX_contract : Contractable μ X := contractable_of_exchangeable hX_exch hX_meas
-- Then propagate result from deFinetti_second_proof
```

## Mathlib Lemma Reference

### Completeness of Lp
```lean
#find _ CompleteSpace (Lp _ _ _)
-- Instance: CompleteSpace (Lp E p μ)
-- Use: CauchySeq.tendsto_of_complete
```

### snorm and Lp norms
```lean
#find _ snorm _ _
#find _ snorm_mono_exponent
-- Key: snorm f 1 μ ≤ snorm f 2 μ on probability spaces
```

### Convergence in measure
```lean
#find _ TendstoInMeasure
#find _ TendstoInMeasure.subseq_tendsto_ae
#find _ tendstoInMeasure_of_tendsto_L1
```

### Conditional expectation
```lean
#find _ condexp _ unique
#find _ ae_eq_condexp_of_forall_set_integral_eq
#find _ tendsto_integral_of_dominated_convergence
```

## Dependencies

### From L2Approach.lean (already complete)
- `l2_contractability_bound`: The key L² inequality (Lemma 1.2)

### From CommonEnding.lean (already complete)
- `complete_from_directing_measure`: Finishes proof from directing measure
- π-system argument infrastructure

### From Contractability.lean (already complete)
- `contractable_of_exchangeable`: Exchangeable ⇒ contractable

## Implementation Order

**Phase 1: Core convergence (Steps 2-4)**
1. Fill `weighted_sums_converge_L1` sorries
2. Implement subsequence extraction lemmas
3. Test that phases compose correctly

**Phase 2: Conditional expectation (Steps 5-6)**
4. Prove tail event integral equality
5. Build directing measure from conditionals
6. Connect to tail σ-algebra structure

**Phase 3: Final connection (Steps 7-8)**
7. Wire up to CommonEnding
8. Propagate through exchangeable case

## Notes

- The 3ε argument in Step 2.4 is mechanical but tedious (15-20 lines)
- Most sorries are short (5-15 lines) once correct lemma names are found
- Key challenge: finding exact mathlib names for your snapshot
- Use `#find` liberally to locate lemmas
- Consider asking for detailed 3ε implementation if needed

## Status

- **CommonEnding.lean**: ✅ Complete proof structure, compiles
- **L2Proof.lean**: 🚧 Structure complete, needs sorry implementations
- **Compilation**: 🔴 Has errors from incomplete edits (need to fix syntax first)
