# Lean Blueprint: de Finetti via Mean Ergodic Theorem

**Project**: Formalization of de Finetti's Theorem using the Mean Ergodic approach  
**Target**: Lean 4 + mathlib4  
**Primary Reference**: Olav Kallenberg (2005), *Probabilistic Symmetries and Invariance Principles*, Springer, Chapter 1 (pages 26-27)

---

## Overview

### Goal

Formalize the **mean-ergodic proof** of de Finetti's theorem for infinite exchangeable sequences on standard Borel spaces. The key insight (following Kallenberg's "First proof" on page 26) is to:

1. Define the **left shift** σ on path space Ω = ℕ → α
2. Construct the **Koopman operator** U on L²(μ) induced by σ
3. Apply the **Mean Ergodic Theorem (MET)** to show Birkhoff averages converge in L² to the orthogonal projection onto the fixed-point subspace
4. **Identify** this projection with the conditional expectation onto the **shift-invariant σ-algebra** 𝓘_ξ
5. Deduce the **conditional product structure** via dominated convergence and "extreme members agree"
6. Conclude that the sequence is **conditionally i.i.d.** given 𝓘_ξ

---

## Mathematical Background

### Kallenberg's Theorem 1.1 (page 26)

> **Theorem 1.1** (Infinite exchangeable sequences)  
> For a random sequence ξ = (ξₙ)_{n∈ℕ} taking values in a measurable space S:
> - **(i) contractable** ⇔ **(ii) exchangeable** ⇔ **(iii) conditionally i.i.d.**  
> when S is **Borel** (standard Borel space).

**Note**: "Contractable" means the empirical measures converge; we work directly with stationarity and apply MET.

### Kallenberg's First Proof (page 26)

1. Set **𝓘_ξ = ξ⁻¹(𝓘)** (the shift-invariant σ-algebra)
2. Let **ν = Law(ξ₁ | 𝓘_ξ)** be a regular conditional distribution
3. By the **ergodic theorem** (MET), empirical measures (1/n)∑ᵢ δ_{ξᵢ} converge a.s. to ν
4. By **dominated convergence**, E[∏_{k≤m} f_k(ξ_{i_k}) | 𝓘_ξ] equals the limit as min i_k → ∞ and max i_k → ∞
5. Both limits equal **∏_k ∫f_k dν** (independence + ergodicity)
6. Extend via **monotone class argument**
7. Conclude ξ is conditionally i.i.d. given 𝓘_ξ

### Kallenberg's Lemma 1.2 (page 26)

> **Lemma 1.2**: Let ξ₁,...,ξₙ ∈ L² with common mean m, variance σ², and cov(ξᵢ,ξⱼ) = σ²ρ for i ≠ j.  
> For probability distributions p, q: E(∑ᵢ pᵢξᵢ - ∑ᵢ qᵢξᵢ)² ≤ 2σ²(1-ρ) sup_j |pⱼ - qⱼ|

Alternative elementary route to L² contractability.

---

## File Structure

### Files Implemented

1. **`Prob/Ergodic/KoopmanMeanErgodic.lean`**: Shift, Koopman, MET
2. **`Prob/DeFinetti/InvariantSigma.lean`**: Shift-invariant σ-algebra, projection = condexp
3. **`Prob/DeFinetti/MeanErgodicStep.lean`**: Cylinder functions, main convergence results
4. **`Exchangeability/Contractability.lean`**: Algebraic backbone proving the
   easy implication `contractable → exchangeable` and its converse via
   permutation arguments.  These lemmas plug into every proof strategy for
   Kallenberg’s Theorem 1.1.

---

## FILE 1: KoopmanMeanErgodic.lean

### Key Definitions

- **`shift`**: Left shift (shift ω) n = ω (n+1)
- **`koopman`**: Koopman operator on L²(μ): (U f)(ω) = f(shift ω)
- **`birkhoffAverage`**: (1/n) ∑_{k<n} U^k f
- **`fixedSpace`**: {f | U f = f}

### Key Results

- **`measurable_shift`**: shift is measurable
- **`measurePreserving_shift_pi`**: shift preserves product measures
- **`koopman_isometry`**: Koopman is an isometry
- **`birkhoffAverage_tendsto_fixedSpace`**: MET - Birkhoff averages → projection onto fixed space

**Citation**: Standard von Neumann Mean Ergodic Theorem

---

## FILE 2: InvariantSigma.lean

### Key Definitions

- **`isShiftInvariant`**: Sets with shift⁻¹ s = s
- **`shiftInvariantSigma`**: σ-algebra of invariant sets (Kallenberg's 𝓘_ξ)
- **`fixedSubspace`**: L² functions fixed by Koopman
- **`condexpL2`**: Conditional expectation as orthogonal projection

### Key Results

- **`mem_shiftInvariantSigma_iff`**: Characterization of invariant sets
- **`invMeasurable_iff_shiftInvariant`**: Functions measurable w.r.t. invariant σ-algebra ⟺ shift-invariant
- **`range_condexp_eq_fixedSubspace`**: Both equal the same subspace
- **`proj_eq_condexp`**: Orthogonal projection = conditional expectation

**Citation**: Kallenberg p.26 - the bridge between ergodic theory and probability

---

## FILE 3: MeanErgodicStep.lean

### Key Definitions

- **`cylinderFunction`**: Functions depending on finitely many coordinates
- **`productCylinder`**: ∏_{k<m} f_k(ω k)
- **`shiftedCylinder`**: F ∘ shift^n

### Key Results

- **`birkhoffAverage_tendsto_condexp`**: Combines MET + projection = condexp
- **`birkhoffCylinder_tendsto_condexp`**: Specialization to cylinders
- **`extremeMembers_agree`**: "Extreme members" limits coincide
- **`condexp_cylinder_factorizes`**: E[∏f_k(ξ_{i_k})|𝓘_ξ] = ∏∫f_k dν
- **`l2_contractability_bound`**: Elementary L² bound (Lemma 1.2)

**Citation**: Kallenberg p.26 - dominated convergence + monotone class argument

---

## Dependency Graph

```
measurable_shift → measurePreserving_shift_pi → koopman
  → birkhoffAverage_tendsto_fixedSpace (MET)
  → proj_eq_condexp
  → birkhoffAverage_tendsto_condexp
  → birkhoffCylinder_tendsto_condexp
  → condexp_cylinder_factorizes
```

---

## Implementation Status

All three core files created with:
- ✅ Type signatures and structure
- ✅ Documentation with Kallenberg citations
- ⚠️ Proofs marked with `sorry` (requires MET from mathlib)

---

## Next Steps

1. Resolve mathlib MET lemma name (check `#find birkhoff`)
2. Complete proof of `measurePreserving_shift_pi` via cylinder sets
3. Fill `proj_eq_condexp` using uniqueness of orthogonal projections
4. Complete dominated convergence arguments in `condexp_cylinder_factorizes`
5. Add tests for i.i.d., periodic, and mixture cases

---

## References

**Primary**: Olav Kallenberg (2005), *Probabilistic Symmetries and Invariance Principles*, Springer  
- Theorem 1.1 (page 26): de Finetti for Borel spaces  
- "First proof" (page 26): Mean-ergodic approach  
- Lemma 1.2 (page 26): L² contractability bound

**Mathlib**: MeanErgodic, L2Space, ConditionalExpectation, Projection
