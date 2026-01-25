---
Repo: https://github.com/human-oriented/exchangeability
Commit: aec253b69aaabbd93dd82fe1a7d9bbf34cf90ab5
Date: 2026-01-24
Built: yes
Lean: v4.27.0-rc1
Lake: v5.0.0-src+2fcce72
---

# Proof Overview: Three Routes to de Finetti

## Summary Table

| Aspect | Martingale | L² | Koopman |
|--------|-----------|-----|---------|
| **Reference** | Kallenberg "Third proof" | Kallenberg "Second proof" | Kallenberg "First proof" |
| **Key technique** | Reverse martingale convergence | Elementary L² bounds | Mean Ergodic Theorem |
| **Dependencies** | Medium | Lightest | Heaviest |
| **State space** | Standard Borel | ℝ (bounded or L²) | ℝ (L²) |
| **Files** | 14 | 13 | 18 |
| **Lines** | ~4000 | ~6500 | ~6000 |
| **Status** | Complete | Complete | Complete |
| **Default** | Yes | No | No |

---

## Shared Components

All three proofs share:

1. **Core definitions** (`Contractability.lean`, `ConditionallyIID.lean`)
2. **Easy directions**:
   - `contractable_of_exchangeable` (combinatorial)
   - `exchangeable_of_conditionallyIID` (product measure invariance)
3. **Common ending** (`CommonEnding.lean`):
   - π-system/monotone class extension
   - `finite_product_formula`
   - Upgrade from cylinders to full Borel sets

The divergence is in proving `Contractable → ConditionallyIID`:
- Constructing the directing measure `ν`
- Proving the finite-dimensional product formula for cylinder sets

---

## Route 1: Reverse Martingale (Default)

**Key insight:** The conditional expectation `𝔼[1_B | ℱ_{≥n}]` forms a reverse martingale that converges to `𝔼[1_B | ℱ_∞]`, the tail σ-algebra.

### Proof skeleton

1. **Define the directing measure**
   - `directingMeasure X` via `condExpKernel`
   - Uses conditional probability kernel from mathlib

2. **Reverse martingale convergence**
   - The sequence `𝔼[1_B | ℱ_{≥n}]` converges a.e. and in L¹
   - Limit is `𝔼[1_B | ℱ_∞]`

3. **Tail factorization**
   - The tail σ-algebra is shift-invariant
   - Conditional law given tail equals `ν(ω)`

4. **Product formula for cylinders**
   - Uses independence conditional on tail
   - `finite_product_formula`

5. **Extend to Borel sets**
   - π-system/monotone class (`CommonEnding.lean`)

### Key lemmas

```lean
-- Directing measure construction
def directingMeasure (X : ℕ → Ω → α) : Ω → Measure α

-- Convergence
theorem condExp_convergence_ae :
  ∀ᵐ ω, Tendsto (condExp_n ω) atTop (nhds (condExp_tail ω))

-- Product formula
theorem finite_product_formula :
  Map (Xₖ) μ = μ.bind (fun ω => Measure.pi (fun _ => ν ω))
```

### Dependencies
- Conditional expectation (mathlib)
- Reverse martingale convergence (built in repo)
- Conditional probability kernels (mathlib)

---

## Route 2: Elementary L² Bounds

**Key insight:** For bounded random variables, Kallenberg's Lemma 1.2 gives explicit L² bounds on correlations that force limiting independence.

### Proof skeleton

1. **Clip to [0,1]** (`Clip01.lean`)
   - Work with bounded random variables first
   - Transfer results via approximation

2. **Block averages** (`BlockAverages.lean`)
   - Define `α_n = (1/n) Σᵢ₌₀ⁿ⁻¹ Xᵢ`
   - Study their L² properties

3. **L² convergence** (`AlphaConvergence.lean`)
   - `α_n` converges in L² to a limit `α_∞`
   - Uses contractability to bound cross-correlations

4. **Directing measure from limit** (`DirectingMeasureCore.lean`)
   - Define `ν(ω) = δ_{α_∞(ω)}`... (actually more subtle)
   - The limit encodes the directing measure

5. **Product formula** (`DirectingMeasureIntegral.lean`)
   - Verify finite-dimensional products match

6. **Extend to Borel** (`CommonEnding.lean`)

### Key lemmas

```lean
-- Kallenberg Lemma 1.2: correlation bound
lemma kallenberg_correlation_bound :
  |𝔼[XᵢXⱼ] - 𝔼[Xᵢ]𝔼[Xⱼ]| ≤ C / min(i,j)

-- L² convergence
theorem alpha_L2_convergence :
  Tendsto αₙ atTop (L² μ, α_∞)
```

### Dependencies
- L² spaces (mathlib)
- Basic measure theory
- **Lightest dependencies** - no ergodic theory, minimal martingale theory

---

## Route 3: Mean Ergodic Theorem (Koopman)

**Key insight:** The shift operator on the path space is measure-preserving. The Mean Ergodic Theorem gives L² convergence of Cesàro averages to the projection onto invariant functions.

### Proof skeleton

1. **Path space shift** (`PathSpace/Shift.lean`)
   - Define `T : (ℕ → α) → (ℕ → α)` by `T(x)ₙ = x_{n+1}`
   - Contractability implies `T` is measure-preserving

2. **Koopman operator** (`Ergodic/KoopmanMeanErgodic.lean`)
   - `U_T f = f ∘ T`
   - Acts on L² as an isometry

3. **Mean Ergodic Theorem** (`Ergodic/KoopmanMeanErgodic.lean`)
   - `(1/n) Σᵢ₌₀ⁿ⁻¹ Uᵢ f → P f` in L²
   - `P` is projection onto `U`-invariant subspace

4. **Invariant functions** (`Ergodic/InvariantSigma.lean`)
   - Invariant functions are tail-measurable
   - Extract directing measure from invariant limit

5. **Product formula** (various files)
   - Uses factorization through ergodic decomposition

6. **Extend to Borel** (`CommonEnding.lean`)

### Key lemmas

```lean
-- Mean Ergodic Theorem
theorem mean_ergodic_L2 :
  Tendsto (cesaro U f) atTop (L², P f)

-- Invariant projection
theorem projection_invariant :
  U (P f) = P f
```

### Dependencies
- Ergodic theory (Koopman operators, projections)
- L² spaces and Hilbert space theory
- **Heaviest dependencies**

---

## Comparison

### Conceptual elegance

| Route | Score | Notes |
|-------|-------|-------|
| Martingale | ★★★★☆ | Probabilistically natural |
| L² | ★★★☆☆ | Elementary but technical |
| Koopman | ★★★★★ | Connects to ergodic theory |

### Formalization complexity

| Route | Score | Notes |
|-------|-------|-------|
| Martingale | ★★★☆☆ | Uses mathlib machinery well |
| L² | ★★★★☆ | Many explicit estimates |
| Koopman | ★★★★★ | Requires ergodic theory setup |

### Generalizability

| Route | Score | Notes |
|-------|-------|-------|
| Martingale | ★★★★★ | Works for general state spaces |
| L² | ★★★☆☆ | Primarily for ℝ-valued |
| Koopman | ★★★★☆ | Connects to broader theory |

---

## Which to use?

- **For standard Borel spaces:** Use the martingale proof (default)
- **For understanding dependencies:** Use the L² proof
- **For connections to dynamics:** Use the Koopman proof
- **For mathlib contribution:** Martingale proof likely cleanest
