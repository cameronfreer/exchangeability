---
Repo: https://github.com/human-oriented/exchangeability
Commit: aec253b69aaabbd93dd82fe1a7d9bbf34cf90ab5
Date: 2026-01-24
Built: yes
Lean: v4.27.0-rc1
Lake: v5.0.0-src+2fcce72
---

# Open Questions and Future Extensions

## Completed Work

All three proofs of de Finetti's theorem are complete:
- Martingale proof (default)
- L² proof
- Koopman/Mean Ergodic proof

The full equivalence `Contractable ⟺ Exchangeable ⟺ ConditionallyIID` is established.

## Potential Extensions

### 1. Finite Exchangeability

**Diaconis-Freedman (1980):** Finite versions of de Finetti's theorem with explicit error bounds.

**Question:** Can we formalize the finite de Finetti theorem?

**Approach:**
- Bound the total variation distance from a mixture of products
- Relates to sampling without replacement

**Difficulty:** Medium - requires careful quantitative analysis

---

### 2. Partial Exchangeability

**Kallenberg (2005), Chapter 7:** Sequences that are exchangeable within blocks but not across blocks.

**Example:** Observations from multiple subjects where observations are exchangeable within each subject.

**Question:** Formalize partial exchangeability and its representation theorem.

**Difficulty:** Medium-High - requires multi-index infrastructure

---

### 3. Continuous-Time Exchangeability

**Kallenberg (2005), Chapter 9:** Exchangeable random measures and point processes.

**Example:** Poisson processes with random intensity.

**Question:** Formalize exchangeable point processes.

**Difficulty:** High - requires point process machinery

---

### 4. Exchangeable Arrays

**Aldous-Hoover theorem:** Two-dimensional arrays with separate row and column exchangeability.

**Question:** Formalize the Aldous-Hoover representation.

**Difficulty:** High - requires sophisticated measure theory

---

### 5. mathlib Integration

**Current status:** ForMathlib/ contains 45 files with potential contributions.

**Question:** Which lemmas should be upstreamed to mathlib?

**Candidates:**
- Reverse martingale convergence enhancements
- Conditional independence infrastructure
- π-system utilities

**Difficulty:** Medium - requires mathlib style compliance

---

### 6. Computation

**Question:** Can we extract computable approximations?

**Ideas:**
- Truncated directing measure approximations
- Finite-sample bounds
- Connection to MCMC methods

**Difficulty:** High - requires computational interpretation of proofs

---

### 7. Connections to Other Areas

#### Bayesian Nonparametrics

de Finetti's theorem is foundational for:
- Dirichlet process priors
- Chinese restaurant process
- Infinite mixture models

#### Probability Theory

- Connection to tail σ-algebras and 0-1 laws
- Relationship to ergodic decomposition
- Links to stationary processes

#### Logic and Foundations

- Constructive versions?
- Type-theoretic interpretation of "random measure"

---

## Technical Debt

### Build Warnings

The build produces warnings that could be cleaned up:
- ~20 unused section variables
- ~15 deprecated lemma names
- ~25 unused simp arguments

**Action:** Apply golfing and update to new mathlib names.

### Code Organization

- Some helper lemmas could move to ForMathlib
- Proof routes share some duplicated infrastructure
- Consider unifying common patterns

---

## Questions from the Formalization

### 1. Tail σ-Algebra Characterization

**Current state:** Tail σ-algebra defined as intersection of shifted σ-algebras.

**Question:** Prove the characterization: tail = shift-invariant σ-algebra (a.e.).

**Reference:** Kallenberg FMP 10.2-10.4

---

### 2. Conditional Independence Simplification

**Current state:** Conditional independence defined via conditional expectations.

**Question:** Explore alternative characterizations (kernels, independence given σ-algebra).

---

### 3. Uniqueness of Directing Measure

**Current state:** Existence proved; uniqueness implicit.

**Question:** Make uniqueness (up to a.e. equality) explicit.

---

### 4. Rate of Convergence

**Question:** Can we give rates for the convergence of block averages?

**Relevance:** Quantitative versions of de Finetti could have applications.

---

## Suggestions for Paper

When writing the AFM paper:

1. **Highlight the three proofs:** Show that formalizing multiple proofs provides insight.

2. **Discuss mathlib integration:** What infrastructure was reused vs. built.

3. **Note the combinatorial heart:** The permutation extension lemma is purely combinatorial but crucial.

4. **Emphasize π-system technique:** Show how the same technique works for both equivalence proofs (Exchangeable ↔ FullyExchangeable and the de Finetti extension).

5. **Compare proof lengths:** Quantify complexity of each approach.

6. **Discuss axioms:** Emphasize that only standard mathlib axioms are used.
