---
Repo: https://github.com/cameronfreer/exchangeability
Commit: aec253b69aaabbd93dd82fe1a7d9bbf34cf90ab5
Date: 2026-01-24
Built: yes
Lean: v4.27.0-rc1
Lake: v5.0.0-src+2fcce72
---

# Main Theorems and Interfaces

## The Central Theorem

### `deFinetti` (Standard Form)

**File:** `Exchangeability/DeFinetti/TheoremViaMartingale.lean:96`

```lean
theorem deFinetti
    [StandardBorelSpace Ω]
    {α : Type*} [MeasurableSpace α] [StandardBorelSpace α] [Nonempty α]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ℕ → Ω → α) (hX_meas : ∀ i, Measurable (X i))
    (hX_exch : Exchangeable μ X) :
    ConditionallyIID μ X
```

**Statement:** Every exchangeable sequence on a standard Borel space is conditionally i.i.d. given the tail σ-algebra.

**Hypotheses:**
- `Ω` is a standard Borel space (probability space)
- `α` is a standard Borel space (state space)
- `μ` is a probability measure
- `X : ℕ → Ω → α` is a sequence of random variables
- Each `X i` is measurable
- `X` is exchangeable under `μ`

**Conclusion:** There exists a directing measure `ν : Ω → Measure α` such that `X` is conditionally i.i.d. with distribution `ν`.

---

### `deFinetti_equivalence` (Two-Way)

**File:** `Exchangeability/DeFinetti/TheoremViaMartingale.lean:116`

```lean
theorem deFinetti_equivalence
    [StandardBorelSpace Ω]
    {α : Type*} [MeasurableSpace α] [StandardBorelSpace α] [Nonempty α]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ℕ → Ω → α) (hX_meas : ∀ i, Measurable (X i)) :
    Exchangeable μ X ↔ ConditionallyIID μ X
```

**Statement:** A sequence is exchangeable if and only if it is conditionally i.i.d.

---

### `deFinetti_RyllNardzewski_equivalence` (Three-Way, Kallenberg 1.1)

**File:** `Exchangeability/DeFinetti/TheoremViaMartingale.lean:138`

```lean
theorem deFinetti_RyllNardzewski_equivalence
    [StandardBorelSpace Ω]
    {α : Type*} [MeasurableSpace α] [StandardBorelSpace α] [Nonempty α]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ℕ → Ω → α) (hX_meas : ∀ (i : ℕ), Measurable (X i)) :
    Contractable μ X ↔ Exchangeable μ X ∧ ConditionallyIID μ X
```

**Statement:** For infinite sequences on standard Borel spaces:
```
Contractable ⟺ Exchangeable ⟺ Conditionally i.i.d.
```

This is Kallenberg's Theorem 1.1.

---

## Supporting Theorems

### `contractable_of_exchangeable`

**File:** `Exchangeability/Contractability.lean:486`

```lean
theorem contractable_of_exchangeable {μ : Measure Ω} {X : ℕ → Ω → α}
    (hX : Exchangeable μ X) (hX_meas : ∀ i, Measurable (X i)) : Contractable μ X
```

**Statement:** Every exchangeable sequence is contractable.

**Proof method:** Combinatorial - extends strictly monotone selections to full permutations.

---

### `exchangeable_of_conditionallyIID`

**File:** `Exchangeability/ConditionallyIID.lean:260`

```lean
theorem exchangeable_of_conditionallyIID {μ : Measure Ω} {X : ℕ → Ω → α}
    (hX_meas : ∀ i, Measurable (X i)) (hCIID : ConditionallyIID μ X) :
    Exchangeable μ X
```

**Statement:** Every conditionally i.i.d. sequence is exchangeable.

**Proof method:** Product measures are permutation-invariant.

---

### `conditionallyIID_of_contractable`

**File:** `Exchangeability/DeFinetti/TheoremViaMartingale.lean:70`

```lean
theorem conditionallyIID_of_contractable
    [StandardBorelSpace Ω]
    {α : Type*} [MeasurableSpace α] [StandardBorelSpace α] [Nonempty α]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ℕ → Ω → α) (hX_meas : ∀ i, Measurable (X i))
    (hContract : Contractable μ X) :
    ConditionallyIID μ X
```

**Statement:** Every contractable sequence is conditionally i.i.d.

**Proof method:** Reverse martingale convergence + tail σ-algebra factorization.

---

## Alternative Proof Routes

### Via L² (Elementary Bounds)

**File:** `Exchangeability/DeFinetti/TheoremViaL2.lean:135`

```lean
theorem conditionallyIID_of_contractable_viaL2
    [StandardBorelSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (hX_meas : ∀ i, Measurable (X i))
    (hContract : Contractable μ X)
    (hX_L2 : ∀ i, MemLp (X i) 2 μ) :
    ConditionallyIID μ X
```

**Requirements:** L² integrability (for bounded random variables or via truncation).

**Proof method:** Elementary L² bounds from Kallenberg Lemma 1.2.

---

### Via Koopman (Mean Ergodic Theorem)

**File:** `Exchangeability/DeFinetti/TheoremViaKoopman.lean:224`

```lean
theorem conditionallyIID_of_contractable_viaKoopman
    [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (hX_meas : ∀ i, Measurable (X i))
    (hContract : Contractable μ X)
    (hX_L2 : ∀ i, MemLp (X i) 2 μ) :
    ConditionallyIID μ X
```

**Requirements:** L² integrability.

**Proof method:** Mean Ergodic Theorem via Koopman operator.

---

## Type Signatures Summary

| Theorem | Input | Output |
|---------|-------|--------|
| `deFinetti` | `Exchangeable μ X` | `ConditionallyIID μ X` |
| `contractable_of_exchangeable` | `Exchangeable μ X` | `Contractable μ X` |
| `exchangeable_of_conditionallyIID` | `ConditionallyIID μ X` | `Exchangeable μ X` |
| `conditionallyIID_of_contractable` | `Contractable μ X` | `ConditionallyIID μ X` |

## Axioms Used

All theorems depend on exactly three standard mathlib axioms:
- `propext` (propositional extensionality)
- `Classical.choice` (axiom of choice)
- `Quot.sound` (quotient soundness)

No custom axioms are introduced.
