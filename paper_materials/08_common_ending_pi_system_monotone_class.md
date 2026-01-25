---
Repo: https://github.com/human-oriented/exchangeability
Commit: aec253b69aaabbd93dd82fe1a7d9bbf34cf90ab5
Date: 2026-01-24
Built: yes
Lean: v4.27.0-rc1
Lake: v5.0.0-src+2fcce72
---

# Common Ending: π-System and Monotone Class Extension

## Overview

All three proof routes share a common final step: extending the finite-dimensional product formula from cylinder sets to all Borel sets using the **π-system uniqueness theorem** (also known as the monotone class theorem).

**Main file:** `Exchangeability/DeFinetti/CommonEnding.lean`

## Mathematical Background

### π-System Uniqueness (Dynkin's π-λ Theorem)

If two finite measures agree on a π-system that generates the σ-algebra, then they agree on the entire σ-algebra.

**Formal statement:** Let `𝒫` be a π-system (closed under finite intersections) that generates a σ-algebra `ℱ`. If `μ` and `ν` are finite measures with `μ(A) = ν(A)` for all `A ∈ 𝒫`, then `μ = ν` on `ℱ`.

### Application to de Finetti

The proof routes establish the product formula:
```
∫ ∏ᵢ fᵢ(Xᵢ) dμ = ∫ (∏ᵢ ∫ fᵢ dν(ω)) dμ(ω)
```

for **cylinder sets** (sets depending on finitely many coordinates). The π-system extension upgrades this to:
```
Law(X_0, X_1, ..., X_{n-1}) = ∫ ν^⊗n dμ
```

for all Borel sets.

## Key Structures

### Prefix Cylinders

**File:** `Exchangeability/Core.lean`

```lean
/-- Projection to the first n coordinates. -/
def prefixProj (α : Type*) (n : ℕ) (x : ℕ → α) : Fin n → α :=
  fun i => x i

/-- Cylinder set determined by the first n coordinates. -/
def prefixCylinder {n : ℕ} (S : Set (Fin n → α)) : Set (ℕ → α) :=
  (prefixProj α n) ⁻¹' S
```

### π-System Property

```lean
/-- Prefix cylinders form a π-system. -/
theorem prefixCylinders_isPiSystem :
    IsPiSystem { C : Set (ℕ → α) | ∃ n S, MeasurableSet S ∧ C = prefixCylinder S }
```

### Generator Property

```lean
/-- Prefix cylinders generate the product σ-algebra. -/
theorem measurableSpace_eq_generateFrom_prefixCylinders :
    ‹MeasurableSpace (ℕ → α)› =
      MeasurableSpace.generateFrom { C | ∃ n S, MeasurableSet S ∧ C = prefixCylinder S }
```

## Tail σ-Algebra Structures

**File:** `Exchangeability/DeFinetti/CommonEnding.lean`

### Invariant σ-Field

```lean
/-- The invariant σ-field ℐ consists of all measurable shift-invariant sets. -/
def invariantSigmaField (α : Type*) [MeasurableSpace α] : MeasurableSpace (ℕ → α) :=
  MeasurableSpace.comap shift inferInstance
```

### Tail σ-Algebra

```lean
/-- The tail σ-algebra for infinite sequences. -/
def tailSigmaAlgebra (α : Type*) [MeasurableSpace α] : MeasurableSpace (ℕ → α) :=
  Exchangeability.Tail.tailShift α  -- = ⨅ n, comap (shift^n) inferInstance
```

### Tail Measurability

```lean
/-- A function is tail-measurable if measurable w.r.t. tail σ-algebra. -/
def IsTailMeasurable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (f : (ℕ → α) → β) : Prop :=
  @Measurable (ℕ → α) β (tailSigmaAlgebra α) _ f
```

## Key Lemmas

### Finite-Dimensional Product Formula

```lean
theorem finite_product_formula
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → α}
    (hContract : Contractable μ X)
    (ν : Ω → Measure α)
    (hν_prob : ∀ ω, IsProbabilityMeasure (ν ω))
    (hν_meas : ∀ B, MeasurableSet B → Measurable (fun ω => (ν ω) B))
    (hν_cond : (* conditional law equals ν *))
    (m : ℕ) (k : Fin m → ℕ) (hk : StrictMono k) :
    Measure.map (fun ω i => X (k i) ω) μ =
      μ.bind (fun ω => Measure.pi (fun _ => ν ω))
```

### Indicator Boundedness

```lean
lemma indicator_bounded {α : Type*} {s : Set α} :
    ∃ M : ℝ, ∀ x, |s.indicator (fun _ => (1 : ℝ)) x| ≤ M
```

### Measure Extension

```lean
theorem measure_eq_of_fin_marginals_eq
    {μ ν : Measure (ℕ → α)} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : ∀ n S, MeasurableSet S → μ (prefixCylinder S) = ν (prefixCylinder S)) :
    μ = ν
```

## Proof Structure

### Step 1: Verify Agreement on Indicators

For each cylinder set `C = {x | (x_0, ..., x_{n-1}) ∈ S}`:

```
μ(C) = ∫ 1_S(X_0, ..., X_{n-1}) dμ
     = ∫ (∏ᵢ ∫ 1_{Sᵢ} dν(ω)) dμ(ω)  [by product factorization]
     = ∫ ν^⊗n(S) dμ(ω)
     = (μ.bind (ω ↦ ν^⊗n))(C)
```

### Step 2: Apply π-System Uniqueness

Since cylinder sets form a π-system generating the product σ-algebra:

```
Measure.map (X_0, ..., X_{n-1}) μ = μ.bind (ω ↦ ν^⊗n)
```

on all Borel sets.

### Step 3: Package as ConditionallyIID

The equality for all finite-dimensional distributions gives `ConditionallyIID μ X`.

## mathlib Integration

### Key mathlib Theorems Used

| Theorem | Purpose |
|---------|---------|
| `Measure.ext_of_generate_finite` | π-system uniqueness |
| `IsPiSystem` | π-system definition |
| `MeasurableSpace.generateFrom` | Generated σ-algebra |
| `Measure.bind` | Giry monad composition |
| `Measure.pi` | Finite product measures |

### Imports

```lean
import Mathlib.MeasureTheory.PiSystem
import Mathlib.Probability.Kernel.Basic
import Mathlib.MeasureTheory.Constructions.Cylinders
```

## Relationship to Kolmogorov Extension

The π-system approach is related to but distinct from **Kolmogorov's extension theorem**:

- **Kolmogorov extension:** Constructs a measure from consistent finite-dimensional marginals
- **π-system uniqueness:** Proves equality of two existing measures

For de Finetti, we already have the measure `μ`; we need to prove it equals the mixture. The π-system approach is more direct.

## Connection to Exchangeability ↔ Full Exchangeability

**File:** `Exchangeability/Core.lean`

The same π-system technique proves that exchangeability (finite permutations) implies full exchangeability (all permutations):

```lean
theorem exchangeable_iff_fullyExchangeable
    {μ : Measure (ℕ → α)} [IsProbabilityMeasure μ]
    (X : ℕ → (ℕ → α) → α) (hX : ∀ i, Measurable (X i)) :
    Exchangeable μ X ↔ FullyExchangeable μ X
```

The proof shows that any infinite permutation can be approximated by finite permutations on cylinder sets.
