---
Repo: https://github.com/cameronfreer/exchangeability
Commit: aec253b69aaabbd93dd82fe1a7d9bbf34cf90ab5
Date: 2026-01-24
Built: yes
Lean: v4.27.0-rc1
Lake: v5.0.0-src+2fcce72
---

# Usability and API Examples

## Quick Start

### Import the Main Theorem

```lean
import Exchangeability.DeFinetti.Theorem

-- This imports the martingale proof as the default
-- All main theorems are in namespace Exchangeability.DeFinetti
```

### Basic Usage

```lean
variable {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω]
variable {α : Type*} [MeasurableSpace α] [StandardBorelSpace α] [Nonempty α]
variable {μ : Measure Ω} [IsProbabilityMeasure μ]
variable (X : ℕ → Ω → α) (hX_meas : ∀ i, Measurable (X i))

-- If X is exchangeable, it's conditionally i.i.d.
example (hExch : Exchangeable μ X) : ConditionallyIID μ X :=
  Exchangeability.DeFinetti.deFinetti X hX_meas hExch

-- The full equivalence
example : Exchangeable μ X ↔ ConditionallyIID μ X :=
  Exchangeability.DeFinetti.deFinetti_equivalence X hX_meas
```

## Available Entry Points

### Standard (Martingale Proof)

```lean
import Exchangeability.DeFinetti.Theorem
-- or equivalently:
import Exchangeability.DeFinetti.TheoremViaMartingale
```

Provides:
- `deFinetti` : Exchangeable → ConditionallyIID
- `deFinetti_equivalence` : Exchangeable ↔ ConditionallyIID
- `deFinetti_RyllNardzewski_equivalence` : Contractable ↔ Exchangeable ∧ ConditionallyIID
- `conditionallyIID_of_contractable` : Contractable → ConditionallyIID

### Alternative: L² Proof

```lean
import Exchangeability.DeFinetti.TheoremViaL2
```

Provides:
- `conditionallyIID_of_contractable_viaL2` : Contractable → ConditionallyIID (for ℝ-valued, L²)
- `deFinetti_viaL2` : Exchangeable → ConditionallyIID (for ℝ-valued, L²)

### Alternative: Koopman Proof

```lean
import Exchangeability.DeFinetti.TheoremViaKoopman
```

Provides:
- `conditionallyIID_of_contractable_viaKoopman` : Contractable → ConditionallyIID (for ℝ-valued, L²)

## Definition Access

### Core Definitions

```lean
import Exchangeability.Contractability

-- Access definitions
#check Exchangeability.Exchangeable      -- Finite permutation invariance
#check Exchangeability.FullyExchangeable -- All permutation invariance
#check Exchangeability.Contractable      -- Strictly monotone subsequence invariance
```

```lean
import Exchangeability.ConditionallyIID

#check ConditionallyIID  -- Existence of directing measure
```

## Theorem Signatures Quick Reference

### Main Theorem

```lean
theorem deFinetti
    [StandardBorelSpace Ω]
    {α : Type*} [MeasurableSpace α] [StandardBorelSpace α] [Nonempty α]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ℕ → Ω → α) (hX_meas : ∀ i, Measurable (X i))
    (hX_exch : Exchangeable μ X) :
    ConditionallyIID μ X
```

**What you need:**
1. `Ω` is a standard Borel space
2. `α` is a standard Borel space and nonempty
3. `μ` is a probability measure
4. Each `X i` is measurable
5. `X` is exchangeable

**What you get:**
- A directing measure `ν : Ω → Measure α`
- Each `ν ω` is a probability measure
- `ω ↦ (ν ω) B` is measurable for each measurable `B`
- Finite-dimensional distributions are product mixtures

### Easy Directions (Always Available)

```lean
-- Exchangeable → Contractable
theorem contractable_of_exchangeable
    {μ : Measure Ω} {X : ℕ → Ω → α}
    (hX : Exchangeable μ X) (hX_meas : ∀ i, Measurable (X i)) :
    Contractable μ X

-- ConditionallyIID → Exchangeable
theorem exchangeable_of_conditionallyIID
    {μ : Measure Ω} {X : ℕ → Ω → α}
    (hX_meas : ∀ i, Measurable (X i)) (hCIID : ConditionallyIID μ X) :
    Exchangeable μ X
```

## Working with ConditionallyIID

### Extracting the Directing Measure

```lean
variable (hCIID : ConditionallyIID μ X)

-- Get the directing measure
def ν : Ω → Measure α := hCIID.ν

-- It's a probability measure (for each ω)
example (ω : Ω) : IsProbabilityMeasure (ν ω) := hCIID.isProb ω

-- It's measurable in ω
example (B : Set α) (hB : MeasurableSet B) :
    Measurable (fun ω => (ν ω) B) := hCIID.measurable_eval B hB

-- The product formula holds
example (m : ℕ) (k : Fin m → ℕ) (hk : StrictMono k) :
    Measure.map (fun ω i => X (k i) ω) μ =
      μ.bind (fun ω => Measure.pi (fun _ => ν ω)) :=
  hCIID.finite_product m k hk
```

## Common Patterns

### Proving Exchangeability

To prove a sequence is exchangeable:

```lean
-- Method 1: Show it's conditionally i.i.d.
example (hCIID : ConditionallyIID μ X) : Exchangeable μ X :=
  exchangeable_of_conditionallyIID hX_meas hCIID

-- Method 2: Direct definition (check all finite permutations)
example : Exchangeable μ X := fun n σ => by
  -- Prove: Measure.map (fun ω i => X (σ i) ω) μ = Measure.map (fun ω i => X i ω) μ
  sorry
```

### Proving Contractability

To prove a sequence is contractable:

```lean
-- Method 1: Show it's exchangeable first
example (hExch : Exchangeable μ X) : Contractable μ X :=
  contractable_of_exchangeable hExch hX_meas

-- Method 2: Direct definition (check all strictly monotone subsequences)
example : Contractable μ X := fun m k hk => by
  -- Prove: Measure.map (fun ω i => X (k i) ω) μ = Measure.map (fun ω i => X i ω) μ
  sorry
```

## Tips

1. **Start with the main import:** Use `import Exchangeability.DeFinetti.Theorem` for most applications.

2. **Check state space requirements:** The main theorem requires `[StandardBorelSpace α]`. For concrete types like `ℝ`, `ℕ`, `Bool`, this is automatic.

3. **Measurability hypotheses:** Always carry `(hX_meas : ∀ i, Measurable (X i))` - it's needed for most lemmas.

4. **Opening namespaces:** Use `open Exchangeability Exchangeability.DeFinetti` for cleaner code.

5. **Alternative proofs:** The L² and Koopman proofs require L² integrability but may be useful for ℝ-valued sequences with explicit bounds.
