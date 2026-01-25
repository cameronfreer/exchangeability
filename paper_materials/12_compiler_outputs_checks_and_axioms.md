---
Repo: https://github.com/human-oriented/exchangeability
Commit: aec253b69aaabbd93dd82fe1a7d9bbf34cf90ab5
Date: 2026-01-24
Built: yes
Lean: v4.27.0-rc1
Lake: v5.0.0-src+2fcce72
---

# Compiler Outputs, Checks, and Axioms

## Build Status

```bash
$ lake build
Build completed successfully (3296 jobs).
```

**Build time:** ~5 minutes 12 seconds

## Main Theorem Signatures

### `deFinetti`

```lean
@deFinetti : ∀ {Ω : Type u_1} [inst : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {α : Type u_2} [inst_2 : MeasurableSpace α] [StandardBorelSpace α] [Nonempty α]
  {μ : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure μ]
  (X : ℕ → Ω → α),
  (∀ (i : ℕ), Measurable (X i)) → Exchangeable μ X → ConditionallyIID μ X
```

### `deFinetti_equivalence`

```lean
@deFinetti_equivalence : ∀ {Ω : Type u_1} [inst : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {α : Type u_2} [inst_2 : MeasurableSpace α] [StandardBorelSpace α] [Nonempty α]
  {μ : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure μ]
  (X : ℕ → Ω → α),
  (∀ (i : ℕ), Measurable (X i)) → (Exchangeable μ X ↔ ConditionallyIID μ X)
```

### `deFinetti_RyllNardzewski_equivalence`

```lean
@deFinetti_RyllNardzewski_equivalence : ∀ {Ω : Type u_1} [inst : MeasurableSpace Ω]
  [StandardBorelSpace Ω] {α : Type u_2} [inst_2 : MeasurableSpace α]
  [StandardBorelSpace α] [Nonempty α] {μ : MeasureTheory.Measure Ω}
  [MeasureTheory.IsProbabilityMeasure μ] (X : ℕ → Ω → α),
  (∀ (i : ℕ), Measurable (X i)) →
    (Contractable μ X ↔ Exchangeable μ X ∧ ConditionallyIID μ X)
```

### Alternative Proofs

```lean
@conditionallyIID_of_contractable_viaL2 : ∀ {Ω : Type u_1} [inst : MeasurableSpace Ω]
  [StandardBorelSpace Ω] (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ]
  (X : ℕ → Ω → ℝ),
  (∀ (i : ℕ), Measurable (X i)) → Contractable μ X →
    (∀ (i : ℕ), MeasureTheory.MemLp (X i) 2 μ) → ConditionallyIID μ X

@conditionallyIID_of_contractable_viaKoopman : ∀ {Ω : Type u_1} [inst : MeasurableSpace Ω]
  (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ]
  (X : ℕ → Ω → ℝ),
  (∀ (i : ℕ), Measurable (X i)) → Contractable μ X →
    (∀ (i : ℕ), MeasureTheory.MemLp (X i) 2 μ) → ConditionallyIID μ X
```

## Core Definitions (#print output)

### Exchangeable

```lean
def Exchangeability.Exchangeable.{u_1, u_2} : {Ω : Type u_1} → {α : Type u_2} →
  [inst : MeasurableSpace Ω] → [MeasurableSpace α] →
  MeasureTheory.Measure Ω → (ℕ → Ω → α) → Prop :=
fun {Ω} {α} [MeasurableSpace Ω] [MeasurableSpace α] μ X =>
  ∀ (n : ℕ) (σ : Equiv.Perm (Fin n)),
    MeasureTheory.Measure.map (fun ω i => X (↑(σ i)) ω) μ =
      MeasureTheory.Measure.map (fun ω i => X (↑i) ω) μ
```

### FullyExchangeable

```lean
def Exchangeability.FullyExchangeable.{u_1, u_2} : {Ω : Type u_1} → {α : Type u_2} →
  [inst : MeasurableSpace Ω] → [MeasurableSpace α] →
  MeasureTheory.Measure Ω → (ℕ → Ω → α) → Prop :=
fun {Ω} {α} [MeasurableSpace Ω] [MeasurableSpace α] μ X =>
  ∀ (π : Equiv.Perm ℕ),
    MeasureTheory.Measure.map (fun ω i => X (π i) ω) μ =
      MeasureTheory.Measure.map (fun ω i => X i ω) μ
```

### Contractable

```lean
def Exchangeability.Contractable.{u_1, u_2} : {Ω : Type u_1} → {α : Type u_2} →
  [inst : MeasurableSpace Ω] → [MeasurableSpace α] →
  MeasureTheory.Measure Ω → (ℕ → Ω → α) → Prop :=
fun {Ω} {α} [MeasurableSpace Ω] [MeasurableSpace α] μ X =>
  ∀ (m : ℕ) (k : Fin m → ℕ), StrictMono k →
    MeasureTheory.Measure.map (fun ω i => X (k i) ω) μ =
      MeasureTheory.Measure.map (fun ω i => X (↑i) ω) μ
```

### ConditionallyIID

```lean
def Exchangeability.ConditionallyIID.{u_1, u_2} : {Ω : Type u_1} → {α : Type u_2} →
  [inst : MeasurableSpace Ω] → [MeasurableSpace α] →
  MeasureTheory.Measure Ω → (ℕ → Ω → α) → Prop :=
fun {Ω} {α} [MeasurableSpace Ω] [MeasurableSpace α] μ X =>
  ∃ ν,
    (∀ (ω : Ω), MeasureTheory.IsProbabilityMeasure (ν ω)) ∧
    (∀ (B : Set α), MeasurableSet B → Measurable fun ω => (ν ω) B) ∧
    ∀ (m : ℕ) (k : Fin m → ℕ), StrictMono k →
      MeasureTheory.Measure.map (fun ω i => X (k i) ω) μ =
        μ.bind fun ω => MeasureTheory.Measure.pi fun x => ν ω
```

## Axiom Checks (#print axioms)

### Main Theorem (Martingale Proof)

```lean
#print axioms Exchangeability.DeFinetti.deFinetti
'Exchangeability.DeFinetti.deFinetti' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### Full Equivalence

```lean
#print axioms Exchangeability.DeFinetti.deFinetti_RyllNardzewski_equivalence
'Exchangeability.DeFinetti.deFinetti_RyllNardzewski_equivalence' depends on axioms:
  [propext, Classical.choice, Quot.sound]
```

### L² Proof

```lean
#print axioms Exchangeability.DeFinetti.conditionallyIID_of_contractable_viaL2
'Exchangeability.DeFinetti.conditionallyIID_of_contractable_viaL2' depends on axioms:
  [propext, Classical.choice, Quot.sound]
```

### Koopman Proof

```lean
#print axioms Exchangeability.DeFinetti.conditionallyIID_of_contractable_viaKoopman
'Exchangeability.DeFinetti.conditionallyIID_of_contractable_viaKoopman' depends on axioms:
  [propext, Classical.choice, Quot.sound]
```

## Axiom Analysis

### Axioms Used

| Axiom | Description | Necessity |
|-------|-------------|-----------|
| `propext` | Propositional extensionality | Standard, unavoidable |
| `Classical.choice` | Axiom of choice | Required for measure theory |
| `Quot.sound` | Quotient soundness | Standard for quotients |

### Axioms NOT Used

- No custom axioms (`axiom` declarations)
- No `sorry` in final theorems
- No `Axiom.choice` variants beyond standard mathlib

### Verification Command

```lean
-- In paper_materials/PaperIntrospection.lean
#print axioms Exchangeability.DeFinetti.deFinetti
```

## Build Warnings Summary

The build produces warnings but no errors:

| Category | Count | Impact |
|----------|-------|--------|
| Unused section variables | ~20 | None (style) |
| Deprecated lemma names | ~15 | None (mathlib evolution) |
| Unused simp arguments | ~25 | None (style) |
| simpa vs simp suggestions | ~10 | None (style) |

**All warnings are benign** - they relate to style and mathlib API evolution, not correctness.

## Introspection File

**File:** `paper_materials/PaperIntrospection.lean`

```lean
import Exchangeability.DeFinetti.Theorem
import Exchangeability.DeFinetti.TheoremViaL2
import Exchangeability.DeFinetti.TheoremViaKoopman

#check @Exchangeability.DeFinetti.deFinetti
#check @Exchangeability.DeFinetti.deFinetti_equivalence
#check @Exchangeability.DeFinetti.deFinetti_RyllNardzewski_equivalence
#check @Exchangeability.DeFinetti.conditionallyIID_of_contractable

#print Exchangeability.Exchangeable
#print Exchangeability.Contractable
#print ConditionallyIID

#print axioms Exchangeability.DeFinetti.deFinetti
#print axioms Exchangeability.DeFinetti.deFinetti_RyllNardzewski_equivalence
```

**Run with:**
```bash
lake env lean paper_materials/PaperIntrospection.lean
```
