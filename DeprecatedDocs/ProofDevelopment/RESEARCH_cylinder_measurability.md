# Research: Cylinder Set Measurability in Lean 4

**Goal:** Prove measurability of cylinder set in ViaMartingale.lean line 1799

**Date:** 2025-10-13

## Problem Statement

Need to prove:
```lean
S_std : Set (Fin (r + 1 + k) → α) :=
  {f | (∀ i : Fin r, f ⟨i.val, _⟩ ∈ A i) ∧ f ⟨r, _⟩ ∈ B ∧ (∀ j : Fin k, f ⟨r+1+j.val, _⟩ ∈ C j)}

have hS_meas : MeasurableSet S_std := by ...
```

Where:
- `A : Fin r → Set α` with `hA : ∀ i, MeasurableSet (A i)`
- `B : Set α` with `hB : MeasurableSet B`
- `C : Fin k → Set α` with `hC : ∀ i, MeasurableSet (C i)`

## Mathlib API: Set.pi and MeasurableSet.pi

### Definition (from Data/Set/Operations.lean:229)

```lean
def Set.pi (s : Set ι) (t : ∀ i, Set (α i)) : Set (∀ i, α i) :=
  {f | ∀ i ∈ s, f i ∈ t i}
```

**Meaning:** `s.pi t` is the set of functions `f` such that `f i ∈ t i` for all `i ∈ s`.

### Main Measurability Theorem (from MeasureTheory/MeasurableSpace/Constructions.lean:700)

```lean
protected theorem MeasurableSet.pi
    {s : Set δ} {t : ∀ i : δ, Set (X i)}
    (hs : s.Countable)
    (ht : ∀ i ∈ s, MeasurableSet (t i)) :
    MeasurableSet (s.pi t)
```

**Key requirements:**
1. Index set `s` must be countable
2. Each coordinate set `t i` must be measurable for `i ∈ s`

**Proof method:** Uses `measurable_pi_apply` for each coordinate

### Special Case: univ_pi (line 705)

```lean
protected theorem MeasurableSet.univ_pi [Countable δ]
    {t : ∀ i : δ, Set (X i)}
    (ht : ∀ i, MeasurableSet (t i)) :
    MeasurableSet (pi univ t)
```

When all coordinates are constrained (s = univ).

## Application Strategy for S_std

### Challenge: S_std is NOT in pi form directly

S_std constraints:
- First `r` coordinates: `f ⟨i, _⟩ ∈ A i` for `i : Fin r`
- Coordinate `r`: `f ⟨r, _⟩ ∈ B`
- Last `k` coordinates: `f ⟨r+1+j, _⟩ ∈ C j` for `j : Fin k`

This is equivalent to:
```lean
{f | ∀ i : Fin (r+1+k), f i ∈ (combined constraint on coordinate i)}
```

### Solution Approach 1: Express as univ.pi

Define a function `t : Fin (r+1+k) → Set α` where:
```lean
t i = if h : i.val < r then
        A ⟨i.val, by omega⟩
      else if i.val = r then
        B
      else
        C ⟨i.val - r - 1, by omega⟩
```

Then:
```lean
S_std = univ.pi t
```

Use `MeasurableSet.univ_pi` with `Fin (r+1+k)` countable.

**Proof structure:**
```lean
have hS_meas : MeasurableSet S_std := by
  -- Define t : Fin (r+1+k) → Set α
  let t : Fin (r+1+k) → Set α := fun i =>
    if h : i.val < r then A ⟨i.val, by omega⟩
    else if i.val = r then B
    else C ⟨i.val - r - 1, by omega⟩

  -- Show S_std = univ.pi t
  have h_eq : S_std = univ.pi t := by
    ext f
    simp only [S_std, Set.mem_pi, Set.mem_univ, true_implies]
    constructor
    · intro ⟨hA, hB, hC⟩ i
      simp only [t]
      split_ifs with h1 h2
      · exact hA ⟨i.val, by omega⟩
      · subst h2; exact hB
      · exact hC ⟨i.val - r - 1, by omega⟩
    · intro h
      refine ⟨?_, ?_, ?_⟩
      · intro i; exact h ⟨i.val, by omega⟩
      · exact h ⟨r, by omega⟩
      · intro j; exact h ⟨r + 1 + j.val, by omega⟩

  rw [h_eq]

  -- Apply MeasurableSet.univ_pi
  apply MeasurableSet.univ_pi
  intro i
  simp only [t]
  split_ifs with h1 h2
  · exact hA ⟨i.val, by omega⟩
  · exact hB
  · exact hC ⟨i.val - r - 1, by omega⟩
```

### Solution Approach 2: Intersection decomposition

Express as intersection:
```lean
S_std = (⋂ i : Fin r, {f | f ⟨i, _⟩ ∈ A i}) ∩
        {f | f ⟨r, _⟩ ∈ B} ∩
        (⋂ j : Fin k, {f | f ⟨r+1+j, _⟩ ∈ C j})
```

Use:
- `MeasurableSet.iInter` for finite intersections
- `measurable_pi_apply` for each coordinate preimage

**Proof structure:**
```lean
have hS_meas : MeasurableSet S_std := by
  -- Express as intersection
  have h_decomp : S_std =
      (⋂ i : Fin r, {f | f ⟨i.val, by omega⟩ ∈ A i}) ∩
      {f | f ⟨r, by omega⟩ ∈ B} ∩
      (⋂ j : Fin k, {f | f ⟨r+1+j.val, by omega⟩ ∈ C j}) := by
    ext f; simp only [Set.mem_iInter, Set.mem_inter_iff, Set.mem_setOf]; rfl

  rw [h_decomp]
  apply MeasurableSet.inter
  · apply MeasurableSet.inter
    · apply MeasurableSet.iInter; intro i
      exact measurable_pi_apply ⟨i.val, by omega⟩ (hA i)
    · exact measurable_pi_apply ⟨r, by omega⟩ hB
  · apply MeasurableSet.iInter; intro j
    exact measurable_pi_apply ⟨r+1+j.val, by omega⟩ (hC j)
```

## Comparison of Approaches

| Approach | Pros | Cons |
|----------|------|------|
| **univ.pi** | • Clean API match<br>• Single theorem application | • Requires defining piecewise `t`<br>• Complex case splits in equality proof |
| **iInter decomposition** | • Direct from definition<br>• No piecewise functions | • Requires manual intersection proofs<br>• More verbose |

## Recommended: Approach 1 (univ.pi)

**Rationale:**
1. Cleaner use of mathlib API
2. Single `MeasurableSet.univ_pi` application
3. Case split in `t` definition is localized

**Estimated time:** 20-30 minutes (mostly the equality proof ext/simp)

## Common Pitfalls (from previous attempts)

1. **Anonymous function type inference:**
   ```lean
   -- ❌ WRONG: Type of f not inferred
   let S_A := ⋂ i, (fun f => f i) ⁻¹' (A i)

   -- ✅ RIGHT: Use named definition
   let t : Fin n → Set α := ...
   ```

2. **Fin construction in lambdas:**
   ```lean
   -- ❌ WRONG: Anonymous constructor fails
   measurable_pi_apply ⟨i.val, proof⟩ (hA i)

   -- ✅ RIGHT: Use Fin.mk
   measurable_pi_apply (Fin.mk i.val proof) (hA i)
   ```

3. **Set.mem_pi requires univ for universal quantification:**
   ```lean
   -- For all coordinates: use univ.pi, not manual set-builder
   ```

## Next Steps

1. Implement Approach 1 with `univ.pi` (~20-30 min)
2. Test with `lake build`
3. If ext/simp gets stuck, try manual constructor proofs
4. Alternative: Fall back to Approach 2 if Approach 1 proves difficult

## References

- `Mathlib/MeasureTheory/MeasurableSpace/Constructions.lean:700-709`
- `Mathlib/Data/Set/Operations.lean:229`
- Instance: `Fin n` is `Countable` (required for `univ_pi`)
