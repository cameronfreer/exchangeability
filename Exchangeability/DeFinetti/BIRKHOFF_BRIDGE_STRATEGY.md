# Bridging birkhoffAverage and birkhoffAvgCLM: Technical Strategy

## Status: Infrastructure Complete, Bridge Needed

**Date**: 2025-11-16
**Context**: All Lp coercion infrastructure is complete. Need to connect mathlib's `birkhoffAverage` with our `birkhoffAvgCLM` to resolve ViaKoopman sorries.

---

## The Problem

### ViaKoopman Line 4043 Goal
```lean
⊢ AEMeasurable (fun ω => birkhoffAverage ℝ (⇑(koopman shift hσ)) (fun f => ↑↑f) n fL2 ω
                         - ↑↑(condexpL2 fL2) ω) μ
```

**Key observation**: Goal uses `(fun f => ↑↑f)` - the function-level coercion approach.

### Context Available in ViaKoopman
```lean
hB_eq_pos : ∀ (n : ℕ), 0 < n →
  (fun ω => ↑↑(birkhoffAverage ℝ (⇑(koopman shift hσ)) (fun f => f) n fL2) ω) =ᶠ[ae μ] B n

h_ae : (fun ω => |B n ω - Y ω|) =ᶠ[ae μ]
       (fun ω => |↑↑(birkhoffAverage ℝ (⇑(koopman shift hσ)) (fun f => f) n fL2) ω
                - ↑↑(condexpL2 fL2) ω|)
```

**Key observation**: Context uses `(fun f => f)` - the Lp-level approach.

### The Coercion Mismatch

The elaborator treats these differently:
- `↑↑(birkhoffAverage ℝ U (fun f => f) n g)` — Apply birkhoffAverage at Lp level, then coerce
- `birkhoffAverage ℝ U (fun f => ↑↑f) n g` — Coerce at each iteration, then average

**Mathematical truth**: These are equal a.e., but **not** definitionally equal.

---

## Infrastructure We've Built

### Complete Lp Coercion Chain (BirkhoffAvgCLM.lean)

All 4 lemmas proved (commits `58ab78c`, `44478bc`):

1. **`Lp.coeFn_smul' (c : ℝ) (f : Lp ℝ 2 μ)`**
   ```lean
   (↑↑(c • f) : Ω → ℝ) =ᵐ[μ] fun ω => c * (f : Ω → ℝ) ω
   ```

2. **`Lp.coeFn_sum' {ι : Type*} [Fintype ι] (fs : ι → Lp ℝ 2 μ)`**
   ```lean
   (↑↑(∑ i, fs i) : Ω → ℝ) =ᵐ[μ] fun ω => ∑ i, (fs i : Ω → ℝ) ω
   ```

3. **`EventuallyEq.sum' {fs gs : ι → Ω → ℝ} (h : ∀ i, fs i =ᵐ[μ] gs i)`**
   ```lean
   (fun ω => ∑ i, fs i ω) =ᵐ[μ] (fun ω => ∑ i, gs i ω)
   ```

4. **`birkhoffAvgCLM_coe_ae_eq_function_avg`** (Main application)
   ```lean
   ((birkhoffAvgCLM (koopman T hT_mp) n) fL2 : Ω → ℝ) =ᵐ[μ]
   (fun ω => if n = 0 then 0
             else (n : ℝ)⁻¹ * ∑ k : Fin n, (fL2 : Ω → ℝ) (T^[k] ω))
   ```

### Our Definitions

```lean
-- powCLM U k = U^[k] as a CLM
def powCLM (U : E →L[ℝ] E) : ℕ → (E →L[ℝ] E)
| 0     => ContinuousLinearMap.id ℝ E
| k + 1 => U.comp (powCLM U k)

-- birkhoffAvgCLM U n = (1/n) • ∑_{k=0}^{n-1} U^[k]
def birkhoffAvgCLM (U : E →L[ℝ] E) (n : ℕ) : E →L[ℝ] E :=
  if n = 0 then 0 else ((n : ℝ)⁻¹) • (∑ k : Fin n, powCLM U k)
```

---

## Mathlib's birkhoffAverage

### Type Signature
```lean
birkhoffAverage.{u_1, u_2, u_3}
  (R : Type u_1) {α : Type u_2} {M : Type u_3}
  [DivisionSemiring R] [AddCommMonoid M] [Module R M]
  (f : α → α) (g : α → M) (n : ℕ) (x : α) : M
```

### Definition (from Mathlib.Dynamics.BirkhoffSum.Average)
```lean
birkhoffAverage R f g n x = (n : R)⁻¹ • ∑ k ∈ Finset.range n, g (f^[k] x)
```

### Key Properties
- Works at **value level** (applies `g` at each iterate)
- Generic over module `M` (works for real numbers, Lp spaces, etc.)
- When `f = koopman T` and `g = id`, operates at **Lp level**
- When `f = koopman T` and `g = coercion`, operates at **function level**

---

## The Gap: Two Formulations

### Formulation A: Lp-Level (what context uses)
```lean
birkhoffAverage ℝ (koopman T hT_mp) (fun f => f) n fL2
```
- Type: `Lp ℝ 2 μ`
- Meaning: Average the Lp iterates, stay in Lp
- After coercion: `↑↑(birkhoffAverage ... (fun f => f) ... fL2) : Ω → ℝ`

### Formulation B: Function-Level (what goal uses)
```lean
birkhoffAverage ℝ (koopman T hT_mp) (fun f => ↑↑f) n fL2
```
- Type: `Ω → ℝ` (directly)
- Meaning: Coerce each iterate, then average the functions
- Direct function: `(fun ω => birkhoffAverage ... (fun f => ↑↑f) ... fL2 ω) : Ω → ℝ`

### The Connection Theorem We Need

```lean
lemma birkhoffAverage_coerce_eq_ae
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (T : Ω → Ω) (hT_meas : Measurable T) (hT_mp : MeasurePreserving T μ μ)
    (n : ℕ) (fL2 : Lp ℝ 2 μ) :
  (fun ω => birkhoffAverage ℝ (koopman T hT_mp) (fun f => ↑↑f) n fL2 ω) =ᵐ[μ]
  (fun ω => ↑↑(birkhoffAverage ℝ (koopman T hT_mp) (fun f => f) n fL2) ω) := by
  sorry
```

**This lemma would directly resolve ViaKoopman line 4043!**

---

## Strategy 1: Prove the Bridge Directly

### Approach
Show that the two formulations are equal a.e. by unfolding both sides and using our infrastructure.

### Proof Sketch
```lean
lemma birkhoffAverage_coerce_eq_ae ... := by
  by_cases hn : n = 0
  · -- Both sides are 0
    simp [birkhoffAverage]

  · -- n > 0 case
    unfold birkhoffAverage
    simp only [hn, if_false]

    -- LHS: birkhoffAverage with (fun f => ↑↑f)
    -- = (n⁻¹) • ∑ k : Fin n, ↑↑((koopman T)^[k] fL2)

    -- RHS: ↑↑(birkhoffAverage with (fun f => f))
    -- = ↑↑((n⁻¹) • ∑ k : Fin n, (koopman T)^[k] fL2)

    -- Use Lp.coeFn_smul' for scalar multiplication
    -- Use Lp.coeFn_sum' for sum
    -- Use powCLM_koopman_coe_ae for each iterate
```

### Required Mathlib API
Need to establish:
1. `koopman T` as CLM ✓ (already have)
2. `(koopman T)^[k]` equals `powCLM (koopman T) k` ✓ (have powCLM_apply)
3. Connection between `Finset.range n` and `Fin n` ✓ (mathlib has this)

### Blocking Issues
- **Type compatibility**: `birkhoffAverage` is generic, need to specialize to Lp
- **Finset.range vs Fin**: May need conversion lemmas
- **Extensionality**: Need to work pointwise a.e.

---

## Strategy 2: Use Measurability Directly

### Observation
Since both formulations should give Lp elements (or functions from Lp elements), they're AEStronglyMeasurable.

### Simpler Approach for ViaKoopman Line 4043
```lean
have h_meas : AEMeasurable (fun ω => ...) μ := by
  -- Goal has (fun f => ↑↑f), but we know this equals (fun f => f) version a.e.
  -- Both are Lp elements, so AEStronglyMeasurable when coerced
  apply AEMeasurable.sub
  · -- birkhoffAverage part
    apply Lp.aestronglyMeasurable.aemeasurable
    -- Need: birkhoffAverage ... returns Lp element
    sorry
  · -- condexpL2 part
    exact Lp.aestronglyMeasurable.aemeasurable
```

**Problem**: Need to show `birkhoffAverage ℝ (koopman T) (fun f => ↑↑f) n fL2` is AEMeasurable.

**Better approach**: Show it equals the `(fun f => f)` version a.e., which is manifestly in Lp.

---

## Strategy 3: Extend birkhoffAvgCLM Infrastructure

### Add Bridge Lemma to BirkhoffAvgCLM.lean

```lean
/-- Mathlib's birkhoffAverage with Lp identity equals our CLM formulation. -/
lemma birkhoffAverage_lp_eq_birkhoffAvgCLM
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (T : Ω → Ω) (hT_mp : MeasurePreserving T μ μ)
    (n : ℕ) (fL2 : Lp ℝ 2 μ) :
  birkhoffAverage ℝ (koopman T hT_mp) (fun f => f) n fL2 =
  (birkhoffAvgCLM (koopman T hT_mp) n) fL2 := by
  unfold birkhoffAverage birkhoffAvgCLM
  by_cases hn : n = 0
  · simp [hn]
  · simp only [hn, if_false]
    -- Show ∑ k ∈ Finset.range n, ... = ∑ k : Fin n, ...
    -- Use powCLM_apply
    sorry
```

Then use `birkhoffAvgCLM_coe_ae_eq_function_avg` to get the coercion equality.

---

## Recommended Implementation Plan

### Phase 1: Establish Equivalence (30-60 min)
1. **Add to BirkhoffAvgCLM.lean**:
   ```lean
   lemma birkhoffAverage_lp_eq_birkhoffAvgCLM ...
   ```
   - Unfold both sides
   - Show sum over `Finset.range n` equals sum over `Fin n`
   - Use `powCLM_apply` for iterate equivalence

2. **Compose with existing infrastructure**:
   ```lean
   lemma birkhoffAverage_coerce_eq_ae ... := by
     conv_lhs =>
       rw [show (fun ω => birkhoffAverage ... (fun f => ↑↑f) ... ω) =
               (fun ω => ...) from ...]
     rw [← birkhoffAverage_lp_eq_birkhoffAvgCLM]
     exact birkhoffAvgCLM_coe_ae_eq_function_avg ...
   ```

### Phase 2: Apply to ViaKoopman (15-30 min)
1. **At line 4043**:
   ```lean
   have h_meas : AEMeasurable ... := by
     have h_eq := birkhoffAverage_coerce_eq_ae T hT_meas hT_mp n fL2
     -- Use a.e. equality to transfer measurability
     apply AEMeasurable.congr _ h_eq.symm
     -- Show the (fun f => f) version is measurable (it's in Lp)
     apply AEMeasurable.sub <;> exact Lp.aestronglyMeasurable.aemeasurable
   ```

2. **Cascade fix lines 4065, 4081**:
   - Line 4065 (`h_le`): Should resolve once `h_meas` is proved
   - Line 4081 (`h_toNorm`): Uses same equality, similar approach

---

## Technical Notes

### Finset.range vs Fin Conversion
```lean
-- Mathlib has:
Finset.sum_range : ∑ i ∈ Finset.range n, f i = ∑ i : Fin n, f i.val

-- May need:
lemma finset_range_eq_fin_sum {β : Type*} [AddCommMonoid β] (f : ℕ → β) (n : ℕ) :
    ∑ k ∈ Finset.range n, f k = ∑ k : Fin n, f k := by
  rw [Finset.sum_range]
  congr 1
  ext k
  simp
```

### Koopman Iteration
```lean
-- We have:
lemma powCLM_apply (U : E →L[ℝ] E) (k : ℕ) (v : E) :
    (powCLM U k) v = (U^[k]) v

-- For koopman:
(powCLM (koopman T hT_mp) k) fL2 = (koopman T hT_mp)^[k] fL2
```

### A.e. Equality Transfer
```lean
-- Mathlib has:
AEMeasurable.congr {f g : α → β} (hf : AEMeasurable f μ) (h : f =ᵐ[μ] g) :
  AEMeasurable g μ
```

---

## Estimated Effort

### If Finset.range conversion is smooth:
- **Phase 1**: 1-2 hours
  - `birkhoffAverage_lp_eq_birkhoffAvgCLM`: 30-45 min
  - `birkhoffAverage_coerce_eq_ae`: 30-45 min
  - Testing/debugging: 15-30 min

- **Phase 2**: 30 min
  - Apply to `h_meas`: 10 min
  - Fix cascading sorries: 20 min

**Total**: 1.5-2.5 hours

### If Finset.range conversion is tricky:
- Additional 1-2 hours for auxiliary lemmas
**Total**: 2.5-4.5 hours

---

## Alternative: Axiomatize the Bridge

If the proof is more complex than expected:

```lean
axiom birkhoffAverage_coerce_eq_ae
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (T : Ω → Ω) (hT_meas : Measurable T) (hT_mp : MeasurePreserving T μ μ)
    (n : ℕ) (fL2 : Lp ℝ 2 μ) :
  (fun ω => birkhoffAverage ℝ (koopman T hT_mp) (fun f => ↑↑f) n fL2 ω) =ᵐ[μ]
  (fun ω => ↑↑(birkhoffAverage ℝ (koopman T hT_mp) (fun f => f) n fL2) ω)
```

**Justification**: This is mathematically obvious (both compute the same Cesàro average), and we have all the infrastructure to prove it. The axiom just defers the routine technical work.

---

## Files to Modify

1. **Exchangeability/Ergodic/BirkhoffAvgCLM.lean**
   - Add `birkhoffAverage_lp_eq_birkhoffAvgCLM`
   - Add `birkhoffAverage_coerce_eq_ae`
   - Location: After `birkhoffAvgCLM_coe_ae_eq_function_avg` (line ~270)

2. **Exchangeability/DeFinetti/ViaKoopman.lean**
   - Fix line 4043 (`h_meas`)
   - Remove sorries at lines 4065, 4081 (should auto-resolve)
   - Location: Lines 4032-4089

---

## Success Criteria

✅ `birkhoffAverage_lp_eq_birkhoffAvgCLM` proves definitional equality at Lp level
✅ `birkhoffAverage_coerce_eq_ae` proves a.e. equality after coercion
✅ ViaKoopman line 4043 resolved using measurability transfer
✅ ViaKoopman lines 4065, 4081 resolve cascadingly
✅ ViaKoopman builds successfully (3216 jobs)
✅ No new axioms introduced (or documented if axiomatized)

---

## References

- **BirkhoffAvgCLM.lean**: Lines 12-36 (file header explaining the coercion mismatch)
- **BirkhoffAvgCLM.lean**: Lines 229-270 (`birkhoffAvgCLM_coe_ae_eq_function_avg` proof)
- **ViaKoopman.lean**: Lines 4032-4089 (the problematic proof section)
- **Mathlib**: `Mathlib.Dynamics.BirkhoffSum.Average` (birkhoffAverage definition)
- **Session docs**: `SESSION_2025_11_16_CONTINUED.md` (infrastructure completion)

---

**Last Updated**: 2025-11-16
**Status**: Infrastructure complete, bridge strategy documented
**Next Session**: Implement Phase 1 of the bridge strategy
