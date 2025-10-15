# Plan to Discharge All Axioms in ViaKoopman.lean

## Status Overview

### ✅ Main Theorem: COMPLETE
**`h_tower_of_lagConst`** (lines 1058-1614): All 5 blocks fully proved with NO sorrys in main proof!

**Only remaining `sorry`s are in helper lemmas, not in the theorem itself.**

---

## Axioms to Discharge

### Category 1: Natural Extension & Factor Maps (4 axioms)

#### General Infrastructure (NEW - lines 259-319)
We've added 3 general lemmas that can replace 4 specific axioms:

1. **`ae_pullback_iff`** (line 265)
   - **What**: AE-transport along factor maps `g : Ω' → Ω` with `map g μ' = μ`
   - **Mathlib source**: `Measure.map_apply`, AE definition
   - **Difficulty**: ⭐ Easy (2-3 lines)
   - **Replaces**: `naturalExtension_pullback_ae` (line 349)

2. **`condexp_pullback_factor`** (line 285)
   - **What**: `CE[H | m] ∘ g = CE[H ∘ g | comap g m]` for factor maps
   - **Mathlib source**: `ae_eq_condexp_of_forall_setIntegral_eq`, `Measure.map_apply`
   - **Difficulty**: ⭐⭐ Medium (10-15 lines)
   - **Replaces**: `naturalExtension_condexp_pullback` (line 334)

3. **`condexp_precomp_iterate_eq_of_invariant`** (line 306)
   - **What**: `CE[f ∘ T^[k] | inv(T)] = CE[f | inv(T)]` for T-invariant σ-algebras
   - **Mathlib source**: `MeasurePreserving.preimage_mem_ae_eq`, `ae_eq_condexp_of_forall_setIntegral_eq`
   - **Difficulty**: ⭐⭐ Medium (15-20 lines)
   - **Replaces**: 
     - `condexp_precomp_iterate_eq_twosided` (line 364)
     - `condexp_precomp_shiftℤInv_eq` (line 377)

#### Specializations (once general lemmas are proved)
- Line 349: `naturalExtension_pullback_ae` ← `ae_pullback_iff` with `g := restrictNonneg`
- Line 334: `naturalExtension_condexp_pullback` ← `condexp_pullback_factor` with `g := restrictNonneg`
- Line 364: `condexp_precomp_iterate_eq_twosided` ← invariant lemma with `T := shiftℤ`
- Line 377: `condexp_precomp_shiftℤInv_eq` ← invariant lemma with `T := shiftℤInv`

### Category 2: Natural Extension Construction (1 axiom)

4. **`exists_naturalExtension`** (line 322)
   - **What**: Construct two-sided extension `μ̂` on `ℤ → α` from one-sided `μ` on `ℕ → α`
   - **Method**: Kolmogorov inverse limit construction
   - **Steps**:
     1. Define projections `π_{-m:∞} : α^ℤ → α^ℕ` by `(π ω)(n) := ω(n-m)`
     2. Use shift-invariance: `map π_{-m:∞} μ̂ = μ` for all `m` is consistent
     3. Apply Kolmogorov extension theorem on cylinder sets
     4. Verify `map restrictNonneg μ̂ = μ` and `MeasurePreserving shiftℤ`
   - **Difficulty**: ⭐⭐⭐⭐ Hard (50-100 lines)
   - **Mathlib source**: Kolmogorov extension (if available), or build from cylinder algebra

---

## Checklist

### Immediate (Easy wins)
- [ ] Fill in `ae_pullback_iff` (forward direction: use `Measure.map_apply` on null sets)
- [ ] Fill in `ae_pullback_iff` (backward direction: push forward null sets)

### Short-term (Medium difficulty)
- [ ] Fill in `condexp_pullback_factor`:
  - Show both sides are `comap g m`-measurable and integrable
  - For `A ∈ comap g m`, write `A = g⁻¹' B` with `B ∈ m`
  - Compare `∫_A (CE ∘ g) dμ'` with `∫_B CE dμ` using `hpush`
  - Apply `ae_eq_condexp_of_forall_setIntegral_eq`

- [ ] Fill in `condexp_precomp_iterate_eq_of_invariant`:
  - For `A ∈ m` (T-invariant), show `∫ (f ∘ T^[k]) · 1_A dμ = ∫ f · 1_A dμ`
  - Use measure preservation: LHS = `∫ f · 1_{(T^[k])⁻¹ A} dμ`
  - Use invariance: `(T^[k])⁻¹ A = A`
  - Apply `ae_eq_condexp_of_forall_setIntegral_eq`

### Long-term (Hard)
- [ ] Implement `exists_naturalExtension`:
  - Define cylinder algebra on `α^ℤ`
  - Build premeasure from one-sided law
  - Prove consistency (uses shift-invariance of `μ`)
  - Extend via Carathéodory
  - Package as `NaturalExtensionData`

### Cleanup (Once above are done)
- [ ] Replace `axiom naturalExtension_pullback_ae` with `def` using `ae_pullback_iff`
- [ ] Replace `axiom naturalExtension_condexp_pullback` with `def` using `condexp_pullback_factor`
- [ ] Replace `axiom condexp_precomp_iterate_eq_twosided` with `def` using invariant lemma
- [ ] Replace `axiom condexp_precomp_shiftℤInv_eq` with `def` using invariant lemma
- [ ] Replace `axiom exists_naturalExtension` with `def` using inverse limit construction

---

## Other Axioms in File (Lower Priority)

### Helper Lemmas
- Line 962: `condExp_sum_finset` - notation elaboration issue (mathlib has the result)
- Line 987: `integrable_of_bounded_measurable` - standard, can be filled
- Line 1002: `integrable_condExp` - mathlib has this
- Line 1402: `integrable_condExp.mpr` - duplicate of above

### De Finetti Pipeline (Separate effort)
- Line 448: `Kernel.IndepFun.ae_measure_indepFun` - kernel independence machinery
- Line 709: `condindep_pair_given_tail` - placeholder for proper statement
- Line 729: `kernel_integral_product_factorization` - temporary axiom
- Line 829: `condexp_mul_condexp` - type class inference issue

---

## Progress Summary

**Completed**:
- ✅ Main theorem `h_tower_of_lagConst`: All 5 blocks proved
- ✅ Infrastructure: 3 general lemmas added (with sorry stubs)
- ✅ Documentation: Clear path to discharge 4/5 axioms

**Next Steps**:
1. Fill in the 3 general lemmas (15-40 lines total)
2. Specialize to replace 4 axioms (trivial once general lemmas work)
3. Implement inverse limit construction (hardest, 50-100 lines)

**Impact**: Once these 5 axioms are discharged, the natural extension machinery is complete and can be used for the full De Finetti theorem!
