# ViaKoopman.lean - Next Steps

**Status as of 2025-10-29**: L² → L¹ conversion patch (Step 3b) now compiles successfully after fixing API issues.

---

## Priority 1: Remaining Sorries

From build output, there are **~3-4 sorries** still in the file:

1. **Line 1901** - In ergodic/Koopman section
2. **Line 2330** - In dyadic approximation section
3. **Line 4372** - In Step 4c triangle inequality helper
4. **Possibly line 4497** - In the main theorem's Step 3a (birkhoffAverage = B_n conversion)

**Most critical**: **Line 4497** since it's in the main theorem's proof chain.

---

## Priority 2: Pre-existing Compilation Errors

Several errors existed before the recent L² → L¹ work:

- **Lines 40, 588, 583** - Unrelated to Step 3b/4a work
- **Lines 619, 640, 667, 716, 830, 833** - Pre-existing issues
- **Line 3873** - EventuallyEq application error
- **Line 4183** - ContinuousMul typeclass issue
- **Line 4558** - StandardBorelSpace metavariable issue

These appear to be **independent of the L² → L¹ work** and may require separate investigation.

---

## Priority 3: Code Quality Improvements

From linter warnings:

1. **Line 4523** - Unused tactic (`exact h1.trans h2` does nothing)
2. **Lines 4060-4061** - Replace failing `ring` with `ring_nf`
3. **Lines 4325, 4351** - Replace `simpa` with `simp`
4. **Line 4203** - Unused variable `hG_int`

---

## Priority 4: Axiom Elimination (Long-term)

Per earlier guidance: "8+ axiomatized lemmas" should be:

1. **Fenced in a section** (e.g., `section AxiomsForNaturalExtension`)
2. **Inlined where possible** (thin wrappers around mathlib facts)
3. **Deferred for deep ones** (existence results, ergodic decomposition)

---

## Recommended Order

1. ✅ **Fix line 4497 sorry** (blocks main theorem completion) - **CRITICAL PATH**
2. ✅ **Fix line 4372 sorry** (in Step 4c helper) - **CRITICAL PATH**
3. **Address unused tactic at 4523** (quick win)
4. **Investigate line 4183 ContinuousMul issue** (might block other work)
5. **Tackle remaining sorries** (lines 1901, 2330)
6. **Pre-existing errors audit** (lines 40, 588, etc.) - determine if they're blockers
7. **Axiom inventory and fencing** (longer-term refactoring)

---

## Critical Path to Working Proof

**Sorries 4497 → 4372 → Verify main theorem compiles**

Once these two sorries are resolved, the main `deFinetti_viaKoopman` theorem should be complete and verifiable.

---

## Recent Completed Work (2025-10-29)

### ✅ Fixed Issues

1. **Line 4532**: Trivial bound `|g (ω 0)| ≤ Cg`
   - Solution: `exact hCg_bd (ω 0)`

2. **Line 4260**: linarith failure on `Cg ≤ 2 * Cg` at n=0
   - Solution: Explicitly prove `0 ≤ Cg` and feed to linarith

3. **Lines 3927-4033**: L² → L¹ conversion (Step 3b)
   - Fixed 3 API incompatibilities:
     * `Continuous.tendsto` application syntax
     * `Lp.aestronglyMeasurable` (not `_coe`)
     * Squeeze theorem application structure

### Key API Discoveries

- **Lp.aestronglyMeasurable**: Correct API to get `AEStronglyMeasurable` from Lp elements
  - Found via `Exchangeability/Ergodic/InvariantSigma.lean:631`
  - Usage: `Lp.aestronglyMeasurable (f : Lp E p μ) : AEStronglyMeasurable f μ`

- **Snapshot-robust patterns**:
  - Use `eventually_gt_atTop 0` to avoid n=0 edge cases
  - Fully qualify `MeasureTheory.snorm` for robustness
  - Explicit coercion syntax `(fL2 : Ω[α] → ℝ)` for clarity

---

## Notes

- The file has **~4500 lines** of complex measure-theoretic proofs
- Three independent proofs of de Finetti's theorem (L², Koopman, Martingale)
- Current focus is on the **Koopman/Ergodic approach** (ViaKoopman.lean)
- The **L² approach** (ViaL2.lean) is the default and may be more complete
