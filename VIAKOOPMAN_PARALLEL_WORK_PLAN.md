# ViaKoopman Parallel Work Plan

**Date:** 2025-10-19
**Status:** ViaKoopman currently has ~100+ compilation errors + 4 strategic sorries
**Goal:** Get ViaKoopman building in parallel with other work

## Current Build Status

```bash
lake build Exchangeability.DeFinetti.ViaKoopman
# Result: ~100+ errors, 4 major sorries
```

**Error categories:**
1. **Type class synthesis failures** (~40% of errors)
2. **Unsolved goals** (~30% of errors)
3. **Type mismatches** (~20% of errors)
4. **Tactic failures** (rewrite, apply, etc.) (~10%)

**The 4 strategic sorries** (lines with build warnings):
1. Line 2123: `condexp_tower_for_products` - needs `condexp_pair_lag_constant`
2. Line 2228: Similar conditional expectation tower law
3. Line 3228: `birkhoffCylinder_tendsto_condexp` - needs L² construction
4. Line 3258: `extremeMembers_agree` - Koopman fixed-point argument

---

## Root Cause Analysis

### Problem 1: Measure space definitional equality issues

**Symptoms:**
```
synthesized type class instance is not definitionally equal to
expression inferred by typing rules
```

**Root cause:** The shift-invariant σ-algebra construction creates a coercion
that Lean can't automatically recognize as definitionally equal.

**Locations:** Lines 495, 502, 515, 530, 552, etc.

**Fix strategy:**
- Add explicit type annotations
- Use `convert` tactic instead of `exact`
- Prove auxiliary lemmas about measure space equality

**Estimated effort:** 2-3 hours of systematic fixes

---

### Problem 2: Conditional expectation API gaps

**Missing lemmas:**
1. **`condexp_pair_lag_constant`** (line 2123, 2228)
   - Statement: CE[f(ω₀)·g(ωₖ₊₁) | ℐ] = CE[f(ω₀)·g(ωₖ) | ℐ]
   - Depends on: Shift-invariance of measure
   - Status: Axiom that needs proof

2. **Tower law for products** (lines 2114-2123)
   - Statement: CE[f·g | ℐ] = CE[f·CE[g|ℐ] | ℐ]
   - Depends on: `condexp_pair_lag_constant`
   - Status: Proof blocked on missing lemma

**Fix strategy:**
- Prove `condexp_pair_lag_constant` using shift-invariance
- Apply to complete tower law
- This unblocks sorries at lines 2123, 2228

**Estimated effort:** 4-6 hours (non-trivial CE calculation)

---

### Problem 3: L² construction for cylinders

**Sorry at line 3228:** `birkhoffCylinder_tendsto_condexp`

**What's needed:**
```lean
∃ (fL2 : Lp ℝ 2 μ),
  (∀ᵐ ω ∂μ, fL2 ω = F ω) ∧
  Tendsto (fun n => birkhoffAverage ℝ (koopman shift hσ) id n fL2)
    atTop (𝓝 (condexpL2 (μ := μ) fL2))
```

**Components:**
1. Construct L² representative of cylinder function F
2. Prove Birkhoff averages converge
3. Identify limit as conditional expectation

**Dependencies:**
- `productCylinderLp` (referenced in TODO, may not exist)
- Mean Ergodic Theorem (already have in KoopmanMeanErgodic.lean)

**Fix strategy:**
1. Define `productCylinderLp` helper
2. Show cylinder functions are in L²
3. Apply Mean Ergodic Theorem
4. Use `InvariantSigma.lean` connection to condexpL2

**Estimated effort:** 3-4 hours

---

### Problem 4: Fixed-point characterization

**Sorry at line 3258:** `extremeMembers_agree`

**What's needed:**
```lean
∃ (fL2 : Lp ℝ 2 μ),
  koopman shift hσ (condexpL2 (μ := μ) fL2) = condexpL2 (μ := μ) fL2
```

**Mathematical content:**
- Conditional expectation lives in fixed-point subspace
- Koopman operator fixes conditional expectations onto invariant σ-algebra

**Dependencies:**
- Already proven in `InvariantSigma.lean`!
- Just need to connect the pieces

**Fix strategy:**
- Look up theorem in `InvariantSigma.lean`
- Apply directly (likely 1-liner)

**Estimated effort:** 30 minutes - 1 hour

---

## Parallel Work Streams

### Stream 1: Type class cleanup (High priority, low risk)

**Owner:** Anyone comfortable with type class synthesis
**Time:** 2-3 hours
**Parallelizable:** Yes - can work on different sections independently

**Tasks:**
1. Fix measure space coercion issues (lines 495-600)
2. Add explicit type annotations where needed
3. Convert `exact` to `convert` for definitional equality issues
4. Test incrementally with `lake build`

**Deliverable:** Reduce errors from ~100 to ~20-30

---

### Stream 2: Conditional expectation lemmas (Medium priority, high value)

**Owner:** Someone familiar with conditional expectation theory
**Time:** 4-6 hours
**Parallelizable:** Partially (can prove helper lemmas in parallel)

**Tasks:**
1. **Phase A:** Prove shift-invariance helper lemmas (2 hours)
   - `shift_product_eq`
   - `condexp_shift_invariant`

2. **Phase B:** Prove `condexp_pair_lag_constant` (2-3 hours)
   - Use shift-invariance
   - Apply tower law
   - Verify bounded case

3. **Phase C:** Complete `condexp_tower_for_products` (1 hour)
   - Apply `condexp_pair_lag_constant`
   - Remove sorries at lines 2123, 2228

**Deliverable:** 2 of 4 sorries resolved

---

### Stream 3: L² and convergence (Medium priority, moderate difficulty)

**Owner:** Someone comfortable with L² spaces and ergodic theory
**Time:** 3-4 hours
**Parallelizable:** Partially (L² construction separate from convergence)

**Tasks:**
1. **Phase A:** Define `productCylinderLp` (1 hour)
   - Construct L² representative
   - Prove boundedness
   - Show ae-equality with cylinder function

2. **Phase B:** Prove convergence (2-3 hours)
   - Apply Mean Ergodic Theorem from `KoopmanMeanErgodic.lean`
   - Show Birkhoff averages converge
   - Identify limit

**Deliverable:** Sorry at line 3228 resolved

---

### Stream 4: Fixed-point connection (Low priority, easy)

**Owner:** Anyone (trivial once Stream 3 done)
**Time:** 30 minutes - 1 hour
**Parallelizable:** No - depends on Stream 3

**Tasks:**
1. Find relevant theorem in `InvariantSigma.lean`
2. Apply to `extremeMembers_agree`
3. Remove sorry at line 3258

**Deliverable:** Last sorry resolved

---

### Stream 5: Integration with ViaL2/ViaMartingale (Low priority, long-term)

**Owner:** Project lead
**Time:** Ongoing
**Parallelizable:** Yes - completely independent

**Context:**
- ViaL2.lean: Has pre-existing simp errors (unrelated to ViaKoopman)
- ViaMartingale.lean: Has pre-existing simp errors
- These should be fixed independently

**Tasks:**
1. Fix ViaL2 simp recursion errors (lines 104, 138, 604)
2. Fix ViaMartingale simp errors (lines 137, 148, 328+)
3. Complete any remaining sorries in those files

**Note:** This doesn't block ViaKoopman - they're independent proofs

---

## Recommended Execution Order

### Week 1: Foundation (Parallel)

**Day 1-2:**
- Stream 1 (Type class cleanup) - **Start immediately**
- Stream 2 Phase A (CE helpers) - **Start immediately**

**Day 3:**
- Stream 2 Phase B (`condexp_pair_lag_constant`)
- Stream 3 Phase A (`productCylinderLp`)

**Day 4:**
- Stream 2 Phase C (Apply to tower law)
- Stream 3 Phase B (Convergence)

**Day 5:**
- Stream 4 (Fixed-point) - **Depends on Stream 3**
- Final integration and testing

### Week 2: Polish and Integration

- Extract CE utilities (Tier 2) once ViaKoopman builds
- Performance optimization
- Documentation updates

---

## Success Criteria

**Milestone 1: Reduce error count** (2-3 hours)
- ✅ Goal: <30 errors remaining
- Owner: Stream 1
- Signal: Type class issues resolved

**Milestone 2: Resolve CE sorries** (1 week)
- ✅ Goal: Lines 2123, 2228 no longer have sorry
- Owner: Stream 2
- Signal: Tower law complete

**Milestone 3: L² construction** (1 week)
- ✅ Goal: Line 3228 no longer has sorry
- Owner: Stream 3
- Signal: Birkhoff convergence proven

**Milestone 4: Full build** (1.5 weeks)
- ✅ Goal: `lake build Exchangeability.DeFinetti.ViaKoopman` succeeds
- Owner: All streams
- Signal: Zero errors, zero sorries

**Milestone 5: Tier 2 extraction** (2 weeks)
- ✅ Goal: CE utilities moved to `Probability/CondExp.lean`
- Owner: Refactoring team
- Signal: ViaKoopman reduced by ~120 lines

---

## Risk Assessment

### High Risk: Conditional expectation lemmas (Stream 2)

**Risks:**
- `condexp_pair_lag_constant` may require new mathlib infrastructure
- Shift-invariance argument could be subtle
- May need to ask mathlib community for help

**Mitigation:**
- Start early (Day 1)
- Keep sorry placeholders if proof is complex
- Consider axiom if mathlib PR needed

### Medium Risk: L² construction (Stream 3)

**Risks:**
- `productCylinderLp` API may not match what's needed
- Convergence proof might need different formulation

**Mitigation:**
- Check mathlib for similar constructions
- Use `SimpleFunc` if cylinder approach doesn't work

### Low Risk: Type class cleanup (Stream 1)

**Risks:**
- Tedious but mechanical
- Could introduce new errors if not careful

**Mitigation:**
- Test incrementally
- Use `#check` to verify types

---

## Quick Start Guide

**Want to help? Pick a stream based on your expertise:**

### Option A: I know Lean type classes well
→ **Stream 1** - Start at line 495, fix type class synthesis errors

### Option B: I know conditional expectation theory
→ **Stream 2** - Start with `condexp_pair_lag_constant` proof sketch

### Option C: I know L² spaces and ergodic theory
→ **Stream 3** - Define `productCylinderLp` helper

### Option D: I want an easy win
→ **Stream 4** - Find the theorem in `InvariantSigma.lean` (do this last)

### Option E: I want to work on a different proof
→ **Stream 5** - Fix ViaL2 or ViaMartingale simp errors independently

---

## Current Blockers Summary

| Sorry | Line | Blocker | Stream | Estimated Time |
|-------|------|---------|--------|----------------|
| condexp_tower_for_products | 2123 | needs condexp_pair_lag_constant | 2 | 4-6 hours |
| (similar) | 2228 | needs condexp_pair_lag_constant | 2 | (same as above) |
| birkhoffCylinder_tendsto_condexp | 3228 | needs productCylinderLp | 3 | 3-4 hours |
| extremeMembers_agree | 3258 | lookup in InvariantSigma.lean | 4 | 30 min - 1 hour |

**Total estimated effort:** 8-12 hours of focused work across 4 parallel streams

**Critical path:** Stream 2 → Stream 3 → Stream 4 (sequential dependencies)

**Parallelizable:** Streams 1, 2, 5 can all run simultaneously

---

## Notes

- ViaKoopman is **not blocking** ViaL2 or ViaMartingale - they're independent proofs
- Once ViaKoopman builds, can extract CE utilities to Tier 2
- Ergodic theory files (Tier 3) are already organized and building
- This is a **completeness** task, not a **correctness** task - the math is sound

**Updated:** 2025-10-19
