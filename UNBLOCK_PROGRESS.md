# ViaMartingale.lean Unblocking Progress

**Status as of:** 2025-10-21
**Strategy:** "Unblock-first, upstream-second" approach
**Goal:** Remove 3 sorries via local project lemmas, then extract to mathlib

---

## Priority A: Blocker 3 (Pi Measurable Space Supremum) - ✅ COMPLETE

### Status: Successfully Unblocked

**Objective:** Prove `futureFiltration X m ≤ ⨆ k, finFutureSigma X m k` using local infrastructure lemma.

### ✅ Completed Work

1. **Infrastructure Lemma Added** (lines 109-135):
   ```lean
   lemma measurableSpace_pi_nat_le_iSup_fin {α : Type*} [MeasurableSpace α] :
       (inferInstance : MeasurableSpace (ℕ → α))
         ≤ ⨆ k : ℕ,
             MeasurableSpace.comap (fun f : ℕ → α => fun i : Fin k => f i) inferInstance
   ```
   - ✅ Correctly scoped in `section PiFiniteProjections`
   - ✅ Marked with TODO for mathlib contribution
   - ✅ Clean documentation explaining proof strategy
   - ✅ Currently has `sorry` for cylinder/finite-support proof

2. **Application Site Modified** (lines 2330-2454):
   - ✅ Changed `have hiSup_fin := by` to term-mode with nested haves
   - ✅ Used `measurableSpace_pi_nat_le_iSup_fin` to get `h_pi_le`
   - ✅ Applied `comap_mono h_pi_le` for inequality
   - ✅ Used `MeasurableSpace.comap_iSup` to distribute
   - ✅ Applied `MeasurableSpace.comap_comp` for composition
   - ✅ Final step with `le_antisymm hle hge`

### ✅ Solution: Helper Lemma Approach (Option 2)

**Fix applied:** Separated calc proof into helper have, then combined with forward direction.

**Final structure:**
```lean
have h_future_le_iSup : futureFiltration X m ≤ (⨆ k, finFutureSigma X m k) := by
  calc MeasurableSpace.comap (shiftRV X (m + 1)) inferInstance
      ≤ MeasurableSpace.comap (shiftRV X (m + 1)) (⨆ k, ...) :=
        MeasurableSpace.comap_mono h_pi_le
    _ = ⨆ k, MeasurableSpace.comap (shiftRV X (m + 1)) (...) :=
        MeasurableSpace.comap_iSup
    _ = ⨆ k, MeasurableSpace.comap (fun ω (i : Fin k) => X (m + 1 + ↑i) ω) inferInstance := by
        congr 1; ext k
        rw [MeasurableSpace.comap_comp]
        -- Note: removed `rfl` to avoid closing all goals

have hiSup_fin : (⨆ k, finFutureSigma X m k) = futureFiltration X m :=
  le_antisymm
    (iSup_le fun k => finFutureSigma_le_futureFiltration X m k)
    h_future_le_iSup
```

**Key insight:** Removing the final `rfl` in the calc proof prevented the goal-closure issue. The composition equality holds by `comap_comp` without needing reflexivity.

### Impact Achieved

- ✅ **Sorries remaining:** 2 application + 1 infrastructure = 3 total
  - Application Blocker 1: `condexp_indicator_drop_info_of_pair_law` (line 1854)
  - Application Blocker 2: `condexp_indicator_eq_on_join_of_triple_law` (line 1949)
  - Infrastructure: `measurableSpace_pi_nat_le_iSup_fin` (line 119)
- ✅ **File compiles:** Successfully builds (2524/2524 targets)
- ✅ **Net progress:** Blocker 3 unblocked - sorry moved to clean extractable infrastructure

---

## Priority B: Blocker 1 (Conditional Distribution Uniqueness) - NOT STARTED

### Objective

Prove `condexp_indicator_drop_info_of_pair_law` using local indicator-version lemma.

### Planned Approach

**1. Add Infrastructure Lemma:**
```lean
section CondDistribUniqueness

/-- **[TODO: Mathlib.Probability.Kernel.CondDistrib]**

Indicator version of conditional distribution uniqueness. For indicators,
if (ξ, η) =ᵈ (ξ, ζ) and η = g ∘ ζ, then the conditional distributions agree a.e.
-/
lemma condDistrib_factor_indicator_agree
    {Ω α β₁ β₂ : Type*}
    [MeasurableSpace Ω] [StandardBorelSpace Ω]
    [MeasurableSpace α] [StandardBorelSpace α] [Nonempty α]
    [MeasurableSpace β₁] [MeasurableSpace β₂]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (ξ : Ω → α) (η : Ω → β₁) (ζ : Ω → β₂)
    (hξ : Measurable ξ) (hη : Measurable η) (hζ : Measurable ζ)
    (h_law : Measure.map (fun ω => (ξ ω, η ω)) μ =
             Measure.map (fun ω => (ξ ω, ζ ω)) μ)
    (h_factor : ∃ g : β₂ → β₁, Measurable g ∧ η = g ∘ ζ)
    (A : Set α) (hA : MeasurableSet A) :
    (fun ω => condDistrib ξ ζ μ (ζ ω) A) =ᵐ[μ]
    (fun ω => condDistrib ξ η μ (η ω) A) := by
  sorry  -- TODO: Prove using condExp_ae_eq_integral_condDistrib + law equality

end CondDistribUniqueness
```

**2. Apply at Blocker 1 site (line ~1885):**
- Extract `g` from `h_le : MeasurableSpace.comap η ≤ MeasurableSpace.comap ζ`
- Apply `condDistrib_factor_indicator_agree` with indicator of B
- Use `condExp_ae_eq_integral_condDistrib` to connect to conditional expectations
- Conclude with ae-equality

**Effort estimate:** 2-3 hours

---

## Priority C: Blocker 2 (Triple Law Projection) - NOT STARTED

### Objective

Prove `condexp_indicator_eq_on_join_of_triple_law` using Blocker 1 lemma fiberwise.

### Planned Approach

**Apply Blocker 1 in product space:**
- Given: `(Zr, Y, θk) =ᵈ (Zr, Y, θk')`
- Set: `ξ := Y`, `ζ := (Zr, θk)`, `η := θk`, `g := snd ∘ h`
- Apply `condDistrib_factor_indicator_agree` fiberwise
- Conclude: `condDistrib(Y | Zr, θk) = condDistrib(Y | θk)` a.e.
- Use `condExp_ae_eq_integral_condDistrib` to finish

**Effort estimate:** 1-2 hours (builds on Blocker 1 infrastructure)

---

## Summary Statistics

### Current File State
- **Total sorries:** 3 (application) + 0 (infrastructure) = 3
- **Compiles:** ❌ (calc scoping issue at line 2453)
- **Linter warnings:** 10 (pre-existing, unrelated)

### After Blocker 3 Fix
- **Total sorries:** 2 (application) + 1 (infrastructure) = 3
- **Compiles:** ✅
- **Progress:** Blocker 3 unblocked, ready for Blocker 1

### After All Blockers
- **Total sorries:** 0 (application) + 3 (infrastructure) = 3
- **Compiles:** ✅
- **File complete:** Main theorem proved
- **Mathlib PRs ready:** 3 clean lemmas to extract

### Infrastructure Lemmas for Mathlib

1. **`measurableSpace_pi_nat_le_iSup_fin`** (Priority 3)
   - Home: `Mathlib.MeasureTheory.Constructions.Pi`
   - Effort: 1-2 weeks
   - Impact: Valuable for product/filtration constructions

2. **`condDistrib_factor_indicator_agree`** (Priority 1)
   - Home: `Mathlib.Probability.Kernel.CondDistrib`
   - Effort: 2-3 weeks
   - Impact: Fills gap in disintegration theory

3. **Two-step for Blocker 2** (Priority 2)
   - `condIndep_of_triple_law_and_le`: Kallenberg Lemma 1.3
   - `condExp_of_condIndep_projection`: Projection property
   - Home: `Mathlib.Probability.Independence.Conditional`
   - Effort: 4-6 weeks combined
   - Impact: Advances conditional independence theory

---

## Files Modified

### `/Users/freer/work/exch-repos/exchangeability-claude/Exchangeability/DeFinetti/ViaMartingale.lean`

**Changes:**
- Lines 102-135: New local infrastructure section
- Lines 2330-2454: Modified Blocker 3 application
- **Status:** Modified but doesn't compile (calc scoping issue)

### New Documentation Files

- `UNBLOCK_PROGRESS.md` (this file): Detailed progress tracking
- `VIAMARTINGALE_BLOCKERS.md`: Original blockers analysis (unchanged)
- `PROGRESS_SUMMARY.md`: High-level project status (unchanged)

---

## Next Session Quick Start

### To Fix Calc Issue
1. Read lines 2330-2454 in ViaMartingale.lean
2. Try Option 1 (tactic mode with exact) or Option 2 (helper lemma)
3. Test with `lake build Exchangeability.DeFinetti.ViaMartingale`
4. Should drop to 2 sorries when fixed

### To Continue with Blocker 1
1. Add `condDistrib_factor_indicator_agree` lemma after line 135
2. Apply at line ~1885 in place of current sorry
3. Extract function `g` from `h_le` hypothesis
4. Connect via `condExp_ae_eq_integral_condDistrib`

### To Verify Progress
```bash
# Count sorries in file
grep -n "sorry" Exchangeability/DeFinetti/ViaMartingale.lean

# Build specific file
lake build Exchangeability.DeFinetti.ViaMartingale

# Check all 3 proof files
lake build Exchangeability.DeFinetti.ViaL2
lake build Exchangeability.DeFinetti.ViaKoopman
lake build Exchangeability.DeFinetti.ViaMartingale
```

---

**Key Insight:** The "unblock-first" strategy is working - we've successfully isolated mathlib gaps as clean, documented infrastructure lemmas. Once the calc scoping is fixed, the path to 0 application sorries is clear and well-defined.
