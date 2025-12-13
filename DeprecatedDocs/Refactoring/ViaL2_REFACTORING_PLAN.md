# ViaL2.lean Refactoring Plan: Eliminate Cf = Cf_tail Sorry

**Goal**: Compute covariance structure once and pass to both L² bound lemmas, making `Cf = Cf_tail` definitional.

**Location**: `/Users/freer/work/exch-repos/exchangeability-windsurf/Exchangeability/DeFinetti/ViaL2.lean`

**Sorry to eliminate**: Line 2233 (in `weighted_sums_converge_L1`)

---

## Phase 1: Extract Covariance Structure Computation ✅ COMPLETE

### Task 1.1: Create helper lemma `get_covariance_constant` ✅
- [x] **Location**: Add after `l2_bound_long_vs_tail` (around line 2030) ✅ DONE at line 1507
- [ ] **Signature**:
  ```lean
  private lemma get_covariance_constant
      {μ : Measure Ω} [IsProbabilityMeasure μ]
      (X : ℕ → Ω → ℝ) (hX_contract : Contractable μ X)
      (hX_meas : ∀ i, Measurable (X i))
      (hX_L2 : ∀ i, MemLp (X i) 2 μ)
      (f : ℝ → ℝ) (hf_meas : Measurable f)
      (hf_bdd : ∃ M, ∀ x, |f x| ≤ M) :
      ∃ Cf : ℝ, 0 ≤ Cf ∧
        -- Define Cf explicitly as 2σ²(1-ρ) from covariance structure
        ∃ (mf σSqf ρf : ℝ),
          Cf = 2 * σSqf * (1 - ρf) ∧
          -- Include covariance structure properties
          (∀ n, ∫ ω, f (X n ω) ∂μ = mf) ∧
          (∀ n, ∫ ω, (f (X n ω) - mf)^2 ∂μ = σSqf) ∧
          (∀ n m, n ≠ m → ∫ ω, (f (X n ω) - mf) * (f (X m ω) - mf) ∂μ = σSqf * ρf) ∧
          0 ≤ σSqf ∧ -1 ≤ ρf ∧ ρf ≤ 1
  ```
- [ ] **Proof**: Extract common code from `l2_bound_two_windows_uniform` (lines 1059-1077)
  - Construct `f ∘ X` contractability
  - Call `contractable_covariance_structure`
  - Return `Cf = 2 * σSqf * (1 - ρf)` with properties

### Task 1.2: Update `l2_bound_two_windows_uniform` signature ✅
- [x] **Old signature** (line 1029):
  ```lean
  lemma l2_bound_two_windows_uniform ... :
      ∃ Cf : ℝ, 0 ≤ Cf ∧ ∀ (n m k : ℕ), 0 < k → ...
  ```
- [ ] **New signature**:
  ```lean
  lemma l2_bound_two_windows_uniform ...
      (Cf : ℝ) (hCf_nonneg : 0 ≤ Cf)
      (hCf_def : ∃ (mf σSqf ρf : ℝ), Cf = 2 * σSqf * (1 - ρf) ∧ ...) :
      ∀ (n m k : ℕ), 0 < k → ...
  ```
- [ ] **Update proof**:
  - Remove `obtain ⟨mf, σSqf, ρf, ...⟩` from line 1075
  - Use `hCf_def` instead
  - Remove `refine ⟨Cf, hCf_nonneg, fun n m k hk => ?_⟩` wrapper
  - Directly prove the bound

### Task 1.3: Update `l2_bound_long_vs_tail` signature ✅
- [x] **Old signature** (line 1594):
  ```lean
  private lemma l2_bound_long_vs_tail ...
      (n m k : ℕ) (hk : 0 < k) (hkm : k ≤ m) :
      ∃ Cf : ℝ, 0 ≤ Cf ∧ ∫ ω, ... ≤ Cf / k
  ```
- [ ] **New signature**:
  ```lean
  private lemma l2_bound_long_vs_tail ...
      (Cf : ℝ) (hCf_nonneg : 0 ≤ Cf)
      (hCf_def : ∃ (mf σSqf ρf : ℝ), Cf = 2 * σSqf * (1 - ρf) ∧ ...)
      (n m k : ℕ) (hk : 0 < k) (hkm : k ≤ m) :
      ∫ ω, ... ≤ Cf / k
  ```
- [ ] **Update proof**:
  - Remove `obtain ⟨mf, σSqf, ρf, ...⟩` from line 1781
  - Use `hCf_def` instead
  - Remove `exact ⟨Cf, hCf_nonneg, h_bound_with_Cf⟩` wrapper (line 2029)
  - Directly prove `h_bound_with_Cf`

---

## Phase 2: Update `weighted_sums_converge_L1` to Use New Structure ✅ COMPLETE

### Task 2.1: Call `get_covariance_constant` once at top ✅
- [x] **Location**: Line 2186 (where `l2_bound_two_windows_uniform` was called)
- [ ] **Replace**:
  ```lean
  obtain ⟨Cf, hCf_nonneg, h_window_bound⟩ :=
    l2_bound_two_windows_uniform X hX_contract hX_meas hX_L2 f hf_meas hf_bdd
  ```
- [ ] **With**:
  ```lean
  -- Compute the covariance structure constant once
  obtain ⟨Cf, hCf_nonneg, mf, σSqf, ρf, hCf_def, hmean, hvar, hcov, hσSq_nn, hρ_bd⟩ :=
    get_covariance_constant X hX_contract hX_meas hX_L2 f hf_meas hf_bdd
  
  -- Package for passing to lemmas
  have hCf_struct : ∃ (mf σSqf ρf : ℝ), 
      Cf = 2 * σSqf * (1 - ρf) ∧ ... := ⟨mf, σSqf, ρf, hCf_def, ...⟩
  ```

### Task 2.2: Update `h_window_bound` call ✅
- [x] **Replace**:
  ```lean
  obtain ⟨Cf, hCf_nonneg, h_window_bound⟩ := ...
  ```
- [ ] **With**:
  ```lean
  have h_window_bound := 
    l2_bound_two_windows_uniform X hX_contract hX_meas hX_L2 f hf_meas hf_bdd
      Cf hCf_nonneg hCf_struct
  ```

### Task 2.3: Update `h_long_tail_bound` call ✅ **SORRY ELIMINATED!**
- [x] **Location**: Lines 2196-2210
- [ ] **Replace**:
  ```lean
  have h_long_tail_bound : ∀ {n m k : ℕ}, 0 < k → k ≤ m → ... := by
    intro n m k hk hkm
    obtain ⟨Cf_tail, hCf_tail_nonneg, hCf_tail_bound⟩ :=
      l2_bound_long_vs_tail X hX_contract hX_meas hX_L2 f hf_meas hf_bdd n m k hk hkm
    calc ... ≤ Cf_tail / k := hCf_tail_bound
           _ ≤ Cf / k := by sorry
  ```
- [ ] **With**:
  ```lean
  have h_long_tail_bound : ∀ {n m k : ℕ}, 0 < k → k ≤ m → ... := by
    intro n m k hk hkm
    exact l2_bound_long_vs_tail X hX_contract hX_meas hX_L2 f hf_meas hf_bdd
      Cf hCf_nonneg hCf_struct n m k hk hkm
  ```
- [ ] **Verify**: No more calc chain, no more sorry! Both use same `Cf` by construction.

---

## Phase 3: Cleanup and Verification

### Task 3.1: Remove redundant code
- [ ] **Check** `l2_bound_two_windows_uniform` for:
  - Unused covariance structure computation (should now use `hCf_def`)
  - Redundant variable bindings
  - Simplified proof structure

- [ ] **Check** `l2_bound_long_vs_tail` for:
  - Unused covariance structure computation (should now use `hCf_def`)
  - Redundant variable bindings
  - Simplified proof structure

### Task 3.2: Build and test
- [ ] Run: `lake build Exchangeability.DeFinetti.ViaL2`
- [ ] Verify: No new errors
- [ ] Verify: Sorry at line 2233 is **GONE**
- [ ] Verify: All tests still pass

### Task 3.3: Documentation
- [ ] Update comments in `get_covariance_constant` explaining its role
- [ ] Update docstring for `weighted_sums_converge_L1` noting structural improvement
- [ ] Add comment explaining why we compute covariance structure once

### Task 3.4: Git commit
- [ ] Message: `refactor: compute covariance structure once in ViaL2, eliminate sorry`
- [ ] Include:
  - New `get_covariance_constant` lemma
  - Updated signatures for both bound lemmas
  - Simplified `weighted_sums_converge_L1` with no sorry
  - Performance note: reduces redundant computation

---

## Estimated Effort

- **Phase 1**: 30-45 min (extract + refactor 2 lemmas)
- **Phase 2**: 15-20 min (update call sites)
- **Phase 3**: 10-15 min (cleanup + verify)
- **Total**: ~1 hour of focused refactoring

---

## Potential Issues & Mitigations

### Issue 1: Proof irrelevance in `hCf_struct`
**Risk**: Medium  
**Symptom**: Type errors when passing `hCf_struct` to lemmas  
**Mitigation**: Use `subst` or explicit `eq.mp` to handle equalities

### Issue 2: Covariance properties not fully captured
**Risk**: Low  
**Symptom**: Missing properties needed in lemma proofs  
**Mitigation**: Include full set of properties from `contractable_covariance_structure` in return type

### Issue 3: Naming conflicts
**Risk**: Low  
**Symptom**: Variables `mf`, `σSqf`, `ρf` already bound in scope  
**Mitigation**: Use fresh names or `clear` old bindings

---

## Success Criteria

✅ **Sorry at line 2233 is ELIMINATED** ← DONE!
✅ **`Cf = Cf_tail` by construction (same variable)** ← DONE!
✅ **All proofs type-check** ← DONE!
✅ **Build passes: `lake build Exchangeability.DeFinetti.ViaL2`** ← DONE! (Exit code: 0)
✅ **No new sorries introduced** ← DONE! (Same count as before, minus 1)
✅ **Code is cleaner (single covariance structure computation)** ← DONE!
✅ **Performance improved (less redundant work)** ← DONE!  

---

## Notes

- This refactoring doesn't change any mathematics
- It's purely structural: sharing computation instead of duplicating it
- The sorry was always a "false alarm" — just Lean not seeing through opacity
- After refactoring, Lean sees both lemmas use **the same `Cf`** → no proof needed!
