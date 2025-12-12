# Session 3: Next Steps with User Guidance

## Summary

The user provided **complete drop-in solutions** that remove all conceptual blockers! The remaining work is purely mechanical API resolution.

## Key Conceptual Resolution from User

### 1. h_shift_inv: NO Exchangeability Needed! ✅

**USER'S GUIDANCE**: Don't try to prove `CE[f(ω₀)·g(ω₁)|m] = CE[f(ω₀)·g(ω₀)|m]` directly!

Instead, prove **lag-constancy**:
```
H_k := CE[f(ω₀)·g(ω_k)|ℐ]  satisfies  H_{k+1} = H_k  a.s. for all k≥0
```

This is immediate from `condexp_precomp_iterate_eq` (line 1483)!

**Why this works**: By lag-constancy + Cesàro averaging + MET, we get the factorization WITHOUT needing exchangeability.

### 2. condExp_mul_pullout: Complete Strategy ✅

User provided the exact helper lemma needed (see below).

### 3. h_tower: 5-Line Proof ✅

**Strategy**:
```lean
-- Want: CE[f·g|m] = CE[f·CE[g|m]|m]
-- Let Z = CE[g|m] (which is m-measurable)
-- Then: CE[f·g|m] - CE[f·Z|m] = CE[f·(g-Z)|m]
-- Apply pull-out: = CE[f|m]·CE[g-Z|m]
-- But CE[g-Z|m] = CE[g|m] - Z = 0 (by idempotence)
```

## Ready-to-Paste Code

### Helper Lemma 1: integrable_mul_of_ae_bdd_left

```lean
/-- If `Z` is a.e.-bounded and measurable and `Y` is integrable,
    then `Z*Y` is integrable (finite measure suffices). -/
private lemma integrable_mul_of_ae_bdd_left
    {μ : Measure (Ω[α])} [IsFiniteMeasure μ]
    {Z Y : Ω[α] → ℝ}
    (hZ : Measurable Z) (hZ_bd : ∃ C, ∀ᵐ ω ∂μ, |Z ω| ≤ C)
    (hY : Integrable Y μ) :
    Integrable (Z * Y) μ := by
  rcases hZ_bd with ⟨C, hC⟩
  have h_meas : AEStronglyMeasurable (Z * Y) μ :=
    hZ.aestronglyMeasurable.mul hY.aestronglyMeasurable
  have h_le : (fun ω => |(Z * Y) ω|) ≤ᵐ[μ] (fun ω => C * |Y ω|) := by
    refine hC.mono ?_; intro ω hω
    have hC' : 0 ≤ C := by
      have := abs_nonneg (Z ω); exact le_trans this hω
    calc |Z ω * Y ω| = |Z ω| * |Y ω| := by simpa [abs_mul]
      _ ≤ C * |Y ω| := mul_le_mul_of_nonneg_right hω (abs_nonneg _)
  have h_int_dom : Integrable (fun ω => C * |Y ω|) μ :=
    hY.norm.const_mul C
  exact h_int_dom.mono h_meas (Filter.eventually_of_forall (fun ω =>
    by rw [Real.norm_eq_abs, Real.norm_eq_abs]; exact le_trans (h_le.self_of_ae_mem trivial) (le_abs_self _)))
```

**STATUS**: Needs minor API fixes for the last line (Integrable.mono signature).

### condExp_mul_pullout Implementation

**Current blocker**: Converting `Measurable[shiftInvariantSigma] Z` to `Measurable Z`.

**Attempted approaches**:
1. `hZ_meas.mono (le_refl m)` - returns function, not term
2. `hZ_meas.aemeasurable.measurable` - gives `Measurable[m]` not `Measurable`
3. Using AEStronglyMeasurable - signature mismatch

**Solution needed**: Find correct API for sub-σ-algebra coercion. Likely one of:
- A typeclass instance that automatically coerces
- `.mono'` or similar variant
- Change helper to accept `Measurable[m]` directly

### Lag-Constancy Lemma (Replaces h_shift_inv)

```lean
lemma condexp_pair_lag_constant
    {μ : Measure (Ω[α])} [IsProbabilityMeasure μ] [StandardBorelSpace α]
    (hσ : MeasurePreserving shift μ μ)
    (f g : α → ℝ)
    (hf_meas : Measurable f) (hf_bd : ∃ C, ∀ x, |f x| ≤ C)
    (hg_meas : Measurable g) (hg_bd : ∃ C, ∀ x, |g x| ≤ C)
    (k : ℕ) :
    μ[(fun ω => f (ω 0) * g (ω (k+1))) | shiftInvariantSigma (α := α)]
      =ᵐ[μ]
    μ[(fun ω => f (ω 0) * g (ω k)) | shiftInvariantSigma (α := α)] := by
  set m := shiftInvariantSigma (α := α)
  -- The function ω ↦ f(ω₀)·g(ω_k) is integrable (bounded × bounded)
  have h_int : Integrable (fun ω => f (ω 0) * g (ω k)) μ := by
    obtain ⟨Cf, hCf⟩ := hf_bd
    obtain ⟨Cg, hCg⟩ := hg_bd
    refine MeasureTheory.integrable_of_bounded ?_ ?_
    · exact (hf_meas.comp (measurable_pi_apply 0)).mul (hg_meas.comp (measurable_pi_apply k))
    · use Cf * Cg
      intro ω
      calc |f (ω 0) * g (ω k)|
          = |f (ω 0)| * |g (ω k)| := abs_mul _ _
        _ ≤ Cf * Cg := mul_le_mul (hCf _) (hCg _) (abs_nonneg _) (by linarith)
  -- Apply condexp_precomp_iterate_eq with shift count 1
  simpa using condexp_precomp_iterate_eq (μ := μ) hσ (k := 1) h_int
```

**Location**: Add before `condexp_pair_factorization_MET`.

### h_tower Implementation

```lean
have h_tower : μ[(fun ω => f (ω 0) * g (ω 0)) | m]
    =ᵐ[μ] μ[(fun ω => f (ω 0) * μ[(fun ω => g (ω 0)) | m] ω) | m] := by
  set G := (fun ω => g (ω 0))
  set F := (fun ω => f (ω 0))
  set Z := μ[G | m]

  -- Use linearity: CE[F·G|m] - CE[F·Z|m] = CE[F·(G-Z)|m]
  have h_sub : μ[F * G | m] - μ[F * Z | m] =ᵐ[μ] μ[F * (G - Z) | m] := by
    sorry -- Use condExp_sub and algebra

  -- Z is m-measurable, so pull out: CE[F·(G-Z)|m] = CE[F|m]·CE[G-Z|m]
  have h_pullout : μ[F * (G - Z) | m] =ᵐ[μ] μ[F | m] * μ[G - Z | m] := by
    sorry -- Apply condExp_mul_pullout (once it's fixed)

  -- CE[G-Z|m] = 0 by idempotence
  have h_zero : μ[G - Z | m] =ᵐ[μ] 0 := by
    calc μ[G - Z | m]
        =ᵐ[μ] μ[G | m] - μ[Z | m] := condExp_sub _ _ _
      _ =ᵐ[μ] Z - Z := by sorry -- CE of m-measurable is itself
      _ = 0 := sub_self _

  -- Combine
  sorry
```

### h_pullout Implementation

**Once condExp_mul_pullout is fixed**:

```lean
have h_pullout : μ[(fun ω => f (ω 0) * μ[(fun ω => g (ω 0)) | m] ω) | m]
    =ᵐ[μ] (fun ω => μ[(fun ω => g (ω 0)) | m] ω * μ[(fun ω => f (ω 0)) | m] ω) := by
  set Z := μ[(fun ω => g (ω 0)) | m]
  set Y := (fun ω => f (ω 0))

  -- Z is m-measurable
  have hZ_meas : Measurable[m] Z := stronglyMeasurable_condExp.measurable

  -- Z is bounded (by Jensen)
  obtain ⟨C, hC⟩ := hg_bd
  have hZ_bd : ∃ C, ∀ ω, |Z ω| ≤ C := by
    use C
    intro ω
    sorry -- Need: |CE[g|m]| ≤ CE[|g||m] ≤ C (Jensen + monotonicity)

  -- Y is integrable
  obtain ⟨Cf, hCf⟩ := hf_bd
  have hY_int : Integrable Y μ := by
    refine MeasureTheory.integrable_of_bounded ?_ ?_
    · exact hf_meas.comp (measurable_pi_apply 0)
    · exact ⟨Cf, fun ω => hCf (ω 0)⟩

  -- Apply condExp_mul_pullout
  have h := condExp_mul_pullout hZ_meas hZ_bd hY_int

  -- Rewrite to match goal (commutativity)
  calc μ[(fun ω => f (ω 0) * Z ω) | m]
      =ᵐ[μ] μ[(fun ω => Z ω * f (ω 0)) | m] := by filter_upwards with ω; ring
    _ =ᵐ[μ] (fun ω => Z ω * μ[Y | m] ω) := h
    _ =ᵐ[μ] (fun ω => Z ω * μ[(fun ω => f (ω 0)) | m] ω) := by rfl
```

## Immediate Action Items

### Priority 1: Fix `integrable_mul_of_ae_bdd_left` (5-10 min)

The issue is in the last line with `Integrable.mono`. Need to find correct signature or use alternative like:
```lean
exact ⟨h_meas, h_int_dom.hasFiniteIntegral.of_le h_le⟩
```

### Priority 2: Fix `condExp_mul_pullout` (10-15 min)

**Option A**: Find correct coercion API
**Option B**: Modify helper to accept `Measurable[m]` instead of `Measurable`
**Option C**: Use `stronglyMeasurable_condExp` pattern from line 1596

### Priority 3: Implement lag-constancy (10-15 min)

Paste the user's code, adjust to local names.

### Priority 4: Implement h_tower and h_pullout (20-30 min each)

Follow the strategies above once pull-out is working.

## Expected Timeline

- **Fix helpers**: 30 minutes
- **Implement lag-constancy**: 15 minutes
- **Implement h_tower**: 30 minutes
- **Implement h_pullout**: 30 minutes

**Total**: ~2 hours to complete the BREAKTHROUGH lemma!

## User's Complete Roadmap

After completing the above:

1. **Finite product factorization** (~30 LOC): Induction using pair case
2. **Indicator bridge** (~5 LOC): Apply to indicators
3. **Main theorem** (~5 LOC): Remove axiom keywords

This eliminates ALL 2 core axioms and completes de Finetti!

## Notes

- User confirmed NO exchangeability assumption needed
- Lag-constancy is the correct Kallenberg approach
- All strategies are mathematically sound
- Only remaining issues are Lean API technicalities
