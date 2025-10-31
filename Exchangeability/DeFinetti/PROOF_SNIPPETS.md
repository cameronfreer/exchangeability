# Proof Snippets for ViaMartingale.lean

This file contains proof strategies and code snippets for completing the remaining sorries in ViaMartingale.lean, based on the kernel uniqueness approach for Kallenberg Lemma 1.3.

## Status (2025-10-31)

**Completed:**
- ✅ Added `map_pair_eq_compProd_condDistrib` (disintegration helper)
- ✅ Added `map_swap_pair_eq` (swap helper)
- ✅ `equal_kernels_on_factor` proof structure (lines 437-541) - already in file
- ✅ Partial proof for `condexp_indicator_drop_info_of_pair_law_proven` (lines 555-626)

**Remaining:**
- ⚠️ Fix compilation errors in helper lemmas
- ⚠️ Complete `map_pair_eq_compProd_change_base` (line 414 sorry)
- ⚠️ Fill `condIndep_of_triple_law` (line 705 sorry)

## 1. Conditional Independence from Triple Law

**Location:** `condIndep_of_triple_law` (currently at line ~705 in ViaMartingale.lean)

**Goal:** Prove rectangle factorization:
```lean
μ[ 1_A(Y) · 1_B(Z) | W ] =ᵐ μ[ 1_A(Y) | W ] · μ[ 1_B(Z) | W ]
```

**Strategy:** Use tower property + conditional expectation pull-out rules.

### Complete Proof Sketch

```lean
lemma condIndep_indicator_of_triple_law
  (A B : Set ℝ) (hA : MeasurableSet A) (hB : MeasurableSet B) :
  condExp μ (σ[W])
    (fun ω => Set.indicator (Y ⁻¹' A) (fun _ => (1 : ℝ)) ω
            * Set.indicator (Z ⁻¹' B) (fun _ => (1 : ℝ)) ω)
  =ᵐ[μ]
  (condExp μ (σ[W]) (fun ω => Set.indicator (Y ⁻¹' A) (fun _ => (1 : ℝ)) ω)) *
  (condExp μ (σ[W]) (fun ω => Set.indicator (Z ⁻¹' B) (fun _ => (1 : ℝ)) ω)) := by
  classical
  -- Use the tower property w.r.t. σ(W) ≤ σ(Z,W)
  have hle : σ[W] ≤ σ[Z, W] := by
    -- Prove inclusion of σ-algebras
    sorry  -- standard inclusion proof

  -- Step 1: Tower property
  have h1 :
    condExp μ (σ[W])
      (fun ω => Set.indicator (Y ⁻¹' A) (fun _ => (1 : ℝ)) ω
              * Set.indicator (Z ⁻¹' B) (fun _ => (1 : ℝ)) ω)
    =ᵐ[μ]
    condExp μ (σ[W])
      (condExp μ (σ[Z, W])
        (fun ω => Set.indicator (Y ⁻¹' A) (fun _ => (1 : ℝ)) ω
                * Set.indicator (Z ⁻¹' B) (fun _ => (1 : ℝ)) ω)) := by
    simpa using
      condExp_condExp_of_le
        (μ := μ) (hm := hle)
        (f := fun ω => Set.indicator (Y ⁻¹' A) (fun _ => (1 : ℝ)) ω
                        * Set.indicator (Z ⁻¹' B) (fun _ => (1 : ℝ)) ω)

  -- Step 2: Pull out σ(Z,W)-measurable factor 1_B(Z)
  have h2 :
    condExp μ (σ[Z, W])
      (fun ω => Set.indicator (Y ⁻¹' A) (fun _ => (1 : ℝ)) ω
              * Set.indicator (Z ⁻¹' B) (fun _ => (1 : ℝ)) ω)
    =ᵐ[μ]
    (fun ω => Set.indicator (Z ⁻¹' B) (fun _ => (1 : ℝ)) ω)
    * condExp μ (σ[Z, W])
      (fun ω => Set.indicator (Y ⁻¹' A) (fun _ => (1 : ℝ)) ω) := by
    -- Use condExp_mul_left_ae_measurable
    have hZmeas :
      AEStronglyMeasurable
        (fun ω => Set.indicator (Z ⁻¹' B) (fun _ => (1 : ℝ)) ω)
        (μ.trim le_rfl) := by
      exact (hZ.measurableSet_preimage hB).aemeasurable.indicator
    simpa [mul_comm, mul_left_comm, mul_assoc]
      using condExp_mul_left_ae_measurable
              (μ := μ) (m := σ[Z, W])
              (h := fun ω => Set.indicator (Z ⁻¹' B) (fun _ => (1 : ℝ)) ω)
              (X := fun ω => Set.indicator (Y ⁻¹' A) (fun _ => (1 : ℝ)) ω)
              (hh := hZmeas)

  -- Step 3: Drop info for Y (use condexp_indicator_drop_info_of_pair_law_proven)
  -- This is where we use the triple law!
  have hdrop :
    condExp μ (σ[Z, W])
      (fun ω => Set.indicator (Y ⁻¹' A) (fun _ => (1 : ℝ)) ω)
    =ᵐ[μ]
    condExp μ (σ[W])
      (fun ω => Set.indicator (Y ⁻¹' A) (fun _ => (1 : ℝ)) ω) := by
    -- Apply condexp_indicator_drop_info_of_pair_law_proven
    -- with the triple law projected to (Y,W) vs (Y,W')
    sorry  -- Use condExp_eq_of_triple_law

  -- Step 4: Push hdrop through outer CE and take out σ(W)-measurable factor
  have h3 :
    condExp μ (σ[W])
      ( (fun ω => Set.indicator (Z ⁻¹' B) (fun _ => (1 : ℝ)) ω)
      * condExp μ (σ[Z, W])
          (fun ω => Set.indicator (Y ⁻¹' A) (fun _ => (1 : ℝ)) ω) )
    =ᵐ[μ]
    condExp μ (σ[W])
      ( (fun ω => Set.indicator (Z ⁻¹' B) (fun _ => (1 : ℝ)) ω)
      * condExp μ (σ[W])
          (fun ω => Set.indicator (Y ⁻¹' A) (fun _ => (1 : ℝ)) ω) ) := by
    refine condExp_congr_ae (μ := μ) (m := σ[W]) ?_ ?_
    · -- integrability
      sorry
    · -- apply hdrop pointwise
      filter_upwards [hdrop] with ω hω; simpa [hω]

  -- Step 5: Take out σ(W)-measurable factor
  have h4 :
    condExp μ (σ[W])
      ( (fun ω => Set.indicator (Z ⁻¹' B) (fun _ => (1 : ℝ)) ω)
      * condExp μ (σ[W])
          (fun ω => Set.indicator (Y ⁻¹' A) (fun _ => (1 : ℝ)) ω) )
    =ᵐ[μ]
    (condExp μ (σ[W])
      (fun ω => Set.indicator (Z ⁻¹' B) (fun _ => (1 : ℝ)) ω))
    *
    (condExp μ (σ[W])
      (fun ω => Set.indicator (Y ⁻¹' A) (fun _ => (1 : ℝ)) ω)) := by
    have hWmeas :
      AEStronglyMeasurable
        (condExp μ (σ[W]) (fun ω => Set.indicator (Y ⁻¹' A) (fun _ => (1 : ℝ)) ω)) μ :=
      (condExp_ae_stronglyMeasurable
        (μ := μ) (m := σ[W])
        (fun ω => Set.indicator (Y ⁻¹' A) (fun _ => (1 : ℝ)) ω))
    simpa [Pi.mul_def, mul_comm, mul_left_comm, mul_assoc]
      using condExp_mul_right_ae_measurable
        (μ := μ) (m := σ[W])
        (h := condExp μ (σ[W]) (fun ω => Set.indicator (Y ⁻¹' A) (fun _ => (1 : ℝ)) ω))
        (X := fun ω => Set.indicator (Z ⁻¹' B) (fun _ => (1 : ℝ)) ω)
        (hh := hWmeas)

  -- Assemble the chain
  calc
    condExp μ (σ[W])
      (fun ω => Set.indicator (Y ⁻¹' A) (fun _ => (1 : ℝ)) ω
              * Set.indicator (Z ⁻¹' B) (fun _ => (1 : ℝ)) ω)
        =ᵐ[μ]
      condExp μ (σ[W])
        (condExp μ (σ[Z, W])
          (fun ω => Set.indicator (Y ⁻¹' A) (fun _ => (1 : ℝ)) ω
                  * Set.indicator (Z ⁻¹' B) (fun _ => (1 : ℝ)) ω)) := h1
    _ =ᵐ[μ]
      condExp μ (σ[W])
        ((fun ω => Set.indicator (Z ⁻¹' B) (fun _ => (1 : ℝ)) ω)
         * condExp μ (σ[Z, W])
            (fun ω => Set.indicator (Y ⁻¹' A) (fun _ => (1 : ℝ)) ω)) := by
          simpa [Pi.mul_def, mul_comm, mul_left_comm, mul_assoc] using congrArg _ h2
    _ =ᵐ[μ]
      condExp μ (σ[W])
        ((fun ω => Set.indicator (Z ⁻¹' B) (fun _ => (1 : ℝ)) ω)
         * condExp μ (σ[W])
            (fun ω => Set.indicator (Y ⁻¹' A) (fun _ => (1 : ℝ)) ω)) := h3
    _ =ᵐ[μ]
      (condExp μ (σ[W])
        (fun ω => Set.indicator (Z ⁻¹' B) (fun _ => (1 : ℝ)) ω))
      *
      (condExp μ (σ[W])
        (fun ω => Set.indicator (Y ⁻¹' A) (fun _ => (1 : ℝ)) ω)) := h4
```

### Adaptation to Current File

The current `condIndep_of_triple_law` at line ~705 needs to:
1. Convert from generic types (α, β, γ) to ℝ-valued indicators
2. Use `condIndep_of_rect_factorization` constructor
3. Apply the proof above for each rectangle A × B

**Key insight:** The "drop info" step (hdrop) is exactly what `condExp_eq_of_triple_law` provides!

## 2. Completing map_pair_eq_compProd_change_base

**Location:** Line ~414 in ViaMartingale.lean

**Missing piece:** Rectangle computation showing that pushforward of compProd along (φ, id) works correctly.

**Status:** This is the `hR` admit in the `equal_kernels_on_factor` proof. The user mentioned this can be filled with a "25-line rectangle/π-λ proof".

**Strategy:**
1. Check rectangles A × B
2. Use `Measure.compProd_prod`
3. Change of variables via `lintegral_map_equiv`
4. Monotone class theorem

## 3. Fixing Compilation Errors

**Current errors (as of commit 4dd9918):**

1. **`map_pair_eq_compProd_condDistrib`** (line 377):
   - Type mismatch in `compProd_map_condDistrib` application
   - Need to swap argument order or use correct signature

2. **`map_swap_pair_eq`** (line 387):
   - Missing `measurableSet_preimage` method
   - Can use simpler proof with `ext S hS` + measure equality

3. **`condExp_ae_eq_integral_condDistrib`** (lines 578, 586):
   - Wrong argument names (should use `X`, `Y` not `ξ`, `η`)
   - Need `Measurable` not `MeasurableSet` for last argument

4. **`hkernel_eq` connection** (line 602):
   - Need to show composition kernel at `η ω` equals direct kernel at `ζ ω`
   - This requires understanding kernel composition definition

## References

- Kallenberg (2005), Lemma 1.3 (contraction-independence)
- Mathlib: `ProbabilityTheory.condDistrib_ae_eq_of_measure_eq_compProd`
- Mathlib: `MeasureTheory.condExp_condExp_of_le` (tower property)
