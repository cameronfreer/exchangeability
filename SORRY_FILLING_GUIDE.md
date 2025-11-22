# ViaL2 Sorry Filling Guide

Comprehensive guide to filling the remaining `sorry`s in the ViaL2 proof files.

**Generated:** 2025-11-22
**Status:** 24 sorries remaining across 3 files

---

## Quick Inventory

### `MoreL2Helpers.lean` (7 sorries)

1. **Line 151** - L¹ uniqueness lemma (`L1_unique_of_two_limits`)
2. **Line 372** - IsFiniteMeasure instance (depends on directing_measure_isProbabilityMeasure)
3. **Line 382** - Probability measure constant (depends on directing_measure_isProbabilityMeasure)
4. **Line 470** - Non-measurable set case in directing_measure_measurable
5. **Line 510** - Indicator integral identity (base case for monotone class)
6. **Line 521** - Monotone class argument
7. **Line 569** - Bridge property inductive step

### `MainConvergence.lean` (3 sorries)

1. **Line 888** - Packaged conditional expectation (wrapper around directing_measure)
2. **Line 2628** - alphaIic → 0 as t → -∞
3. **Line 2656** - alphaIic → 1 as t → +∞

### `CesaroConvergence.lean` (8 sorries)

1. **Line 1158** - Finset sum conversion (range n → Fin m with indicators)
2. **Line 1161** - Finset sum conversion (range n' → Fin m with indicators)
3. **Line 1164** - Simplify indicator sums, relate to p, q, ξ
4. **Line 2279** - Tail measurability of blockAvg L² limit
5. **Line 2577** - Tail measurability construction in cesaro_to_condexp_L2
6. **Line 2695** - Uniqueness via set-integral equality
7. **Line 2766** - L² → L¹ conversion
8. **Line 2882** - DCT for indicators of (-∞, t]

---

## 1. Easy Wins (Can Fill Now)

### 1.1. L¹ Uniqueness (`MoreL2Helpers.lean:151`)

**Mathematical argument:**
- Given: `‖fn - f‖₁ → 0` and `‖fn - g‖₁ → 0`
- Triangle inequality: `‖f - g‖₁ ≤ ‖f - fn‖₁ + ‖fn - g‖₁`
- RHS → 0, so `‖f - g‖₁ = 0`
- Use `eLpNorm_eq_zero_iff` to get `f =ᵐ g`

**Lean sketch:**

```lean
private lemma L1_unique_of_two_limits
  {μ : Measure Ω} {f g : Ω → ℝ}
  (hf : Integrable f μ) (hg : Integrable g μ)
  {fn : ℕ → Ω → ℝ}
  (hfn : ∀ n, AEStronglyMeasurable (fn n) μ)
  (h1 : Tendsto (fun n => eLpNorm (fn n - f) 1 μ) atTop (𝓝 0))
  (h2 : Tendsto (fun n => eLpNorm (fn n - g) 1 μ) atTop (𝓝 0)) :
  f =ᵐ[μ] g := by
  -- Triangle inequality for each n
  have h_triangle : ∀ n,
      eLpNorm (f - g) 1 μ ≤
      eLpNorm (fn n - f) 1 μ + eLpNorm (fn n - g) 1 μ := by
    intro n
    have : f - g = (f - fn n) + (fn n - g) := by funext ω; ring
    -- Apply eLpNorm_add_le with p=1
    sorry -- standard triangle inequality application

  -- RHS tends to 0
  have h_rhs_tendsto :
      Tendsto (fun n => eLpNorm (fn n - f) 1 μ + eLpNorm (fn n - g) 1 μ)
              atTop (𝓝 0) := by
    simpa using h1.add h2

  -- Therefore LHS ≤ 0
  have h_norm_zero : eLpNorm (f - g) 1 μ = 0 := by
    apply le_antisymm
    · -- Show ‖f-g‖₁ ≤ ε for all ε > 0
      sorry -- standard ε-δ from h_triangle and h_rhs_tendsto
    · exact eLpNorm_nonneg _

  -- Translate to a.e. equality
  have h_ae : f - g =ᵐ[μ] 0 := by
    -- Use eLpNorm_eq_zero_iff for p=1
    sorry

  -- Conclude f =ᵐ g
  simpa [Filter.EventuallyEq.sub_eq, Pi.sub_def] using h_ae
```

**Key lemmas needed:**
- `eLpNorm_add_le` (triangle inequality)
- `eLpNorm_eq_zero_iff` (norm zero ⟺ equality a.e.)

---

### 1.2. Finset Indicator Sums (`CesaroConvergence.lean:1158,1161,1164`)

**Goal:** Show
```
∑ k < n, Z k ω = ∑ i : Fin m, (if i < n then 1 else 0) * Z i ω
```

**Strategy:**

1. **Rewrite RHS as filtered sum:**
   ```lean
   ∑ i : Fin m, (if i.val < n then 1 else 0) * Z i.val ω
     = ∑ i in Finset.univ.filter (fun i => i.val < n), Z i.val ω
   ```
   Use `Finset.sum_ite` or variant.

2. **Construct bijection:**
   Between `Finset.range n` and `Finset.univ.filter (fun i : Fin m => i.val < n)`
   using `Finset.sum_bij`:
   - `g : ℕ → Fin m := fun k => ⟨k, hk⟩` where `k < n ≤ m`
   - Inverse: `fun i => i.val`

**Lean sketch:**

```lean
have h_sum_n : ∑ k ∈ Finset.range n, Z k ω =
    ∑ i : Fin m, (if i.val < n then 1 else 0) * Z i.val ω := by
  classical
  -- Step 1: sum over range n = sum over filtered Fin m
  have h₁ : ∑ k ∈ Finset.range n, Z k ω =
      ∑ i in Finset.univ.filter (fun i : Fin m => i.val < n), Z i.val ω := by
    refine Finset.sum_bij ?g ?inj ?map ?inv ?inv_mem
    -- g: k ∈ range n ↦ ⟨k, hk⟩ ∈ Fin m
    -- Need to fill in bijection details
    sorry

  -- Step 2: rewrite as indicator-weighted sum
  have h₂ : ∑ i in Finset.univ.filter (fun i : Fin m => i.val < n), Z i.val ω =
      ∑ i : Fin m, (if i.val < n then 1 else 0) * Z i.val ω := by
    -- Use Finset.sum_filter and pull scalar multiplication
    sorry

  exact h₁.trans h₂

-- h_sum_n' is identical with n' instead of n
```

For the final simplification at line 1164:
```lean
rw [h_sum_n, h_sum_n']
simp [p, q, ξ, mul_comm, mul_left_comm, mul_assoc]
-- Should match the form expected by l2_contractability_bound
```

---

### 1.3. Alpha Conditional Expectation Wrapper (`MainConvergence.lean:888`)

**One-liner using existing axiom:**

```lean
theorem alpha_is_conditional_expectation
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (hX_contract : Contractable μ X)
    (hX_meas : ∀ i, Measurable (X i))
    (f : ℝ → ℝ) (hf_meas : Measurable f)
    (alpha : ℕ → Ω → ℝ) :
    ∃ (nu : Ω → Measure ℝ),
      (∀ ω, IsProbabilityMeasure (nu ω)) ∧
      (Measurable fun ω => nu ω (Set.univ)) ∧
      (∀ n, ∀ᵐ ω ∂μ, alpha n ω = ∫ x, f x ∂(nu ω)) := by
  classical
  exact alpha_is_conditional_expectation_packaged X hX_contract hX_meas f hf_meas alpha
```

Later, replace the axiom with actual theorem using `directing_measure_integral`.

---

### 1.4. Probability Measure Dependencies (`MoreL2Helpers.lean:372,382`)

**Line 372 - IsFiniteMeasure instance:**

```lean
haveI : IsFiniteMeasure (directing_measure X hX_contract hX_meas hX_L2 ω) := by
  have hprob := directing_measure_isProbabilityMeasure X hX_contract hX_meas hX_L2 ω
  exact hprob.toIsFiniteMeasure
```

**Line 382 - Measure univ = 1:**

```lean
have h_univ_const : ∀ ω, directing_measure X hX_contract hX_meas hX_L2 ω Set.univ = 1 := by
  intro ω
  have hprob := directing_measure_isProbabilityMeasure X hX_contract hX_meas hX_L2 ω
  simpa using hprob.measure_univ
```

Both use the existing axiom `directing_measure_isProbabilityMeasure`.

---

## 2. Medium/Heavy Lemmas

### 2.1. Tail Measurability (`CesaroConvergence.lean:2279`)

**4-step diagonal subsequence strategy:**

1. **Work in L²(μ) with tail σ-algebras**
   - Let `m_N := TailSigma.tailSigma (fun k => X (N + k))`
   - Each `m_N` is the σ-field from index N onwards

2. **Show block averages form m_N-measurable closed subspace**
   - For `n ≥ N`, `blockAvg f X N n` is `m_N`-measurable
   - L²-closure is range of `condexpL2` onto `m_N` (closed)
   - Any L² limit is `m_N`-measurable

3. **Diagonalize over N**
   - For each N, extract subsequence converging to `α_f^N` (m_N-measurable)
   - Use diagonal subsequence to get single `α_f` for all N

4. **Relate to original limit**
   - Use `L1_unique_of_two_limits` to show limits coincide a.e.
   - Conclude `α_f` belongs to every tail σ-field `m_N`
   - Therefore tail-measurable

**Dependencies:**
- `condexpL2` API
- `Lp` / `MemLp` conversion lemmas
- Closed subspace property for tail-measurable functions

---

### 2.2. Cesàro → Conditional Expectation (`CesaroConvergence.lean:2577,2695`)

**Two tasks:**

1. **Construct α_f and show tail-measurability (line 2577)**
   - Use `tail_measurability_of_blockAvg` once implemented
   - Extract from diagonal subsequence + L² Cauchy estimate

2. **Uniqueness: α_f =ᵐ condExp[f ∘ X 0 | tail] (line 2695)**

   **Strategy:**
   - For any tail event A:
     * Exchangeability + tail invariance → `∫ f(X₀) 1_A = ∫ blockAvg 1_A`
     * Pass n → ∞ using L² convergence → `∫ α_f 1_A = ∫ f(X₀) 1_A`
   - Invoke uniqueness lemma:
     ```lean
     MeasureTheory.ae_eq_of_forall_setIntegral_eq_of_sigmaFinite'
     ```

   **Requirements:**
   - `hm : TailSigma.tailSigma X ≤ m0`
   - `SigmaFinite (μ.trim hm)`
   - Both functions integrable

---

### 2.3. L² → L¹ Conversion (`CesaroConvergence.lean:2766`)

**On probability spaces: ‖f‖₁ ≤ ‖f‖₂**

**Use existing helper:**
```lean
IntegrationHelpers.L2_tendsto_implies_L1_tendsto_of_bounded
  (μ : Measure Ω) [IsProbabilityMeasure μ]
  (f : ℕ → Ω → ℝ) (g : Ω → ℝ)
  (hf_meas : ∀ n, Measurable (f n))
  (hf_bdd : ∃ M, ∀ n ω, |f n ω| ≤ M)
  (hg_memLp : MemLp g 2 μ)
  (hL2 : Tendsto (fun n => ∫ ω, (f n ω - g ω)^2 ∂μ) atTop (𝓝 0)) :
  Tendsto (fun n => ∫ ω, |f n ω - g ω| ∂μ) atTop (𝓝 0)
```

**Application:**
```lean
have hL1_conv : Tendsto (fun n => ∫ ω, |blockAvg f X 0 n ω - α_f ω| ∂μ) atTop (𝓝 0) := by
  exact L2_tendsto_implies_L1_tendsto_of_bounded
    (f := fun n ω => blockAvg f X 0 n ω)
    (g := α_f)
    (M := 1)  -- using |f| ≤ 1
    (h_bound := ...)
    (hL2 := hα_conv)
```

Then combine with `hα_eq : α_f =ᵐ condExp[f ∘ X 0 | tail]`.

---

### 2.4. Directing Measure Measurability (`MoreL2Helpers.lean:470`)

**Current state:**
- Defined `G := { s | MeasurableSet s ∧ Measurable (ω ↦ ν_ω s) }`
- Showed: ∅ ∈ G, closed under complement, countable disjoint union
- Showed: `Iic t ∈ G` for all t (π-system)
- Have: `borel = generateFrom (Set.range Set.Iic)`

**To complete:**
Use Dynkin system / π-λ theorem from mathlib:

1. **Build Dynkin system:**
   ```lean
   def G' : MeasureTheory.dynkinSystem ℝ :=
   { hasEmpty := h_empty,
     hasCompl := h_compl,
     has_iUnion_nat := h_iUnion }
   ```

2. **Show π-system S ⊆ G':**
   ```lean
   have hS_subset : S ⊆ G' := ...
   ```

3. **Apply π-λ theorem:**
   ```lean
   have h_all : MeasurableSet s → s ∈ G := by
     intro hs
     -- s ∈ Dynkin system generated by S, which ⊆ G
     ...
   ```

**Note:** API-heavy, recommend tackling after probabilistic pieces.

---

### 2.5. Monotone Class & Bridge (`MoreL2Helpers.lean:510,521,569`)

**Three interconnected proofs:**

**Line 510 - Base case (indicators):**
Show for each t:
```lean
alphaIic X ... t ω = ∫ x, 1_{(-∞,t]}(x) d(directing_measure ω)
```
a.e.

**Strategy:**
- Integral of indicator = measure of set
- Identify alphaIic with α from block averages of indicators
- Use definition of directing_measure via Measure.ofCDF

**Line 521 - Monotone class:**
Let C = {f bounded Borel | α_f(ω) = ∫ f dν(ω) a.e.}

**Show:**
1. Indicators of half-lines ∈ C (from line 510)
2. C is vector space (linearity of integral and L¹ limits)
3. C closed under bounded monotone convergence (DCT + diagonal argument)
4. Apply monotone class theorem: C contains all bounded Borel

**Required:**
- `MeasureTheory.integral_add`, `integral_const_mul`
- `MeasureTheory.tendsto_integral_of_monotone_convergence`
- Monotone class API from mathlib

**Line 569 - Bridge property:**
Induction on product length, each step uses:
- Reorder indices (make k(m) maximal via contractability)
- Factor product: `∏_{i≤m} = (∏_{i<m}) · (last factor)`
- Use directing_measure_integral for last factor
- Apply tower property of conditional expectation
- Induction hypothesis on first m factors

**Required:**
- `Finset.prod_bij` (for reindexing)
- `MeasureTheory.condExp_of_stronglyMeasurable` (tower property)
- `ENNReal.lintegral_const_mul`

---

### 2.6. Endpoint Limits of α_{Iic t} (`MainConvergence.lean:2628,2656`)

**Current approach: Pointwise for each ω**

**Issue:** Direct pathwise proofs are delicate; requires careful limit interchange.

**Alternative approach:**
1. Prove endpoint behavior for ν using general probability measure facts
   - For probability measure μ on ℝ: `μ((-∞,t]) → 0` as t → -∞
   - Already in mathlib for probability measures
2. Show `cdf_from_alpha` equals genuine CDF a.e. in ω
3. Endpoint limits follow automatically

**This avoids pathwise lemmas entirely** or weakens to a.e. version.

**If keeping pointwise approach:**
- Use dominated convergence with uniform bounds
- Diagonal argument to interchange Cesàro and threshold limits
- Careful ε-δ based on finite support arguments

---

### 2.7. DCT for Indicators (`CesaroConvergence.lean:2882`)

**Current statement:**
```lean
theorem tendsto_integral_indicator_Iic
  (Xn : ℕ → Ω → ℝ) (X : Ω → ℝ) (t : ℝ)
  (hXn_meas : ∀ n, Measurable (Xn n)) (hX_meas : Measurable X)
  (hae : ∀ᵐ ω, Tendsto (fun n => Xn n ω) atTop (𝓝 (X ω))) :
  Tendsto (fun n => ∫ ω, 1_{(-∞,t]}(Xn n ω) ∂μ) atTop
          (𝓝 (∫ ω, 1_{(-∞,t]}(X ω) ∂μ))
```

**Problem:** FALSE in general without continuity assumption!

The map `x ↦ 1_{(-∞,t]}(x)` is discontinuous at t, so pointwise convergence of Xₙ → X doesn't imply pointwise convergence of indicators when X(ω) = t.

**Options:**

1. **Add continuity assumption:**
   ```lean
   (hcont : μ { ω | X ω = t } = 0)
   ```
   Then DCT applies:
   - On {X < t} and {X > t}: pointwise convergence of indicator
   - On {X = t}: negligible set

2. **Weaken conclusion:**
   - Convergence along subsequence
   - Convergence for "almost every t"
   - More complex, probably not needed

3. **Remove from dependency chain:**
   - If `cdf_from_alpha` uses `ciInf` over rationals of alphaIic
   - Extract endpoint limits directly without this lemma
   - Likely cleaner approach

**Recommendation:** Either add continuity assumption or refactor to avoid this lemma.

---

## 3. Suggested Order of Attack

### Phase 1: Easy Wins (Removes ~7 sorries)
1. ✅ `L1_unique_of_two_limits` (MoreL2Helpers:151)
2. ✅ Finset sums h_sum_n, h_sum_n', simplification (Cesaro:1158,1161,1164)
3. ✅ Probability measure mini-sorries (MoreL2Helpers:372,382)
4. ✅ Alpha conditional expectation wrapper (MainConvergence:888)

### Phase 2: L² Infrastructure (Removes ~3 sorries)
5. ✅ Add/confirm L² → L¹ helper in IntegrationHelpers
6. ✅ Fill L² → L¹ sorry (Cesaro:2766)
7. ✅ Wire helper into cesaro_to_condexp_L2 uniqueness

### Phase 3: Tail Measurability (Removes ~3 sorries)
8. ⚠️ Implement tail_measurability_of_blockAvg (Cesaro:2279)
   - Biggest technical chunk
   - Enables next steps
9. ⚠️ Complete tail-measurability in cesaro_to_condexp_L2 (Cesaro:2577)
10. ⚠️ Complete uniqueness using set-integral equality (Cesaro:2695)

### Phase 4: DCT Reassessment (Removes 1 sorry)
11. ⚠️ Either:
    - Add `μ{X=t} = 0` and complete DCT proof (Cesaro:2882), OR
    - Refactor CDF limits to avoid this lemma

### Phase 5: Carathéodory/Monotone Class (Removes ~10 sorries)
12. ⚠️ directing_measure_measurable final sorry (MoreL2Helpers:470)
13. ⚠️ directing_measure_integral base + monotone class (MoreL2Helpers:510,521)
14. ⚠️ directing_measure_bridge inductive step (MoreL2Helpers:569)
15. ⚠️ Replace cdf_from_alpha_limits axiom using endpoint lemmas
16. ⚠️ Endpoint limits (MainConvergence:2628,2656) - or refactor approach

**Throughout:** Keep axioms (A3, A10, etc.) as named gaps until heavy measure theory is complete.

---

## Key Dependencies

### From Mathlib
- `eLpNorm_add_le` (triangle inequality)
- `eLpNorm_eq_zero_iff` (L^p norm characterization)
- `Finset.sum_bij` (bijective sum reindexing)
- `condexpL2` API (conditional expectation in L²)
- `ae_eq_of_forall_setIntegral_eq_of_sigmaFinite'` (uniqueness via integrals)
- `MeasureTheory.dynkinSystem` (π-λ theorem)
- `tendsto_integral_of_monotone_convergence` (MCT)

### From Project
- `L2_tendsto_implies_L1_tendsto_of_bounded` (IntegrationHelpers)
- `directing_measure_isProbabilityMeasure` (axiom → theorem)
- `cdf_from_alpha_limits` (axiom → theorem)

---

## Notes

- All ViaL2 sorries now have comprehensive documentation
- Proof strategies documented with step-by-step approaches
- Required lemmas explicitly listed
- Dependency chains mapped out
- Build verification: All files compile successfully

**Next steps:** Follow Phase 1 order of attack to systematically eliminate sorries.
