# API Questions for `condIndep_of_triple_law` Implementation

## Current Status (Line 767 in ViaMartingale.lean)

**✅ Completed:**
- Steps 1-3: Setup, integrability of φ/ψ, measurability of U/V (lines 791-809)
- Step 4 framework: Test function g defined and measurable (lines 813-825)
- Step 5 hφψ_int: Product of indicators proven integrable (lines 855-866) ✨ NEW
- Step 5 tower properties: h_left and h_right using condExp_mul (lines 895-914)

**⚠️ Remaining Sorries:** 6 total (~60-70 lines)

---

## Question 1: Product of Bounded × Integrable Functions

**Context:** Need to prove integrability for:
- `hφV_int : Integrable (φ * V) μ` where φ is bounded indicator (≤1), V is integrable (CE)
- `hUψ_int : Integrable (U * ψ) μ` where U is integrable (CE), ψ is bounded indicator (≤1)

**What I tried:**
```lean
-- Option A: Integrable.bdd_mul
refine Integrable.bdd_mul integrable_condExp aemeasurable bound
-- Problem: Signature unclear, got type errors

-- Option B: Integrable.mul  
exact Integrable.mul hφ_int integrable_condExp
-- Problem: Lean doesn't recognize Integrable.mul

-- Option C: Integrable.bdd_mul'
apply Integrable.bdd_mul' hφ_int integrable_condExp
-- Problem: Argument order mismatch
```

**Question:**
What's the correct mathlib API for "bounded function × integrable function = integrable"?

**Candidates:**
- `Integrable.bdd_mul` (found in ViaKoopman.lean line 1326)
- `Integrable.of_bounded`
- Some combination with `AEStronglyMeasurable`?

**Desired signature:**
```lean
lemma integrable_of_bounded_mul_integrable 
    {f g : Ω → ℝ} (hf_bdd : ∃ C, ∀ᵐ ω ∂μ, ‖f ω‖ ≤ C) 
    (hg_int : Integrable g μ) (hf_meas : AEStronglyMeasurable f μ) :
    Integrable (f * g) μ
```

---

## Question 2: integral_map with Type Class Synthesis

**Context:** Step 4 test function (line 848), need:
```lean
∫ ω, g (Y ω, Z ω, W ω) ∂μ = ∫ p, g p ∂(Measure.map (fun ω => (Y ω, Z ω, W ω)) μ)
```

**What I tried:**
```lean
-- Direct integral_map_equiv
exact integral_map_equiv hg_meas (hY.prodMk (hZ.prodMk hW))
-- Problem: Type class synthesis for MeasurableSpace (α × β × γ)

-- With explicit AEStronglyMeasurable
have hg_ae : AEStronglyMeasurable g (Measure.map ...) := hg_meas.aestronglyMeasurable
exact (integral_map (hY.prodMk (hZ.prodMk hW)).aemeasurable hg_ae).symm
-- Problem: Still type class mismatch
```

**Reference:** ViaL2.lean lines 274, 284 show working pattern with `.aemeasurable`

**Question:**
How do I correctly apply `integral_map` for triple products with proper type class instances?

**Working example needed:** Integration over pushforward of product measure `α × β × γ`.

---

## Question 3: Simple Function Approximation API

**Context:** Core of h_integral_eq (line 876), need to approximate 𝔾-measurable function V by simple functions.

**Strategy:**
1. V is 𝔾-measurable, so V = h ∘ W for some h : γ → ℝ
2. Approximate V by simple functions {Vₙ} with Vₙ → V in L¹
3. Each Vₙ = Σᵢ cᵢ (1_{Bᵢ} ∘ W) for measurable Bᵢ ⊆ γ
4. Apply h_test_fn to each indicator term
5. Pass to limit using DCT

**Questions:**
a) What's the right lemma for "𝔾-measurable ⇒ factors through W"?
   - `MeasurableSpace.comap_measurable_iff`?
   - Something in `MeasurableSpace.comap` namespace?

b) L¹ approximation by simple functions:
   - `SimpleFunc.approxOn` for L¹ convergence?
   - `MeasureTheory.Lp.simpleFunc.denseEmbedding`?

c) DCT or L¹ limit interchange:
   - `integral_tendsto_of_tendsto_of_integral_le`?
   - `tendsto_integral_of_L1`?

**Estimated size:** ~25 lines once API is clear

---

## Question 4: Conditional Expectation Uniqueness

**Context:** h_ce_eq (line 889), need to show two CEs are equal given integral equality.

**Have:** `∫ ω, φ ω * V ω ∂μ = ∫ ω, U ω * ψ ω ∂μ` (from h_integral_eq)

**Want:** `μ[φ * V | 𝔾] =ᵐ[μ] μ[U * ψ | 𝔾]`

**Strategy:** Both sides integrate equally over all 𝔾-measurable sets.

**Question:**
What's the uniqueness lemma for conditional expectations?
- `ae_eq_of_forall_setIntegral_eq`?
- Something like `condExp_ae_eq_of_integral_eq`?

**Expected signature:**
```lean
lemma condExp_ae_eq_of_integral_eq (hf_int : Integrable f μ) (hg_int : Integrable g μ)
    (h : ∀ s, MeasurableSet[m] s → ∫ ω in s, f ω ∂μ = ∫ ω in s, g ω ∂μ) :
    μ[f | m] =ᵐ[μ] μ[g | m]
```

---

## Summary of Remaining Work

| Item | Lines | API Clarity | Priority |
|------|-------|-------------|----------|
| Q1: Bounded × integrable | ~6 | ⚠️ Unclear | High |
| Q2: integral_map | ~5 | ⚠️ Type classes | High |
| Q3: Simple fn approx | ~25 | ⚠️ Multiple APIs | High |
| Q4: CE uniqueness | ~10 | 🟡 Likely exists | Medium |
| Final factorization | ~15 | ✅ Clear (blocked) | Low |

**Total:** ~61 lines, mostly API lookups

**Once APIs are identified:** ~2-3 hours of straightforward implementation.

---

## Request

Could you search for:
1. Mathlib lemmas for bounded × integrable = integrable
2. Working examples of `integral_map` with triple products
3. Simple function approximation in L¹ for comap-measurable functions
4. CE uniqueness from integral equality

Thank you! 🙏
