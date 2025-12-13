# cesaro_to_condexp_L1 Usage Across De Finetti Proofs

## Overview

The axiom `cesaro_to_condexp_L1` states that for a contractable (exchangeable) sequence,
Cesàro averages of bounded measurable functions converge in L¹ to the conditional
expectation onto the tail σ-algebra.

**Mathematical Statement:**
```
For contractable X and bounded measurable f (|f| ≤ 1):
  (1/m) * ∑_{i<m} f(X_i) →_{L¹} E[f(X_0) | tail σ-algebra]
```

This is a **fundamental ergodic-theoretic result** that can be derived from the
Mean Ergodic Theorem.

---

## Usage in the Three Proof Approaches

### 1. ViaL2.lean - **CRITICAL DEPENDENCY**

**Status:** Currently an axiom (line 1609), used once (line 2810)

**Location:** `Exchangeability/DeFinetti/ViaL2.lean`

**Definition:**
```lean
axiom cesaro_to_condexp_L1
  {Ω : Type*} [MeasurableSpace Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ]
  {X : ℕ → Ω → ℝ} (hX_contract : Contractable μ X)
  (hX_meas : ∀ i, Measurable (X i))
  (f : ℝ → ℝ) (hf_meas : Measurable f) (hf_bdd : ∀ x, |f x| ≤ 1) :
  ∀ ε > 0, ∃ (M : ℕ), ∀ (m : ℕ), m ≥ M →
    ∫ ω, |(1 / (m : ℝ)) * ∑ i : Fin m, f (X i ω) -
           (μ[(f ∘ X 0) | TailSigma.tailSigma X] ω)| ∂μ < ε
```

**Usage (line 2810):**
```lean
theorem alphaIicCE_is_L1_limit
  -- ...
  (∀ n, ∀ ε > 0, ∃ M : ℕ, ∀ m : ℕ, m ≥ M →
      ∫ ω, |A n m ω - alphaIicCE X hX_contract hX_meas hX_L2 t ω| ∂μ < ε) := by
    intro n ε hε
    sorry  -- TODO: Apply Helpers.cesaro_to_condexp_L1 with appropriate index handling
```

**Why needed:** The L² approach builds CDFs from Cesàro averages of indicator functions.
Proving these averages converge to conditional expectations is the **key convergence step**.

**Impact of removal:** Eliminates 1 of 11 axioms in ViaL2.lean, completing the first
deep ergodic-theoretic bridge.

---

### 2. ViaKoopman.lean - **INFRASTRUCTURE PRESENT**

**Status:** Already has Mean Ergodic Theorem machinery!

**Location:** `Exchangeability/DeFinetti/ViaKoopman.lean`

**Imports:**
```lean
import Exchangeability.Ergodic.KoopmanMeanErgodic
```

**Key infrastructure (lines 1023-1050):**
```lean
/-- **Bridge lemma**: The Mean Ergodic Theorem projection equals conditional expectation
onto the tail σ-algebra. -/
lemma metProjection_eq_condexp_tail
```

**Usage pattern (line 1890):**
```lean
/-- **Section 3 helper**: L² Mean Ergodic Theorem implies L¹ convergence of Cesàro averages. -/
theorem birkhoffCylinder_tendsto_condexp
  -- Uses Mean Ergodic Theorem for L² convergence
  -- Then transfers to L¹ via Cauchy-Schwarz
```

**Why different:** ViaKoopman works directly with the Koopman operator on path space
and already has the projection = conditional expectation identification. The **same
bridge file** can be used here, or ViaKoopman can continue using its own infrastructure.

**Opportunities:**
- Could refactor to use the same bridge as ViaL2
- Could keep separate (proof diversity)
- The bridge file provides a **canonical reference** both can use

---

### 3. ViaMartingale.lean - **NOT NEEDED**

**Status:** Uses a different proof technique (reverse martingale convergence)

**Approach:** Instead of ergodic theory, ViaMartingale uses:
1. Reverse martingale convergence theorem
2. Direct martingale limit identification

**Relevant axiom (different):**
```lean
-- ViaMartingale uses reverse martingale convergence, not Cesàro averages:
axiom reverseMartingale_convergence_ae
axiom reverseMartingaleLimit_eq
```

**Why not needed:** The martingale approach directly proves convergence to conditional
expectations via martingale convergence theorem, without needing Cesàro averaging.

---

## The Bridge: Mean Ergodic Theorem → cesaro_to_condexp_L1

### What We Have

**From KoopmanMeanErgodic.lean:**
```lean
theorem birkhoffAverage_tendsto_metProjection
    {μ : Measure Ω} [IsProbabilityMeasure μ] (T : Ω → Ω)
    (hT : MeasurePreserving T μ μ) (f : Lp ℝ 2 μ) :
    Tendsto (fun n => birkhoffAverage ℝ (koopman T hT) _root_.id n f)
      atTop (𝓝 (metProjection T hT f))
```

This gives **L² convergence** of Birkhoff averages to an **orthogonal projection**
on path space.

### What We Need (4 Bridges)

**Bridge 1: Contractable → Shift-invariant**
```
Contractable μ X  ⇒  MeasurePreserving shift (μ_path X) (μ_path X)
```
**Status:** Should exist in codebase or be 3-line proof

**Bridge 2: Fixed Space = Tail σ-algebra**
```
metProjection shift = condexp_L2 onto tail σ-algebra
```
**Status:** Standard ergodic theory, one-time identification

**Bridge 3: L² → L¹ Convergence**
```
On probability space: ‖f‖₂ → 0  ⇒  ∫|f| → 0
```
**Status:** Trivial via Hölder (we already have the helper in IntegrationHelpers!)

**Bridge 4: Pullback along Factor Map**
```
E_path[g | tail_path] ∘ pathify  =  E_Ω[g ∘ pathify | tail_process]
```
**Status:** Standard conditional expectation change of variables

### Expected Outcome

After implementing the bridge file `Exchangeability/Bridge/CesaroToCondExp.lean`:
1. Remove axiom from ViaL2.lean (line 1609)
2. Import the bridge and use the theorem (line 2810)
3. ViaL2 axiom count: 11 → 10
4. Provides canonical implementation ViaKoopman can also reference

---

## Implementation Plan

### Phase 1: Create Bridge File ✓ (Next step)
```
Exchangeability/Bridge/CesaroToCondExp.lean
```

### Phase 2: Fill 5 Admits
1. `contractable_shift_invariant_law` - Use existing stationarity lemma
2. `metProjection_eq_condexp_tail_on_path` - One-time identification via fixed space
3. `h_L1` (L² → L¹) - Use `L2_tendsto_implies_L1_tendsto_of_bounded` from IntegrationHelpers!
4. `h_id_birkhoff` - Reindex sums using existing `sum_window_eq_*` lemmas
5. `condexp_pullback_along_pathify` - Standard change of variables

### Phase 3: Replace Axiom in ViaL2
```lean
-- Delete line 1609:
-- axiom cesaro_to_condexp_L1 ...

-- Add import:
import Exchangeability.Bridge.CesaroToCondExp

-- At line 2810, replace sorry with:
exact Exchangeability.Bridge.cesaro_to_condexp_L1 hX_contract hX_meas ...
```

---

## Benefits

**For ViaL2:**
- Removes deep axiom dependency
- Connects L² contractability to conditional expectation rigorously
- Makes proof complete modulo remaining helpers

**For ViaKoopman:**
- Provides alternative formulation
- Canonical bridge between abstract MET and concrete applications
- Potential for code reuse

**For the project:**
- Demonstrates how to connect abstract ergodic theory to concrete probability
- Reusable pattern for other ergodic-theoretic results
- Documentation of the "four bridges" technique

---

## Mathematical Context

The Mean Ergodic Theorem states that for measure-preserving T:

```
Birkhoff averages → orthogonal projection onto fixed-point subspace
```

For the shift on path space:
- **Fixed points** = functions constant on shift orbits = tail-measurable functions
- **Orthogonal projection** onto this space = conditional expectation onto tail σ-algebra

Thus MET directly gives:
```
(1/n) ∑ f ∘ shift^i → E[f | tail]  in L²
```

The bridges simply:
1. Identify the setup (shift-invariance from contractability)
2. Identify the target (projection = conditional expectation)
3. Transfer convergence (L² → L¹)
4. Pull back to the original process (factor map)

This is **exactly the workflow** for applying abstract functional analysis
(MET) to concrete probability theory (exchangeable sequences).
