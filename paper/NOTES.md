# Technical Lessons & Mathematical Insights

Content extracted and updated from `NotesForLater/PUBLICATION_IDEAS.md`.

---

## Technical Lessons Learned

### Lesson 1: Type Class Resolution is Fragile with Multiple Structures

**What happened:**
- Anonymous instance notation `‹_›` resolved incorrectly in `m ≤ ‹_›`
- Led to vacuous hypothesis `m ≤ m` instead of `m ≤ m₀`
- Blocked 4 critical proofs for hours

**Why it matters:**
- Common pattern in probability: ambient space + sub-σ-algebra
- Affects filtrations, adapted processes, conditional independence
- Not documented in Lean 4 references

**Publication angle:**
- Case study in type class design
- Proposals for better diagnostics
- Pattern documentation for future work

---

### Lesson 2: Proof Approach Affects Formalization Effort Dramatically

**What happened:**
- L² approach: Elementary bounds, minimal dependencies
- Ergodic approach: Requires Koopman operator theory, heavy imports
- Martingale approach: Blocked by missing kernel theory in mathlib

**Why it matters:**
- Choice of proof significantly impacts formalization difficulty
- "Conceptual" proofs may be harder to formalize than "computational" ones
- Mathlib gaps can completely block approaches

**Update (Jan 2026):** ViaMartingale eventually completed first despite initial blockers!

---

### Lesson 3: Proof Restructuring for Reusability

**What happened:**
- L¹ uniqueness lemma initially had inline boundedness proofs
- Abstract helper couldn't prove specific properties of `alphaIicCE`
- 30+ lines of duplicated calc-chain proofs

**The restructuring:**
```lean
-- Before: Try to prove everything inside the helper
lemma h_L1_uniqueness (f g : Ω → ℝ) ... := by
  sorry  -- Can't prove f is bounded without unfolding definition!

-- After: Pass boundedness as hypotheses
lemma h_L1_uniqueness (f g : Ω → ℝ)
    (hf_bdd : ∀ᵐ ω ∂μ, ‖f ω‖ ≤ 1) ... := by
  exact Integrable.of_bound hf 1 hf_bdd

-- Prove specific bounds at call site
apply h_L1_uniqueness
· exact alphaIicCE_nonneg_le_one  -- Reuse existing lemma!
```

**Why it matters:**
- Generic helpers should take properties as hypotheses
- Prove specific properties where you have definition access
- Enables reuse across different instantiations

---

### Lesson 4: Integration Theory Has Surprising Gaps

**What happened:**
- L² → L¹ convergence for bounded functions: Not in mathlib!
- Needed custom `L2_tendsto_implies_L1_tendsto_of_bounded`
- Cauchy-Schwarz specialized to L² not readily available
- Pushforward integral lemmas required boilerplate elimination

**Why it matters:**
- Even "elementary" probability needs infrastructure
- Integration theory still developing in mathlib
- Opportunity for contributions

---

### Lesson 5: Avoiding Heavy Infrastructure via Reformulation

**What happened:**
- ViaKoopman initially needed full Koopman operator theory on L²
- Heavy infrastructure: operator algebras, spectral theory, Mean Ergodic Theorem
- Discovered clever reformulation: "project first, then average" approach

**The insight:**
For T-invariant σ-algebras, conditional expectation commutes with shift:
```
E[f ∘ T | m] = E[f | m]
```

This means Birkhoff averages become **constant sequences** after projection - trivially converge!

**Why it matters:**
- Reduced dependency from "full ergodic theory" to "conditional expectation properties"
- Proof from ~500 lines (with heavy infrastructure) to ~90 lines (self-contained)
- Formalization-driven proof discovery

---

### Lesson 6: Type-Level Mismatches Can Block Entire Approaches

**What happened:**
- ViaKoopman initially planned to use general Mean Ergodic Theorem (MET)
- Koopman operator defined for **ambient** MeasurableSpace
- Our theorem needs conditional expectation on **sub-σ-algebra** `m`
- Type-level mismatch: cannot connect Koopman machinery to sub-σ-algebra

**Why shift-specific version worked:**
- `shiftInvariantSigma` IS the ambient σ-algebra in that construction
- No type mismatch because we constructed the space that way
- But can't generalize to arbitrary (T, m) pairs

**Solution chosen:** "project first, then average" reformulation

**Effort estimates for alternatives (from analysis):**
- Generalize Koopman: 1-2 weeks
- Restriction lemma: 3-5 days
- Direct MET proof: 2-3 weeks
- Clever reformulation: 1 day ✓ (chosen)

---

### Lesson 7: "Unblock-First, Upstream-Second" Strategy (NEW)

**What happened:**
- Identified 3 critical blockers in ViaMartingale proof
- Created local infrastructure lemmas to unblock immediately
- Marked them with TODO for future mathlib contribution
- Proof proceeds while infrastructure can be upstreamed later

**The pattern:**
```lean
/-! ## Local Infrastructure (TODO: Contribute to mathlib) -/

-- TODO: Contribute to Mathlib.Probability.Kernel.CondDistrib
lemma condDistrib_factor_indicator_agree ... := by sorry

-- Application site uses the infrastructure immediately
exact condDistrib_factor_indicator_agree h_law h_le
```

**Results:**
- 3 application blockers → 0 application blockers
- 0 infrastructure sorries → 3 infrastructure sorries
- File compiles ✓
- Clear roadmap for mathlib contributions

---

## Mathematical Insights

### Insight 1: Kallenberg's "Three Proofs" Have Different Formalization Profiles

**Mathematical observation:**
- First proof (Koopman): Deepest connection to ergodic theory
- Second proof (L²): Most elementary, fewest dependencies
- Third proof (Martingale): Most probabilistic, requires kernel theory

**Formalization reveals:**
- L² proof appeared easiest to formalize initially
- Martingale proof completed first despite initial blockers!
- Koopman proof requires substantial ergodic theory infrastructure

**Publication angle:**
- Formalization as a lens for understanding proof complexity
- Different notions of "elementary" in math vs. formalization

---

### Insight 2: The π-System Approach Generalizes Naturally

**Mathematical observation:**
- Cylinder sets form a π-system generating the product σ-algebra
- Measures determined by finite marginals via π-system uniqueness

**Formalization reveals:**
- Pattern works beautifully for infinite products
- Generalizes beyond ℕ → α to arbitrary countable products
- Key to proving exchangeable ⟺ fully exchangeable

---

### Insight 3: Contractability is the "Right" Definition

**Mathematical observation:**
- Three equivalent definitions: contractable, exchangeable, conditionally i.i.d.
- Contractability is least known but most structured

**Formalization reveals:**
- Contractability → exchangeability is easy (permutation extension)
- Exchangeability → conditionally i.i.d. is deep (all three proofs needed)
- Conditionally i.i.d. → contractability is direct (kernel factorization)

---

## Formalization Methodologies

### Methodology 1: Multiple Proof Approaches as Risk Mitigation

**What we did:**
- Started formalizing all three proofs simultaneously
- Discovered ViaL2 was most tractable initially
- ViaMartingale completed first despite late start on blockers
- Kept all three for completeness and comparison

**Why it worked:**
- Mathlib gaps could have blocked any single approach
- Comparison revealed formalization difficulty early
- Provides multiple verification paths for the theorem

---

### Methodology 2: Tactic Modernization as Refactoring

**What we did:**
- Systematically applied modern `fun_prop` tactic across codebase
- Replaced manual measurability composition proofs
- Added `@[fun_prop]` attributes to enable automation

**Why it worked:**
- Reduced proof brittleness
- Improved readability
- Made proofs more maintainable for future mathlib updates

---

### Methodology 3: Pattern Discovery Through Debugging

**What we did:**
- Hit type class errors in CondExp
- Debugged systematically to find root cause
- Discovered `condExpWith` as canonical pattern
- Documented for future use

**Why it worked:**
- Deep understanding of problem led to general solution
- Pattern applies beyond immediate need
- Created reusable knowledge

---

## Course Corrections (Dec-Jan 2026)

### 1. Kallenberg Identification Chain (Dec 3-10)
- Shifted from abstract functional analysis to Kallenberg's precise argument
- Created DirectingMeasure.lean infrastructure
- More concrete distributional arguments

### 2. Kallenberg-Faithful Martingale Refactor (Dec 31)
- Recognized Aldous's approach needed reframing
- Introduced reverse filtration machinery
- Explicit chain lemma connecting revFiltration to tailSigma

### 3. Proof Completion Sprint (Jan 1-3)
- ViaKoopmanContractable achieved zero sorries (Jan 1)
- ViaMartingale stabilized
- ViaL2 addressed final DCT obstacles
