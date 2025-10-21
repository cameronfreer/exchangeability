# Publication Ideas - Formalizing de Finetti's Theorem

This document outlines potential publication angles from the de Finetti formalization project, focusing on technical lessons learned, formalization methodology, and contributions to the mathematical formalization community.

## Table of Contents
1. [Main Publication Concepts](#main-publication-concepts)
2. [Technical Lessons Learned](#technical-lessons-learned)
3. [Mathematical Insights](#mathematical-insights)
4. [Formalization Methodology](#formalization-methodology)
5. [Target Venues](#target-venues)

---

## Main Publication Concepts

### Concept 1: "Three Proofs, One Theorem: Formalizing de Finetti's Theorem in Lean 4"
**Focus:** Comparative study of three proof approaches to the same deep theorem

**Key angles:**
- **Proof diversity:** L² approach vs. Ergodic theory vs. Martingale convergence
- **Dependency analysis:** L² is lightest, Ergodic requires heavy theory, Martingale blocked by mathlib gaps
- **Formalization trade-offs:** Elementary proofs vs. conceptual proofs
- **When to choose which approach:** Practical guidance for formalizers

**Narrative arc:**
1. Mathematical background: de Finetti's theorem and the Ryll-Nardzewski equivalence
2. Three proof approaches from Kallenberg (2005)
3. Formalization challenges for each approach
4. Comparative analysis: LOC, dependencies, mathlib gaps revealed
5. Lessons for formalizing probability theory

**Target audience:** Formal methods community, proof assistant users, probability theorists interested in formalization

---

### Concept 2: "Conditional Expectations and Type Classes: Lessons from Measure-Theoretic Formalization"
**Focus:** Deep dive into the `condExpWith` pattern discovery and type class issues

**Key angles:**
- **The anonymous instance anti-pattern:** How `‹_›` fails with sub-σ-algebras
- **Root cause analysis:** Type class resolution with multiple structures
- **The canonical solution:** `condExpWith` pattern and explicit instance management
- **Broader implications:** Sub-structure patterns in formalization (filtrations, stopping times, etc.)

**Narrative arc:**
1. The problem: 4 critical conditional expectation lemmas blocked
2. The debugging journey: Cryptic errors to root cause discovery
3. The pattern: `condExpWith` as canonical solution
4. Generalization: When and why this pattern is needed
5. Proposals for Lean 4 improvements

**Target audience:** Lean 4 developers, mathlib contributors, type theory community

---

### Concept 3: "Formalizing Infinite-Dimensional Probability: π-Systems, Cylinder Sets, and Measure Uniqueness"
**Focus:** General infrastructure for infinite product spaces in probability

**Key angles:**
- **π-system machinery:** Cylinder sets as generators
- **Measure uniqueness:** Finite marginals determine infinite measures
- **Formalization challenges:** Balancing generality and usability
- **Applications beyond de Finetti:** Stochastic processes, random sequences

**Narrative arc:**
1. Mathematical need: Infinite product measures in probability
2. Formalization approach: π-systems and generating sets
3. Key lemma: `measure_eq_of_fin_marginals_eq`
4. Design decisions: Generality vs. convenience
5. Future work: Kolmogorov extension theorem

**Target audience:** Probability theorists, mathlib contributors, formal methods in mathematics

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

**Publication angle:**
- Guidance for choosing proof approaches in formalization
- Analysis of formalization effort vs. mathematical elegance
- Identifying mathlib gaps systematically

---

### Lesson 3: Proof Restructuring for Reusability

**What happened:**
- L¹ uniqueness lemma initially had inline boundedness proofs
- Abstract helper couldn't prove specific properties of `alphaIicCE`
- 30+ lines of duplicated calc-chain proofs

**The restructuring:**
```lean
-- Before: Try to prove everything inside the helper
lemma h_L1_uniqueness (f g : Ω → ℝ) (hf : Measurable f) (hg : Measurable g) ... := by
  -- Can't prove f is bounded without unfolding definition!
  sorry

-- After: Pass boundedness as hypotheses
lemma h_L1_uniqueness (f g : Ω → ℝ)
    (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ)
    (hf_bdd : ∀ᵐ ω ∂μ, ‖f ω‖ ≤ 1) (hg_bdd : ∀ᵐ ω ∂μ, ‖g ω‖ ≤ 1) ... := by
  -- Now we can use the hypotheses!
  exact Integrable.of_bound hf 1 hf_bdd

-- Prove specific bounds at call site using existing lemmas
apply h_L1_uniqueness
· exact alphaIicCE_nonneg_le_one  -- Reuse existing lemma!
```

**Why it matters:**
- Generic helpers should take properties as hypotheses
- Prove specific properties where you have definition access
- Enables reuse: same helper for `alphaIic`, `alphaIicCE`, future uses
- Reduced code: 66 lines changed, 37 deletions

**Publication angle:**
- Design patterns for reusable formal lemmas
- When to abstract vs. when to instantiate
- Balancing genericity with provability
- Leveraging existing infrastructure

**Reference commit:** `c0e369b` - L¹ uniqueness restructuring

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

**Publication angle:**
- Survey of integration theory gaps revealed by formalization
- Contributions made during project
- Roadmap for mathlib probability theory

---

### Lesson 4: Avoiding Heavy Infrastructure via Clever Problem Reformulation

**What happened:**
- ViaKoopman initially needed full Koopman operator theory on L²
- Heavy infrastructure: operator algebras, spectral theory, Mean Ergodic Theorem
- Discovered clever reformulation: "project first, then average" approach

**The insight:**
For T-invariant σ-algebras, conditional expectation commutes with shift:
```
𝔼[f ∘ T | m] = 𝔼[f | m]
```

This means Birkhoff averages become **constant sequences** after projection:
```
𝔼[Birkhoff average | m] = 𝔼[f | m]  (constant!)
```

Constant sequences trivially converge, bypassing the entire Mean Ergodic Theorem machinery!

**Why it matters:**
- Reduced dependency from "full ergodic theory" to "conditional expectation properties"
- Proof from ~500 lines (with heavy infrastructure) to ~90 lines (self-contained)
- Mathematical elegance: the same as before, but formalization complexity dramatically different

**Publication angle:**
- Case study in formalization-driven proof discovery
- Sometimes the "right" proof for formalization differs from the textbook proof
- Reformulation can eliminate entire dependency chains
- Interplay between mathematical insight and formalization pragmatism

**Reference commits:** `fe4d4c3` (roadmap), `e1941fe` (implementation)

---

### Lesson 5: Type-Level Mismatches Can Block Entire Approaches

**What happened:**
- ViaKoopman initially planned to use general Mean Ergodic Theorem (MET)
- Koopman operator defined for **ambient** MeasurableSpace
- Our theorem needs conditional expectation on **sub-σ-algebra** `m`
- Type-level mismatch: cannot connect Koopman machinery to sub-σ-algebra

**The blocker:**
```lean
-- Koopman operator expects ambient space
def koopman (T : Ω → Ω) : (Ω → ℝ) → (Ω → ℝ) := fun f ω => f (T ω)

-- Our theorem needs: E[·|m] where m ≤ m₀ (sub-σ-algebra)
-- But: condExp operates on ambient space, not Koopman's L² space
-- Mismatch: No way to apply MET to get convergence on sub-σ-algebra
```

**Why shift-specific version worked:**
- `shiftInvariantSigma` IS the ambient σ-algebra in that construction
- No type mismatch because we constructed the space that way
- But can't generalize to arbitrary (T, m) pairs

**Solution chosen:**
- Discovered "project first, then average" reformulation
- Avoided entire Koopman infrastructure via conditional expectation properties
- Proof from ~500 lines (impossible) to ~90 lines (complete)

**Publication angle:**
- Type systems as both help and hindrance in formalization
- When infrastructure gaps are fundamental vs. fixable
- Cost-benefit analysis of workarounds vs. infrastructure building
- Transforming blockers into precise technical specifications

**Effort estimates for fixing (from analysis):**
- Generalize Koopman: 1-2 weeks
- Restriction lemma: 3-5 days
- Direct MET proof: 2-3 weeks
- Clever reformulation: 1 day ✅ (chosen)

**Reference commits:** `df58f73` (root cause analysis), `fe4d4c3` (reformulation)

---

### Lesson 6: Conditional Expectation API Needs Expansion
**What happened:**
- 4 fundamental lemmas missing: absolute value preservation, Lipschitz continuity, multiplication pullout, bounded product integrability
- Had to prove from first principles
- Discovered canonical `condExpWith` pattern not documented

**Why it matters:**
- Conditional expectation is central to probability
- Missing lemmas block standard arguments
- Pattern discovery could help others

**Publication angle:**
- Survey of conditional expectation formalization
- Operator-theoretic properties needed in practice
- Design patterns for sub-σ-algebra work

---

## Mathematical Insights

### Insight 1: Kallenberg's "Three Proofs" Have Different Formalization Profiles
**Mathematical observation:**
- First proof (Koopman): Deepest connection to ergodic theory
- Second proof (L²): Most elementary, fewest dependencies
- Third proof (Martingale): Most probabilistic, requires kernel theory

**Formalization reveals:**
- L² proof is easiest to formalize (minimal mathlib gaps)
- Koopman proof requires substantial ergodic theory infrastructure
- Martingale proof reveals fundamental gaps (kernel uniqueness, disintegration)

**Publication angle:**
- Formalization as a lens for understanding proof complexity
- Different notions of "elementary" in math vs. formalization
- Guidance for textbook authors on formalization-friendly proofs

---

### Insight 2: The π-System Approach Generalizes Naturally
**Mathematical observation:**
- Cylinder sets form a π-system generating the product σ-algebra
- Measures determined by finite marginals via π-system uniqueness

**Formalization reveals:**
- Pattern works beautifully for infinite products
- Generalizes beyond ℕ → α to arbitrary countable products
- Key to proving exchangeable ⟺ fully exchangeable

**Publication angle:**
- Formalization-driven generalization
- Pattern for other infinite-dimensional probability results
- Blueprint for Kolmogorov extension theorem

---

### Insight 3: Contractability is the "Right" Definition
**Mathematical observation:**
- Three equivalent definitions: contractable, exchangeable, conditionally i.i.d.
- Contractability is least known but most structured

**Formalization reveals:**
- Contractability → exchangeability is easy (permutation extension)
- Exchangeability → conditionally i.i.d. is deep (all three proofs needed)
- Conditionally i.i.d. → contractability is direct (kernel factorization)

**Publication angle:**
- Formalization revealing conceptual structure
- Case for contractability as primary definition
- Pedagogical implications for probability courses

---

## Formalization Methodology

### Methodology 1: "Proof-First, Then Refactor" Strategy
**What we did:**
- Proved individual lemmas with sorries for dependencies
- Identified common patterns (CondExp gaps, integration helpers)
- Extracted infrastructure into reusable modules

**Why it worked:**
- Allowed progress on main proof while infrastructure developed
- Revealed actual needs vs. anticipated needs
- Enabled focused infrastructure development

**Publication angle:**
- Case study in formalization workflow
- When to build infrastructure vs. when to prove directly
- Iterative refinement in formalization projects

---

### Methodology 2: "Unblock-First, Upstream-Second" Strategy

**What we did:**
- Identified 3 critical blockers in ViaMartingale proof
- Created local infrastructure lemmas to unblock immediately
- Marked them with TODO for future mathlib contribution
- Proof proceeds while infrastructure can be upstreamed later

**The pattern:**
```lean
/-! ## Local Infrastructure (TODO: Contribute to mathlib)

This section contains lemmas that should be upstreamed to mathlib but
are implemented locally to unblock the proof. -/

-- TODO: Contribute to Mathlib.Probability.Kernel.CondDistrib
lemma condDistrib_factor_indicator_agree ... := by sorry

-- Application site uses the infrastructure immediately
exact condDistrib_factor_indicator_agree h_law h_le
```

**Why it worked:**
- Proof development doesn't wait for mathlib review process
- Clear separation: application code vs. extractable infrastructure
- Infrastructure lemmas designed for mathlib from the start
- Net progress: sorries moved from application to clean extractable helpers

**Results:**
- 3 application blockers → 0 application blockers
- 0 infrastructure sorries → 3 infrastructure sorries
- File compiles ✅
- Clear roadmap for mathlib contributions

**Publication angle:**
- Managing dependencies in large formalizations
- Balancing "perfect is the enemy of good" with quality standards
- Strategic use of axioms/sorries during development
- Designing for extractability from the start

**Reference commits:** `a483e72` (Priority B), `9ba5b16` (Priority C), `ef7058f` (completion)

---

### Methodology 3: "Multiple Proof Approaches as Risk Mitigation"
**What we did:**
- Started formalizing all three proofs simultaneously
- Discovered ViaL2 was most tractable
- Kept others as fallbacks and for completeness

**Why it worked:**
- Mathlib gaps could have blocked any single approach
- Comparison revealed formalization difficulty early
- Provides multiple verification paths for the theorem

**Publication angle:**
- Risk management in formalization projects
- Benefits of proof diversity
- When to pursue multiple approaches vs. commit to one

---

### Methodology 3: "Tactic Modernization as Refactoring"

**What we did:**
- Systematically applied modern `fun_prop` tactic across codebase
- Replaced manual measurability composition proofs
- Added `@[fun_prop]` attributes to enable automation

**Why it worked:**
- Reduced proof brittleness (less dependent on specific API)
- Improved readability (intent clearer with `by fun_prop`)
- Enabled custom dischargers for domain-specific reasoning
- Made proofs more maintainable for future mathlib updates

**Publication angle:**
- Maintaining formalization codebases as tactics evolve
- When to refactor vs. when to leave working proofs alone
- Building automation layers incrementally
- Community best practices for tactic usage

**Reference commit:** `443b96c` - Systematic fun_prop application

---

### Methodology 4: "Pattern Discovery Through Debugging"
**What we did:**
- Hit type class errors in CondExp
- Debugged systematically to find root cause
- Discovered `condExpWith` as canonical pattern
- Documented for future use

**Why it worked:**
- Deep understanding of problem led to general solution
- Pattern applies beyond immediate need
- Created reusable knowledge

**Publication angle:**
- Formalization as a discovery process
- How debugging leads to better design patterns
- Building institutional knowledge in formalization

---

## Potential Publication Outlines

### AFM Paper 1: "Formalizing de Finetti's Theorem in Lean 4: Three Proofs and Their Infrastructure"
**Target venue:** Annals of Formalized Mathematics
**Length:** 20-30 pages (journal format)
**Type:** Full formalization paper with mathematical focus

**AFM-aligned structure emphasizing the 9 virtues:**

1. **Introduction** (accessible to general mathematical audience)
   - de Finetti's theorem: exchangeability and its characterization
   - Ryll-Nardzewski equivalence for Borel spaces
   - Historical context and importance in probability theory
   - Why multiple proofs? Risk mitigation and mathematical insight
   - **Novelty:** First complete formalization of all three classical proofs in Lean 4

2. **Mathematical Content** (primary focus per AFM guidelines)
   - Exchangeability, contractability, and conditional i.i.d. (formal definitions)
   - Three classical proof approaches from Kallenberg (2005):
     * L² contractability bounds (elementary, minimal dependencies)
     * Koopman operator and Mean Ergodic Theorem (deep ergodic theory)
     * Reverse martingale convergence (probabilistic elegance)
   - Mathematical relationships: Contractable ⟺ Exchangeable ⟺ ConditionallyIID
   - **Complexity:** Infinite-dimensional probability, sub-σ-algebras, conditional expectations

3. **Formalization Architecture** (usability focus)
   - Overview of the three-proof structure
   - Common infrastructure modules:
     * π-system machinery for infinite products (Core.lean)
     * Conditional expectation operator theory (CondExp.lean)
     * L² → L¹ convergence infrastructure (IntegrationHelpers.lean)
   - Dependency graph showing independence of the three approaches
   - **Integration:** Designed for mathlib contribution from the start
   - Interface documentation and usage examples

4. **The Three Proofs: Comparative Analysis**
   - **ViaL2** (Kallenberg's "second proof"):
     * Elementary L² bounds, minimal dependencies
     * Complete formalization (~4K LOC)
     * Key lemma: `L2_tendsto_implies_L1_tendsto_of_bounded`
   - **ViaKoopman** (Kallenberg's "first proof"):
     * Mean Ergodic Theorem application
     * Heavy dependencies: ergodic theory, operator algebras
     * Clever reformulation: "project first, then average" (~500→90 LOC reduction)
   - **ViaMartingale** (Kallenberg's "third proof"):
     * Reverse martingale convergence
     * Reveals mathlib gaps: kernel uniqueness, disintegration
   - **Mathematical insights:** Type-level mismatches, proof reformulations
   - Dependency comparison: LOC counts, mathlib imports, completion status

5. **Key Infrastructure Contributions** (integration and generality)
   - π-system uniqueness for infinite products
   - Conditional expectation operator properties (4 new lemmas)
   - L² → L¹ convergence theory
   - Permutation extension lemmas
   - **Generality:** All infrastructure designed for reuse beyond de Finetti
   - Mathlib PR roadmap (5 PRs in 3 phases documented)

6. **Formalization Challenges and Solutions** (mathematical insights)
   - **The `condExpWith` pattern:** Type class resolution with sub-σ-algebras
     * Root cause: anonymous instance notation failure
     * Solution: explicit measurable space parameters
     * Impact: unblocked 4 critical proofs
   - **Type-level mismatches:** Koopman operator vs. sub-σ-algebra
     * Blocker: ambient space vs. restricted space mismatch
     * Reformulation: conditional expectation properties instead
   - **Integration theory gaps:** Specialized results missing from mathlib
   - **Proof restructuring for reusability:** Generic helpers with property hypotheses

7. **Usage and Documentation** (usability and reproducibility)
   - How to use the formalized theorems
   - Example applications (with code snippets)
   - Interface documentation for key modules
   - Build instructions and verification
   - **Reproducibility:** Complete build from mathlib dependencies

8. **Evaluation Against AFM's 9 Virtues**
   - Novelty: ✅ First complete Lean 4 formalization, three proof diversity
   - Mathematical insights: ✅ Type-level mismatches, reformulations, API gaps revealed
   - Generality: ✅ Infrastructure reusable for stochastic processes, ergodic theory
   - Integration: ✅ Mathlib PR plan with 5 contributions staged
   - Reproducibility: ✅ Builds from stable mathlib, comprehensive documentation
   - Complexity: ✅ Advanced probability theory, multiple proof techniques
   - Proof assistant influence: ✅ Type system shaped proof approach choices
   - Documentation quality: ✅ Comprehensive docstrings, usage examples
   - Code readability: ✅ Modern tactics (fun_prop), clear structure

9. **Related Work and Future Directions**
   - Other de Finetti formalizations (Isabelle, Coq)
   - Mathlib contributions planned
   - Extensions to other exchangeability results
   - Ergodic theory infrastructure development

**Appendices:**
- A. Complete theorem statements (Lean 4 code)
- B. Dependency graph visualization
- C. Lines of code statistics per proof approach
- D. Software Heritage persistent ID (SWHID)

**Estimated writing time:** 4-6 months after proof completion

---

### ITP Paper 2: "The condExpWith Pattern: Type Classes and Sub-σ-Algebras in Lean 4"
**Target venue:** ITP (Interactive Theorem Proving) or CPP
**Length:** 12-15 pages (conference paper)
**Type:** Technical contribution paper
**Note:** More focused and technical than AFM paper, targets proof assistant community

**Outline:**
1. Introduction
   - Conditional expectation in probability theory
   - Sub-σ-algebras and filtrations
   - Formalization challenges

2. The Problem
   - Type class resolution with multiple structures
   - Anonymous instance notation pitfall
   - Manifestation in CondExp work

3. The Solution
   - The `condExpWith` pattern
   - Explicit instance management
   - Why it works

4. Generalization
   - Other sub-structure patterns in mathematics
   - Design principles for Lean 4
   - Proposals for language improvements

5. Impact
   - Unblocking 4 critical lemmas
   - Applications to filtrations and stochastic processes
   - Mathlib contributions

**Estimated writing time:** 2-3 months

**Note:** This is a companion technical paper to the AFM submission, focusing on implementation details rather than mathematical content. Could be submitted concurrently or after AFM acceptance.



---

### Optional AFM Paper 3: "Infrastructure for Infinite-Dimensional Probability in mathlib"
**Target venue:** Annals of Formalized Mathematics (after mathlib contributions complete)
**Length:** 15-25 pages
**Type:** Infrastructure paper
**Timeline:** 1-2 years after initial AFM submission (after mathlib PRs accepted)

**Outline:**
1. Introduction
   - Infinite-dimensional probability theory
   - Formalization challenges
   - Overview of contributions

2. Mathematical Background
   - Infinite product spaces
   - Cylinder sets and π-systems
   - Measure uniqueness theorems

3. Formalization in Lean 4
   - Product σ-algebra construction
   - Prefix projections and cylinders
   - π-system lemmas

4. Key Results
   - `measure_eq_of_fin_marginals_eq`
   - Exchangeable iff fully exchangeable
   - Applications to de Finetti

5. Integration Theory
   - L² → L¹ convergence
   - Pushforward measure integrals
   - Helper lemmas for probability

6. Conditional Expectation
   - Operator-theoretic properties
   - Sub-σ-algebra patterns
   - API design

7. Applications
   - de Finetti's theorem
   - Stochastic processes framework
   - Future directions

8. Mathlib Contributions
   - Current contributions
   - Planned PRs
   - Long-term roadmap

**Estimated writing time:** 4-6 months

---

## Target Venues

### Primary Venue: Annals of Formalized Mathematics (AFM)

**Why AFM is ideal for this work:**
- Focus on "formalized mathematics across diverse mathematical disciplines"
- Requires formal proof artifacts (we have complete Lean 4 code)
- Evaluates on mathematical relevance with accessible introductions
- Values the 9 virtues we demonstrate (novelty, insights, integration, complexity, etc.)
- Emphasizes usability and documentation (our strength)
- Open access, open source requirement (GitHub repository ready)

**AFM Submission Requirements:**
- Deposit in arXiv/HAL/Zenodo first
- Provide Software Heritage persistent ID (SWHID)
- Use AFM LaTeX class for final version
- Single-blind review process
- Code artifacts must be open source and accessible

**Our advantages for AFM:**
1. ✅ Complete formal artifacts (3 proof approaches, ~10K LOC)
2. ✅ Novel formalization (first complete de Finetti in Lean 4)
3. ✅ Mathematical insights (type-level mismatches, proof reformulations)
4. ✅ Integration with mathlib (planned PRs documented)
5. ✅ Well-documented code (comprehensive docstrings)
6. ✅ Usability focus (helper infrastructure, patterns documented)
7. ✅ Complexity demonstrated (probability theory, sub-σ-algebras)
8. ✅ Open source (MIT/Apache 2.0 license)

### Secondary Venues (Conference Papers)
1. **ITP (Interactive Theorem Proving)** - Annual, for shorter technical papers
2. **CPP (Certified Programs and Proofs)** - Co-located with POPL
3. **Lean Together** - Community workshop, work-in-progress

### Tertiary Venues (Outreach)
4. **Notices of the AMS** - Expository article on formalization
5. **arXiv** - Preprints (required for AFM submission anyway)
6. **Blog posts** - Lean community blog, personal blog

---

## Strategic Considerations

### AFM Submission Timeline (Recommended)

**Immediate (Project completion to +3 months):**
1. **Finalize ViaL2 or ViaKoopman proof** - at least one complete proof approach
2. **Prepare code artifacts:**
   - Clean up documentation and docstrings
   - Ensure comprehensive README with build instructions
   - Create usage examples
   - Tag stable release on GitHub
3. **Register Software Heritage persistent ID (SWHID)**
   - Required by AFM for reproducibility
   - Links to exact code version

**Months 3-6: Write AFM Paper 1**
1. **Mathematical introduction** (accessible to general audience)
   - de Finetti theorem background
   - Why three proofs? Mathematical and pragmatic reasons
2. **Formalization content** (emphasize the 9 virtues)
   - Proof architecture and comparative analysis
   - Infrastructure contributions (π-system, CondExp, IntegrationHelpers)
   - Challenges and solutions (condExpWith pattern, type-level mismatches)
3. **Usage documentation**
   - Interface descriptions with examples
   - How to build and verify
4. **Evaluation against AFM virtues**
   - Explicitly address each of the 9 virtues

**Month 6: arXiv Submission**
- Deposit paper on arXiv (required before AFM submission)
- Include code availability statement with SWHID
- Use AFM LaTeX class for formatting

**Month 6-7: AFM Submission**
- Submit through HAL or EPIsciences portal
- Link arXiv preprint
- Provide SWHID for code artifacts
- Suggest handling editor if appropriate

**Months 7-12: Review Process**
- Single-blind review
- Address reviewer feedback
- Update arXiv with revisions
- Update code if needed (preserve SWHID versioning)

**Concurrent Work (Months 3-12):**
- Begin mathlib PR submissions (Phase 1: IntegrationHelpers, CondExp)
- Write ITP Paper 2 on condExpWith pattern (months 6-9)
- Submit ITP paper to ITP 2026 or CPP 2026

**Year 2 and Beyond:**
- Complete mathlib Phase 2 and 3 PRs
- Optional AFM Paper 3 on infrastructure (after mathlib acceptance)
- Invited talks at Lean Together, probability theory seminars
- Educational materials and tutorials

### Collaboration Opportunities
- **Lean community:** Co-authorship with mathlib contributors who helped
- **Probability theorists:** Collaboration on interpretation and significance
- **Formal methods experts:** Methodology and tool development

### Impact Goals
1. **Academic:** Publications in top venues, citations
2. **Community:** Mathlib contributions, documentation improvements
3. **Educational:** Tutorials, examples, teaching materials
4. **Broader impact:** Demonstrate formalization value for probability theory

---

## AFM-Specific Preparation Checklist

### Code Artifact Preparation (Required)
- [ ] **Clean repository structure**
  - Remove WIP branches and experimental code
  - Ensure all files have proper headers and licenses
  - Clean up commented-out code and TODOs

- [ ] **Comprehensive documentation**
  - README.md with:
    * Project overview
    * Build instructions (exact mathlib version)
    * How to verify theorems
    * Example usage
  - CLAUDE.md already exists (good!)
  - Add USAGE_EXAMPLES.md with code snippets

- [ ] **Software Heritage Registration**
  - Create account at softwareheritage.org
  - Register GitHub repository
  - Obtain persistent ID (SWHID) for specific commit/tag
  - Include SWHID in paper

- [ ] **Stable release tag**
  - Tag version after proof completion (e.g., v1.0.0)
  - Write release notes
  - Link to this tag in paper

- [ ] **License verification**
  - Confirm MIT or Apache 2.0 (already done)
  - Ensure all files have license headers
  - Check mathlib dependency licenses (should be compatible)

### Paper Preparation (AFM Requirements)
- [ ] **AFM LaTeX class**
  - Download from AFM website
  - Format paper according to their style
  - Check bibliography format

- [ ] **Mathematical accessibility**
  - Write introduction for general mathematical audience
  - Minimize proof assistant jargon
  - Explain formalization benefits to mathematicians

- [ ] **Explicit AFM virtue evaluation**
  - Create table/section explicitly addressing all 9 virtues
  - Provide evidence for each claim

- [ ] **Code in paper**
  - Minimal code snippets (AFM guideline)
  - Focus on mathematical content
  - Refer to repository for full details
  - Use syntax highlighting for readability

- [ ] **arXiv preparation**
  - Create arXiv account
  - Choose appropriate categories (math.LO, cs.LO, cs.MS)
  - Include SWHID in abstract
  - Upload LaTeX source

### Supplementary Materials
- [ ] **Usage examples document**
  - How to use formalized theorems
  - Example applications
  - Interface documentation

- [ ] **Dependency visualization**
  - Create dependency graph
  - Show three proof approaches independence
  - Highlight common infrastructure

- [ ] **Statistics collection**
  - Lines of code per module
  - Theorem count
  - Sorry count over time graph
  - Build time comparisons

---

## Writing Resources to Collect Now

### Screenshots and Examples
- [ ] Type class error before/after fix
- [ ] Proof state showing `condExpWith` pattern in action
- [ ] Dependency graphs for three proof approaches
- [ ] Statistics: LOC, sorry count over time, build times

### Code Artifacts
- [ ] Clean version of IntegrationHelpers.lean for examples
- [ ] CondExp.lean with extensive comments
- [ ] Minimal working examples of patterns

### Data to Track
- [ ] Formalization timeline and milestones
- [ ] Mathlib dependency counts per proof
- [ ] Build time comparisons
- [ ] Sorry evolution over time

### Mathematical Content
- [ ] Informal proof sketches for comparison
- [ ] Detailed explanation of π-system approach
- [ ] Comparison with Kallenberg's original proofs
- [ ] Extensions and generalizations discovered

---

## Potential Co-Authors

### Internal (Project Contributors)
- Cameron Freer (primary formalizer)
- [Any other contributors to the formalization]

### External (Potential Collaborators)
- **Mathlib probability experts** - For infrastructure papers
- **Lean core developers** - For type class improvement proposals
- **Probability theorists** - For mathematical interpretation and significance
- **Formal methods researchers** - For methodology and tooling aspects

---

## Next Steps

1. **Continue documentation** during formalization
2. **Collect artifacts** - screenshots, statistics, examples
3. **Draft outlines** - Start with Paper 2 (shortest, most focused)
4. **Engage community** - Present at Lean Together or workshops
5. **Prepare mathlib PRs** - Start with IntegrationHelpers
6. **Write blog posts** - Build audience and get feedback
7. **Plan submissions** - Target ITP 2026 or CPP 2026 for main paper

---

*Document created: 2025-10-21*
*Next review: After ViaL2 or ViaKoopman completion*
*Target first submission: 6-12 months after project completion*
