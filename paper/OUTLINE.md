# AFM Paper Outline

**Title:** Formalizing de Finetti's Theorem in Lean 4: Three Proofs and Mathematical Insights

**Target:** Annals of Formalized Mathematics (20-30 pages)

---

## 1. Introduction (accessible to general mathematical audience)

- de Finetti's theorem: exchangeability and its characterization
- Ryll-Nardzewski equivalence for Borel spaces
- Historical context and importance in probability theory
- Why multiple proofs? Risk mitigation and mathematical insight
- **Novelty:** First complete formalization of all three classical proofs in Lean 4

## 2. Mathematical Content (primary focus per AFM guidelines)

- Exchangeability, contractability, and conditional i.i.d. (formal definitions)
- Three classical proof approaches from Kallenberg (2005):
  * **L² contractability bounds** - elementary, minimal dependencies
  * **Koopman operator and Mean Ergodic Theorem** - deep ergodic theory
  * **Reverse martingale convergence** - probabilistic elegance
- Mathematical relationships: Contractable ⟺ Exchangeable ⟺ ConditionallyIID
- **Complexity:** Infinite-dimensional probability, sub-σ-algebras, conditional expectations

## 3. Formalization Architecture (usability focus)

- Overview of the three-proof structure
- Common infrastructure modules:
  * π-system machinery for infinite products (Core.lean)
  * Conditional expectation operator theory (CondExp.lean)
  * L² → L¹ convergence infrastructure
- Dependency graph showing independence of the three approaches
- **Integration:** Designed for mathlib contribution from the start
- Interface documentation and usage examples

## 4. The Three Proofs: Comparative Analysis

### 4.1 ViaL2 (Kallenberg's "second proof")
- Elementary L² bounds, minimal dependencies
- Key lemma: `L2_tendsto_implies_L1_tendsto_of_bounded`
- **Status:** COMPLETE

### 4.2 ViaKoopman (Kallenberg's "first proof")
- Mean Ergodic Theorem application
- Heavy dependencies: ergodic theory, operator algebras
- Clever reformulation: "project first, then average"
- **Status:** COMPLETE

### 4.3 ViaMartingale (Kallenberg's "third proof") - Default
- Reverse martingale convergence
- Reveals mathlib gaps: kernel uniqueness, disintegration
- **Status:** COMPLETE

### 4.4 Comparison Table

| Aspect | ViaL2 | ViaKoopman | ViaMartingale |
|--------|-------|------------|---------------|
| Mathematical depth | Elementary | Deep (ergodic) | Medium (martingale) |
| Dependencies | Minimal | Heavy | Medium |
| Key insight | L² bounds | Reformulation | Reverse filtration |
| Status | **COMPLETE** | **COMPLETE** | **COMPLETE** |

## 5. "Equation Archeology": Formalization as Explanation (NEW CONTRIBUTION)

- Case study: Kallenberg's equation chain (1.2)
- How formalization reveals the "why" behind each step
- Extracted general lemmas as certified explanations:
  * Tower property: `condExp_condExp_le`
  * Fixed point property: `condExp_of_stronglyMeasurable`
- Meta-principle: Formalized lemmas document mathematical reasoning
- Benefit: Textbooks could cite formalized lemmas for justification
- Transforms "obvious to experts" into "verified and explained"

## 6. Key Infrastructure Contributions (integration and generality)

- π-system uniqueness for infinite products
- Conditional expectation operator properties (4 new lemmas)
- L² → L¹ convergence theory
- Permutation extension lemmas
- **Generality:** All infrastructure designed for reuse beyond de Finetti
- Mathlib PR roadmap

## 7. Formalization Challenges and Solutions (mathematical insights)

### 7.1 The `condExpWith` Pattern
- Type class resolution with sub-σ-algebras
- Root cause: anonymous instance notation failure
- Solution: explicit measurable space parameters
- Impact: unblocked 4 critical proofs

### 7.2 Type-Level Mismatches
- Koopman operator vs. sub-σ-algebra mismatch
- Blocker: ambient space vs. restricted space
- Solution: reformulation via conditional expectation properties

### 7.3 Integration Theory Gaps
- Specialized results missing from mathlib

### 7.4 Proof Restructuring for Reusability
- Generic helpers with property hypotheses

## 8. Usage and Documentation (usability and reproducibility)

- How to use the formalized theorems
- Example applications (with code snippets)
- Interface documentation for key modules
- Build instructions and verification
- **Reproducibility:** Complete build from mathlib dependencies

## 9. Evaluation Against AFM's 9 Virtues

| Virtue | Evidence |
|--------|----------|
| Novelty | First complete Lean 4 formalization, three proof diversity |
| Mathematical insights | Type-level mismatches, reformulations, API gaps revealed |
| Generality | Infrastructure reusable for stochastic processes, ergodic theory |
| Integration | Mathlib PR plan with contributions staged |
| Reproducibility | Builds from stable mathlib, comprehensive documentation |
| Complexity | Advanced probability theory, multiple proof techniques |
| Proof assistant influence | Type system shaped proof approach choices |
| Documentation quality | Comprehensive docstrings, usage examples |
| Code readability | Modern tactics (fun_prop), clear structure |

## 10. Related Work and Future Directions

- Other de Finetti formalizations (Isabelle, Coq - if any)
- Mathlib contributions planned
- Extensions to other exchangeability results
- Ergodic theory infrastructure development

---

## Appendices

- A. Complete theorem statements (Lean 4 code)
- B. Dependency graph visualization
- C. Lines of code statistics per proof approach
- D. Software Heritage persistent ID (SWHID)

---

## Writing Notes

**Estimated length:** 20-30 pages
**Estimated writing time:** 4-6 months after proof completion
**Key figures needed:**
- Dependency graph
- Three-proof architecture diagram
- Sorry count evolution over time
