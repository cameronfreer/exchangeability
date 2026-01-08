# AFM Preparation Checklist

## Code Artifact Preparation (Required)

### Repository Structure
- [ ] Remove WIP branches and experimental code
- [ ] Ensure all files have proper headers and licenses
- [ ] Clean up commented-out code and TODOs
- [x] Comprehensive README.md with build instructions
- [x] CLAUDE.md developer guide exists
- [ ] Add USAGE_EXAMPLES.md with code snippets

### Software Heritage Registration
- [ ] Create account at softwareheritage.org
- [ ] Register GitHub repository
- [ ] Obtain persistent ID (SWHID) for specific commit/tag
- [ ] Include SWHID in paper

### Stable Release
- [ ] Tag version after proof completion (e.g., v1.0.0)
- [ ] Write release notes
- [ ] Link to this tag in paper

### License Verification
- [x] MIT or Apache 2.0 license (already done)
- [ ] Ensure all files have license headers
- [ ] Check mathlib dependency licenses

---

## Paper Preparation (AFM Requirements)

### AFM LaTeX Class
- [ ] Download from AFM website
- [ ] Format paper according to their style
- [ ] Check bibliography format

### Mathematical Accessibility
- [ ] Write introduction for general mathematical audience
- [ ] Minimize proof assistant jargon
- [ ] Explain formalization benefits to mathematicians

### Explicit AFM Virtue Evaluation
- [ ] Create table/section explicitly addressing all 9 virtues
- [ ] Provide evidence for each claim

### Code in Paper
- [ ] Minimal code snippets (AFM guideline)
- [ ] Focus on mathematical content
- [ ] Refer to repository for full details
- [ ] Use syntax highlighting for readability

### arXiv Preparation
- [ ] Create arXiv account
- [ ] Choose appropriate categories (math.LO, cs.LO, cs.MS)
- [ ] Include SWHID in abstract
- [ ] Upload LaTeX source

---

## Supplementary Materials

### Usage Examples Document
- [ ] How to use formalized theorems
- [ ] Example applications
- [ ] Interface documentation

### Dependency Visualization
- [ ] Create dependency graph
- [ ] Show three proof approaches independence
- [ ] Highlight common infrastructure

### Statistics Collection
- [ ] Lines of code per module
- [ ] Theorem count
- [ ] Sorry count over time graph
- [ ] Build time comparisons

---

## Writing Resources to Collect

### Screenshots and Examples
- [ ] Type class error before/after fix
- [ ] Proof state showing `condExpWith` pattern in action
- [ ] Dependency graphs for three proof approaches
- [ ] Statistics: LOC, sorry count over time, build times

### Code Artifacts
- [ ] Clean version of key files for examples
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

## AFM Submission Workflow

### Phase 1: Pre-Writing (Current)
- [x] Complete all three proof approaches
- [ ] Clean up documentation
- [ ] Tag stable release
- [ ] Register SWHID

### Phase 2: Writing
- [ ] Draft introduction
- [ ] Write comparative analysis
- [ ] Document infrastructure contributions
- [ ] Create figures

### Phase 3: Review
- [ ] Internal review
- [ ] Address feedback
- [ ] Polish prose

### Phase 4: Submission
- [ ] Deposit on arXiv
- [ ] Submit to AFM
- [ ] Link SWHID

### Concurrent: Mathlib & Secondary Papers
- [ ] Begin mathlib PR submissions
- [ ] Optionally: ITP/CPP paper on technical patterns

---

## AFM's 9 Virtues - Evidence Tracking

| Virtue | Status | Evidence |
|--------|--------|----------|
| Novelty | Ready | First complete Lean 4 formalization |
| Mathematical insights | Ready | Type mismatches, reformulations documented |
| Generality | Ready | Infrastructure reusable |
| Integration | Partial | Mathlib PR plan documented |
| Reproducibility | Ready | Builds from stable mathlib |
| Complexity | Ready | Advanced probability theory |
| Proof assistant influence | Ready | Type system shaped choices |
| Documentation quality | Ready | Comprehensive docstrings |
| Code readability | Ready | Modern tactics, clear structure |
