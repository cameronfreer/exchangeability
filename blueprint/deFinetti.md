# Blueprint: de Finetti's Theorem

This document sketches the route for formalising de Finetti's theorem in
`Exchangeability/DeFinetti.lean`.  It pairs each conceptual step with a
proposed Lean statement so that we can track progress and delegate tasks.

## Statement

*Let `(Ω, μ)` be a probability space and `X : ℕ → Ω → α` a sequence of
random variables taking values in a standard Borel space `α`.  If `X` is
exchangeable then there exists a random probability measure `ξ : Ω →
ProbabilityMeasure α` (the directing measure) such that, conditional on the tail
σ-algebra, the sequence is i.i.d. with law `ξ ω` for almost every `ω`.*

In Lean this target will eventually appear as

```
theorem deFinetti
    {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → α) (hX : Exchangeable μ X) :
    ∃ (ξ : DirectingMeasure Ω α μ),
      CondIID μ X ξ
```

where `CondIID` is a bespoke predicate formalising conditional i.i.d.
behaviour with respect to a directing measure.

## High-Level Plan

1. **Foundations**
   - [ ] Define `Exchangeable μ X` as invariance of finite-dimensional
         distributions under permutations.
   - [ ] Construct the tail σ-algebra via `tailSigmaAlgebra X` and prove the
         usual properties (decreasing family, tail-measurability of shifts).
   - [ ] Specify the notion `DirectingMeasure Ω α μ` including measurability of
         the kernel and tail measurability constraints.
   - [ ] Interprete empirical measures `empiricalMeasure X n` and relate them to
         the process.
   - ✓ The algebraic implications `contractable → exchangeable` and
     `exchangeable → contractable` are staged in
     `Exchangeability/Contractability.lean`.  The "easy" direction uses a
     permutation argument; completing these lemmas finishes the (i) ⇔ (ii) part
     of Theorem 1.1 independently of the probabilistic machinery.

2. **Martingale and convergence tools**
   - [ ] Show that the empirical measures form a reverse martingale with respect
         to the tail filtration.
   - [ ] Apply the martingale convergence theorem to obtain almost sure limits of
         `empiricalMeasure X n` in the weak topology on probability measures.
   - [ ] Upgrade convergence to `L¹` as needed for conditional expectation
         arguments.

3. **Construction of the directing measure**
   - [ ] Define the candidate directing measure `ξ ω` as the almost sure limit of
         `empiricalMeasure X n ω`.
   - [ ] Prove `ξ` is a probability kernel and is tail-measurable.
   - [ ] Establish that conditional on the tail σ-algebra, the variables are
         independent and identically distributed with law `ξ ω`.

4. **Completion**
   - [ ] Translate the probabilistic conclusion into the Lean predicate
         `CondIID μ X ξ` and finish the proof of `deFinetti`.

### Alternative proofs tracked in code

Kallenberg lists three proofs of Theorem 1.1.  The blueprint primarily follows
the ergodic/martingale structure above, but the Lean development keeps the
additional arguments in separate files:

1. `Exchangeability/DeFinetti/KoopmanApproach.lean` – mean ergodic proof.
2. `Exchangeability/DeFinetti/L2Approach.lean` – L² contractability bound.
3. `Exchangeability/DeFinetti/MartingaleApproach.lean` – Aldous' martingale
   proof (new scaffold).
4. `Exchangeability/Contractability.lean` – equivalence between contractability
   and exchangeability used by all approaches.

Project B in `EXCHANGEABILITY_TASKS.md` records the infrastructure needed to
complete the martingale proof, notably the contraction/independence lemma and
the conditional i.i.d. construction from tail limits.

## Intermediate Lemmas and TODOs

| Label | Description | Lean placeholder |
| --- | --- | --- |
| L1 | Exchangeability via finite-dimensional distributions | `Exchangeable` |
| L2 | Tail σ-algebra construction | `tailSigmaAlgebra` |
| L3 | Definition of directing measures | `DirectingMeasure` structure |
| L4 | Empirical measures of prefixes | `empiricalMeasure` |
| L5 | Reverse martingale property | `martingale_empirical` (to add) |
| L6 | Almost sure convergence of empirical measures | `ae_tendsto_empirical` (to add) |
| L7 | Tail measurability and conditional i.i.d. | `condIID_of_exchangeable` (to add) |

Further lemmas will be added as we refine the plan; the labels are intended to
mirror sections in the Lean file.

## References

- Bruno de Finetti, *La prévision: ses lois logiques, ses sources subjectives*
  (1937).
- David Aldous, *Exchangeability and related topics*, École d'Été de
  Probabilités de Saint-Flour XIII (1983).
- Patrick Billingsley, *Probability and Measure*, 3rd edition.

## Next Steps

1. Pin down the precise statement of `Exchangeable μ X` using Mathlib's
   machinery for finite products and permutations.
2. Formalise `tailSigmaAlgebra` with Mathlib's filtrations and tail σ-algebra
   helpers.
3. Extend `DirectingMeasure` with measurability and conditional independence
   fields, checking existing API around probability kernels.
4. Introduce a predicate `CondIID` to express conditional i.i.d. with respect to
   a kernel, then restate the main theorem using it.

Progress on each item should be tracked in this blueprint so that the Lean file
always mirrors the documented plan.
