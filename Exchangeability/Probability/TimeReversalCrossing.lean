/-
Copyright (c) 2025 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer, Claude (Anthropic)
-/
import Mathlib.Probability.Martingale.Upcrossing

/-!
# Time-Reversal Crossing Bound

This file contains the proof obligation for the time-reversal crossing bound,
which establishes that upcrossings in a reversed/negated process complete
within the expected time bound.

## Main Results

* `timeReversal_crossing_bound`: For a process X with upcrossings [a→b] before time N,
  the time-reversed negated process Y has its upcrossings [-b→-a] completing at time ≤ N.

## Mathematical Background

The bijection (τ, σ) ↦ (N-σ, N-τ) maps upcrossings of X to upcrossings of the
negated reversed process Y = -X(N-·). The key bound is:
- If X's crossing is at times (τ, σ) with 0 ≤ τ < σ < N
- Then Y's crossing is at times (N-σ, N-τ) with 0 < N-σ < N-τ ≤ N

Since τ ≥ 0, we have N-τ ≤ N, giving the desired bound.

## Implementation Status

This file contains the proof obligation as a `sorry`. The proof requires:
1. Establishing the bijection preserves crossing structure
2. Showing the greedy upcrossing algorithm finds at least as many crossings
3. Proving each bijected crossing completes at target time N-τ ≤ N

## References

* Williams (1991), *Probability with Martingales*, Theorem 11.9 (upcrossing lemma)
* Durrett (2019), *Probability: Theory and Examples*, Section 5.5
-/

open MeasureTheory
open scoped ENNReal

/-- Negation of a stochastic process. -/
def negProcess {Ω : Type*} (X : ℕ → Ω → ℝ) : ℕ → Ω → ℝ :=
  fun n ω => -X n ω

/-- Time reversal of a stochastic process up to time N. -/
def revProcess {Ω : Type*} (X : ℕ → Ω → ℝ) (N : ℕ) : ℕ → Ω → ℝ :=
  fun n ω => X (N - n) ω

/-- **Time-reversal crossing bound.**

For a process X with upcrossings [a→b] before time N, the time-reversed negated process
Y = negProcess (revProcess X N) has its corresponding upcrossings [-b→-a] completing
at time ≤ N.

**Proof obligation:**

The bijection (τ, σ) ↦ (N-σ, N-τ) establishes a 1-1 correspondence between:
- X's upcrossings [a→b] before time N
- Y's upcrossings [-b→-a] ending by time N

The key steps are:
1. **Bijection structure:** If X crosses up from a to b at times (τ, σ),
   then Y = -X(N-·) crosses up from -b to -a at times (N-σ, N-τ).

2. **Time bound:** Since τ ≥ 0 and τ < σ < N:
   - N-σ > 0 (start time is positive)
   - N-τ ≤ N (end time is at most N)

3. **Greedy algorithm:** The mathlib `upperCrossingTime` uses a greedy algorithm.
   We need to show it finds at least k crossings by time N if X has k crossings
   before time N.

The formal proof requires connecting the bijection to the greedy algorithm's behavior.
-/
lemma timeReversal_crossing_bound
    {Ω : Type*} (X : ℕ → Ω → ℝ) (a b : ℝ) (hab : a < b) (N k : ℕ) (ω : Ω)
    (h_k : MeasureTheory.upperCrossingTime a b X N k ω < N)
    (h_neg : -b < -a) :
    MeasureTheory.upperCrossingTime (-b) (-a) (negProcess (revProcess X N)) (N+1) k ω ≤ N := by
  /-
  **Mathematical proof:**

  Let Y := negProcess (revProcess X N), so Y(n) = -X(N-n).

  From h_k, X has k complete upcrossings [a→b] before time N with crossing times
  (τ₁,σ₁), ..., (τₖ,σₖ) where 0 ≤ τ₁ < σ₁ < τ₂ < ... < σₖ < N.

  The bijection (τ, σ) ↦ (N-σ, N-τ) maps these to Y's crossings [-b→-a]:
  - Y(N-σⱼ) = -X(σⱼ) ≤ -b (lower crossing level for Y)
  - Y(N-τⱼ) = -X(τⱼ) ≥ -a (upper crossing level for Y)

  Key observations:
  1. The bijected crossings for Y complete at times N-τₖ < N-τₖ₋₁ < ... < N-τ₁ ≤ N
     (since τ₁ ≥ 0 implies N-τ₁ ≤ N)
  2. Y's greedy algorithm finds crossings in order of completion time
  3. The k-th crossing found by Y's greedy algorithm completes at most by time N-τ₁ ≤ N

  Therefore upperCrossingTime Y k ≤ N.

  **Formal proof status:** Requires showing the greedy algorithm correctly identifies
  the bijected crossings. The key lemma needed is that if valid crossings exist completing
  by time T, then upperCrossingTime ≤ T. This is true by construction of hitting times
  but requires careful unpacking of the recursive definition.
  -/
  -- The full formal proof requires:
  -- 1. Extracting actual crossing times from X's upperCrossingTime structure
  -- 2. Showing the bijected times form valid crossings for Y
  -- 3. Proving the greedy algorithm finds these crossings
  --
  -- For now, we leave this as a proof obligation (sorry) with the understanding
  -- that the mathematical argument is sound - see docstring above.
  sorry
