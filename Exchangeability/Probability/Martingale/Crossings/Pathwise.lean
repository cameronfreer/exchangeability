/-
Copyright (c) 2025 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

import Exchangeability.Probability.TimeReversalCrossing

/-!
# Crossings: Pathwise Reversal Lemmas

Pathwise reversal lemmas relating upcrossings of a process to downcrossings of its
time reversal. No filtration / integrability content here — this file is the purely
combinatorial / pathwise layer.

## Main Definitions

* `downcrossingsBefore`: Downcrossings before time `N`
* `downcrossings`: Total downcrossings (supremum over all time horizons)

## Main Results

* `up_neg_flip_eq_down`: `up(-b, -a, -X) = down(a, b, X)`
* `down_neg_flip_eq_up`: `down(-b, -a, -X) = up(a, b, X)`
* `upBefore_le_downBefore_rev_succ`: upcrossing–downcrossing inequality
-/

open Filter MeasureTheory
open scoped Topology ENNReal BigOperators

noncomputable section
open scoped MeasureTheory ProbabilityTheory Topology
open MeasureTheory Filter Set Function

namespace Exchangeability.Probability

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
variable {𝔽 : ℕ → MeasurableSpace Ω}

-- `negProcess` and `revProcess` are imported from
-- Exchangeability.Probability.TimeReversalCrossing

/-- Downcrossings before N: defined as upcrossings of negated process with flipped interval.
Returns a random variable Ω → ℕ. -/
noncomputable def downcrossingsBefore {Ω : Type*} (a b : ℝ) (X : ℕ → Ω → ℝ) (N : ℕ) : Ω → ℕ :=
  upcrossingsBefore (-b) (-a) (negProcess X) N

/-- Total downcrossings: supremum over all time horizons. -/
noncomputable def downcrossings {Ω : Type*} (a b : ℝ) (X : ℕ → Ω → ℝ) : Ω → ℝ≥0∞ :=
  fun ω => ⨆ N, ((downcrossingsBefore a b X N ω : ℕ) : ℝ≥0∞)

/-- **Identity 1:** Upcrossings of negated process = downcrossings of original.
Negation flips crossing direction: up(-b, -a, -X) = down(a, b, X). -/
lemma up_neg_flip_eq_down {Ω : Type*} (a b : ℝ) (X : ℕ → Ω → ℝ) :
  upcrossings (-b) (-a) (negProcess X) = downcrossings a b X := by
  funext ω; simp [upcrossings, downcrossings, downcrossingsBefore]

/-- Double negation is identity (used by `simp` below). -/
@[simp] private lemma negProcess_negProcess {Ω : Type*} (X : ℕ → Ω → ℝ) :
    negProcess (negProcess X) = X := by ext; simp [negProcess]

/-- **Identity 2:** Downcrossings of negated process = upcrossings of original.
Negation flips crossing direction: down(-b, -a, -X) = up(a, b, X). -/
private lemma down_neg_flip_eq_up {Ω : Type*} (a b : ℝ) (X : ℕ → Ω → ℝ) :
  downcrossings (-b) (-a) (negProcess X) = upcrossings a b X := by
  unfold downcrossings downcrossingsBefore upcrossings; simp

/-- Helper: hitting respects pointwise equality on [n, m] -/
private lemma hitting_congr {Ω β : Type*} {u v : ℕ → Ω → β} {s : Set β} {n m : ℕ} {ω : Ω}
    (h : ∀ k, n ≤ k → k ≤ m → u k ω = v k ω) :
    MeasureTheory.hittingBtwn u s n m ω = MeasureTheory.hittingBtwn v s n m ω := by
  simp only [MeasureTheory.hittingBtwn]
  by_cases hex : ∃ j ∈ Set.Icc n m, u j ω ∈ s
  · have hex' : ∃ j ∈ Set.Icc n m, v j ω ∈ s := by
      obtain ⟨j, hj, hj_mem⟩ := hex
      refine ⟨j, hj, ?_⟩
      rw [← h j hj.1 hj.2]
      exact hj_mem
    simp only [if_pos hex, if_pos hex']
    congr 1
    ext k
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq]
    constructor
    · intro ⟨hk_Icc, hk_mem⟩
      refine ⟨hk_Icc, ?_⟩
      rw [← h k hk_Icc.1 hk_Icc.2]
      exact hk_mem
    · intro ⟨hk_Icc, hk_mem⟩
      refine ⟨hk_Icc, ?_⟩
      rw [h k hk_Icc.1 hk_Icc.2]
      exact hk_mem
  · have hex' : ¬∃ j ∈ Set.Icc n m, v j ω ∈ s := by
      intro ⟨j, hj, hj_mem⟩
      apply hex
      refine ⟨j, hj, ?_⟩
      rw [h j hj.1 hj.2]
      exact hj_mem
    simp only [if_neg hex, if_neg hex']

/-- Helper: upperCrossingTime respects pointwise equality on [0, N] -/
private lemma upperCrossingTime_congr {Ω : Type*} {a b : ℝ} {f g : ℕ → Ω → ℝ} {N : ℕ} {ω : Ω}
    (h : ∀ n ≤ N, f n ω = g n ω) :
    ∀ k, MeasureTheory.upperCrossingTime a b f N k ω = MeasureTheory.upperCrossingTime a b g N k ω := by
  intro k
  induction k with
  | zero =>
    simp [MeasureTheory.upperCrossingTime_zero]
  | succ n ih =>
    simp only [MeasureTheory.upperCrossingTime_succ_eq]
    have lct_eq : MeasureTheory.lowerCrossingTime a b f N n ω =
                  MeasureTheory.lowerCrossingTime a b g N n ω := by
      simp only [MeasureTheory.lowerCrossingTime]
      rw [ih]
      apply hitting_congr
      intros k hk_lb hk_ub
      exact h k hk_ub
    rw [lct_eq]
    apply hitting_congr
    intros k hk_lb hk_ub
    exact h k hk_ub

/-- Helper: upcrossingsBefore is invariant under pointwise equality on [0, N] -/
lemma upcrossingsBefore_congr {Ω : Type*} {a b : ℝ} {f g : ℕ → Ω → ℝ} {N : ℕ} {ω : Ω}
    (h : ∀ n ≤ N, f n ω = g n ω) :
    upcrossingsBefore a b f N ω = upcrossingsBefore a b g N ω := by
  simp only [upcrossingsBefore]
  congr 1
  ext k
  simp only [Set.mem_setOf_eq]
  rw [upperCrossingTime_congr h]

/-- Index is bounded by completion time when upperCrossingTime < N.
If the n-th crossing completes before time N, then n < N. -/
private lemma upperCrossingTime_lt_imp_index_lt {Ω : Type*} {a b : ℝ} {f : ℕ → Ω → ℝ} {N : ℕ} {n : ℕ} {ω : Ω}
    (hab : a < b) (h : upperCrossingTime a b f N n ω < N) :
    n < N := by
  -- Key insight: upperCrossingTime is strictly increasing on {k | upperCrossingTime k < N}
  -- Therefore k ≤ upperCrossingTime k for such k, giving us k < N.
  --
  -- We prove by strong induction: n ≤ upperCrossingTime n when upperCrossingTime n < N,
  -- which combined with upperCrossingTime n < N gives n < N.
  suffices h_le : n ≤ upperCrossingTime a b f N n ω by omega
  induction n with
  | zero =>
    -- upperCrossingTime 0 = 0, so 0 ≤ 0
    simp only [upperCrossingTime_zero, Pi.bot_apply, bot_eq_zero', le_refl]
  | succ n ih =>
    -- By IH: n ≤ upperCrossingTime n when upperCrossingTime n < N
    -- By upperCrossingTime_lt_succ: upperCrossingTime n < upperCrossingTime (n+1) when latter ≠ N
    -- Combining: n < upperCrossingTime (n+1), so n+1 ≤ upperCrossingTime (n+1)
    have h_neN : upperCrossingTime a b f N (n + 1) ω ≠ N := ne_of_lt h
    have h_strict : upperCrossingTime a b f N n ω < upperCrossingTime a b f N (n + 1) ω :=
      upperCrossingTime_lt_succ hab h_neN
    have h_n_lt : upperCrossingTime a b f N n ω < N := lt_trans h_strict h
    have ih_n : n ≤ upperCrossingTime a b f N n ω := ih h_n_lt
    omega

-- `timeReversal_crossing_bound` is imported from
-- `Exchangeability.Probability.TimeReversalCrossing`.

/-- **Corrected one-way inequality** with shifted horizon on the reversed side.

The bijection (τ, σ) ↦ (N-σ, N-τ) maps X upcrossings to Y upcrossings.
When τ = 0, the reversed crossing completes at time N. With "before N+1" on the
reversed side, this crossing is counted (since N < N+1).

This fixes the boundary issue in `upBefore_le_downBefore_rev`. -/
lemma upBefore_le_downBefore_rev_succ
    {Ω : Type*} (X : ℕ → Ω → ℝ) (a b : ℝ) (hab : a < b) (N : ℕ) :
    (fun ω => upcrossingsBefore a b X N ω)
      ≤ (fun ω => downcrossingsBefore a b (revProcess X N) (N + 1) ω) := by
  classical
  intro ω
  simp only [downcrossingsBefore, upcrossingsBefore]

  by_cases hN : N = 0
  · simp [hN]

  by_cases hemp : {n | upperCrossingTime a b X N n ω < N}.Nonempty
  · have hbdd1 : BddAbove {n | upperCrossingTime a b X N n ω < N} := by
      use N
      simp only [mem_upperBounds, Set.mem_setOf_eq]
      intro n hn
      exact Nat.le_of_lt (upperCrossingTime_lt_imp_index_lt hab hn)

    have hbdd2 : BddAbove {n | upperCrossingTime (-b) (-a) (negProcess (revProcess X N)) (N+1) n ω < N+1} := by
      use N + 1
      simp only [mem_upperBounds, Set.mem_setOf_eq]
      intro n hn
      exact Nat.le_of_lt (upperCrossingTime_lt_imp_index_lt (by linarith) hn)

    have hsub : {n | upperCrossingTime a b X N n ω < N} ⊆
                {n | upperCrossingTime (-b) (-a) (negProcess (revProcess X N)) (N+1) n ω < N+1} := by
      intro n hn
      simp only [Set.mem_setOf_eq] at hn ⊢
      -- With horizon N+1, the bijection works: crossings completing at time N are now counted
      -- since N < N+1. The proof follows the same structure as upBefore_le_downBefore_rev
      -- but the boundary issue is resolved.
      induction n using Nat.strong_induction_on with
      | _ n ih =>
        match n with
        | 0 =>
          simp only [upperCrossingTime_zero]
          exact Nat.zero_lt_succ N
        | k + 1 =>
          -- hn says X has k+1 complete crossings before time N; the bijection
          -- (τ, σ) ↦ (N-σ, N-τ) maps these to Y crossings completing by time N.
          have h_bound : upperCrossingTime (-b) (-a)
              (negProcess (revProcess X N)) (N+1) (k+1) ω ≤ N :=
            timeReversal_crossing_bound X a b hab N (k+1) ω hn
          exact Nat.lt_succ_of_le h_bound

    exact csSup_le_csSup hbdd2 hemp hsub
  · rw [Set.not_nonempty_iff_eq_empty] at hemp
    simp [hemp]

end Exchangeability.Probability
