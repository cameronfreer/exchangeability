/-
Copyright (c) 2025 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.Probability.Martingale.Basic
import Mathlib.Probability.Process.Filtration
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.Tactic

/-!
# Reverse Martingale Infrastructure

To prove Lévy's downward theorem, we reverse time on finite horizons to obtain
forward martingales, then apply the upcrossing inequality.

## Main Definitions

- `revFiltration`: Time-reversed filtration on a finite horizon
- `revCEFinite`: Time-reversed conditional expectation process

## Main Results

- `revCEFinite_martingale`: The reversed process is a forward martingale
-/

open Filter MeasureTheory
open scoped Topology ENNReal BigOperators

noncomputable section
open scoped MeasureTheory ProbabilityTheory Topology
open MeasureTheory Filter Set Function

namespace Exchangeability.Probability

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
variable {𝔽 : ℕ → MeasurableSpace Ω}

/-- Reverse filtration on a finite horizon `N`.

For an antitone filtration `𝔽`, define `𝔾ⁿ_k := 𝔽_{N-k}`. Since `k ≤ ℓ` implies
`N - ℓ ≤ N - k`, and `𝔽` is antitone, we get `𝔽_{N-k} ≤ 𝔽_{N-ℓ}`, so `𝔾ⁿ` is
a (forward) increasing filtration. -/
def revFiltration (𝔽 : ℕ → MeasurableSpace Ω) (h_antitone : Antitone 𝔽)
    (h_le : ∀ n, 𝔽 n ≤ (inferInstance : MeasurableSpace Ω))
    (N : ℕ) : Filtration ℕ (inferInstance : MeasurableSpace Ω) where
  seq := fun n => 𝔽 (N - n)
  mono' := by
    intro i j hij
    -- `i ≤ j` implies `N - j ≤ N - i`, then antitone gives `𝔽 (N - i) ≤ 𝔽 (N - j)`.
    have : N - j ≤ N - i := tsub_le_tsub_left hij N
    exact h_antitone this
  le' := fun _ => h_le _

/-- Reverse conditional expectation process at finite horizon `N`.

For `n ≤ N`, this is just `μ[f | 𝔽_{N-n}]`. -/
noncomputable def revCEFinite (f : Ω → ℝ) (𝔽 : ℕ → MeasurableSpace Ω) (N n : ℕ) : Ω → ℝ :=
  μ[f | 𝔽 (N - n)]

/-- The reversed process `revCEFinite f 𝔽 N` is a martingale w.r.t. `revFiltration 𝔽 N`.

**Proof:** For `i ≤ j`, we have `𝔽 (N - j) ≤ 𝔽 (N - i)`, so by the tower property:
  E[revCEFinite N j | revFiltration N i] = E[μ[f | 𝔽_{N-j}] | 𝔽_{N-i}] = μ[f | 𝔽_{N-i}] = revCEFinite N i
-/
lemma revCEFinite_martingale
    [IsProbabilityMeasure μ]
    (h_antitone : Antitone 𝔽) (h_le : ∀ n, 𝔽 n ≤ (inferInstance : MeasurableSpace Ω))
    (f : Ω → ℝ) (_hf : Integrable f μ) (N : ℕ) :
    Martingale (fun n => revCEFinite (μ := μ) f 𝔽 N n) (revFiltration 𝔽 h_antitone h_le N) μ := by
  constructor
  · -- Adapted: revCE N n is 𝔽_{N-n}-measurable
    intro n
    exact stronglyMeasurable_condExp
  · -- Martingale property
    intro i j hij
    simp only [revCEFinite, revFiltration]
    -- Tower: E[μ[f | 𝔽_{N-j}] | 𝔽_{N-i}] = μ[f | 𝔽_{N-i}]
    -- Need: 𝔽_{N-i} ≤ 𝔽_{N-j} (since i ≤ j ⟹ N-j ≤ N-i ⟹ 𝔽(N-i) ≤ 𝔽(N-j))
    have : 𝔽 (N - i) ≤ 𝔽 (N - j) := by
      have : N - j ≤ N - i := tsub_le_tsub_left hij N
      exact h_antitone this
    exact condExp_condExp_of_le this (h_le (N - j))

end Exchangeability.Probability
