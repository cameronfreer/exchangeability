/-
Copyright (c) 2025 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Exchangeability.Probability.CondExp
import Exchangeability.DeFinetti.ViaMartingale.ShiftOperations
import Exchangeability.DeFinetti.ViaMartingale.FutureFiltration
import Exchangeability.DeFinetti.ViaMartingale.FutureRectangles

/-!
# Conditional Expectation Convergence from Contractability

This file proves that for contractable processes, conditional expectations
of indicators converge to the tail conditional expectation.

## Main results

* `condexp_convergence` - For k ≤ m, P[X_m ∈ B | θ_{m+1} X] = P[X_k ∈ B | θ_{m+1} X]
* `extreme_members_equal_on_tail` - P[X_m ∈ B | tail] = P[X_0 ∈ B | tail]

These are key steps in the martingale proof of de Finetti's theorem.
-/

noncomputable section
open scoped MeasureTheory
open MeasureTheory

namespace Exchangeability.DeFinetti.ViaMartingale

variable {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]

/-! ### Conditional expectation convergence from contractability -/

/-- **Conditional expectation convergence:** For k ≤ m, all coordinates look
the same when conditioned on the future filtration at level m.

This is the key convergence result: for k ≤ m and measurable set B,
```
P[X_m ∈ B | θ_{m+1} X] = P[X_k ∈ B | θ_{m+1} X]
```

**Proof:** Uses the CE bridge lemma from CondExp.lean with the measure equality from
contractability. The key insight is that deleting coordinates doesn't change the joint distribution
with the future, which implies conditional expectation equality by the bridge lemma. -/
lemma condexp_convergence
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → α} (hX : Contractable μ X)
    (hX_meas : ∀ n, Measurable (X n))
    (k m : ℕ) (hk : k ≤ m)
    (B : Set α) (hB : MeasurableSet B) :
    μ[Set.indicator B (fun _ => (1 : ℝ)) ∘ (X m) | futureFiltration X m]
      =ᵐ[μ]
    μ[Set.indicator B (fun _ => (1 : ℝ)) ∘ (X k) | futureFiltration X m] := by
  -- Use the CE bridge lemma with Y = X m, Y' = X k, Z = shiftRV X (m+1)
  -- The key is that futureFiltration X m = σ(shiftRV X (m+1)) by definition

  -- Get the measure equality from contractability
  have hmeas_eq := contractable_dist_eq hX hX_meas k m hk

  -- Apply the CE bridge lemma
  have h := Exchangeability.Probability.condexp_indicator_eq_of_pair_law_eq
    (X m) (X k) (shiftRV X (m + 1))
    (hX_meas m) (hX_meas k) (measurable_shiftRV hX_meas)
    hmeas_eq hB

  -- Simplify: futureFiltration X m = MeasurableSpace.comap (shiftRV X (m + 1)) inferInstance
  simpa [futureFiltration] using h

/-- Conditional expectations of indicators are equal on the tail σ-algebra.

For any contractable process X and measurable set B,
```
P[X_m ∈ B | tail] = P[X_0 ∈ B | tail]
```

**Proof:** Uses `condexp_convergence` at level m, then applies tower property
since tailSigma ≤ futureFiltration m. -/
lemma extreme_members_equal_on_tail
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → α}
    (hX : Contractable μ X)
    (hX_meas : ∀ n, Measurable (X n))
    (m : ℕ) (B : Set α) (hB : MeasurableSet B) :
    μ[Set.indicator B (fun _ => (1 : ℝ)) ∘ (X m) | tailSigma X]
      =ᵐ[μ]
    μ[Set.indicator B (fun _ => (1 : ℝ)) ∘ (X 0) | tailSigma X] := by
  classical
  set f_m : Ω → ℝ := (Set.indicator B (fun _ => (1 : ℝ))) ∘ X m
  set f_0 : Ω → ℝ := (Set.indicator B (fun _ => (1 : ℝ))) ∘ X 0

  -- equality at the future level m (contractability)
  have h_eq_m :
      μ[f_m | futureFiltration X m] =ᵐ[μ] μ[f_0 | futureFiltration X m] := by
    -- Use condexp_convergence from contractability
    exact condexp_convergence hX hX_meas 0 m (Nat.zero_le m) B hB

  -- condition both sides on the tail
  have h_cond_on_tail :
      μ[μ[f_m | futureFiltration X m] | tailSigma X]
        =ᵐ[μ]
      μ[μ[f_0 | futureFiltration X m] | tailSigma X] :=
    condExp_congr_ae h_eq_m

  -- tower property since tailSigma ≤ futureFiltration m
  have h_tower (f : Ω → ℝ) :
      μ[μ[f | futureFiltration X m] | tailSigma X] =ᵐ[μ] μ[f | tailSigma X] :=
    condExp_condExp_of_le (tailSigma_le_futureFiltration X m) (futureFiltration_le X m hX_meas)

  -- assemble the equalities: μ[f_m|tail] = μ[μ[f_m|fut]|tail] = μ[μ[f_0|fut]|tail] = μ[f_0|tail]
  exact (h_tower f_m).symm.trans (h_cond_on_tail.trans (h_tower f_0))


section reverse_martingale

variable {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {X : ℕ → Ω → α}

/-- 𝔽ₘ := σ(θ_{m+1} X) (the future filtration). -/
abbrev 𝔽 (m : ℕ) : MeasurableSpace Ω := futureFiltration X m

/-- The reverse filtration is decreasing; packaged for the martingale API. -/
lemma filtration_antitone (X : ℕ → Ω → α) : Antitone (fun m => futureFiltration X m) :=
  futureFiltration_antitone X

/-- Mₘ := 𝔼[1_{Xₖ∈B} | 𝔽ₘ].
The reverse martingale sequence for the indicator of X_k in B.

Uses `condExpWith` from CondExp.lean to manage typeclass instances properly. -/
noncomputable
def M (hX_meas : ∀ n, Measurable (X n)) (k : ℕ) (B : Set α) (_hB : MeasurableSet B) :
    ℕ → Ω → ℝ :=
  fun m => Exchangeability.Probability.condExpWith μ (futureFiltration X m)
    (futureFiltration_le X m hX_meas)
    (B.indicator (fun _ => (1 : ℝ)) ∘ X k)

-- TODO (CondExp.lean milestones):
-- (1) `0 ≤ M k B m ω ≤ 1` a.s.
--     API: `condexp_indicator_bounds`.
-- (2) For `m ≤ n`, `M k B n` is `𝔽 n`-measurable and
--     `μ[fun ω => M k B n ω | 𝔽 m] =ᵐ[μ] M k B m`.
--     API: `condexp_tower`, `condexp_stronglyMeasurable`.
-- (3) If `(X m, θₘ X) =^d (X k, θₘ X)`, then
--     `M m B m =ᵐ[μ] M k B m`.
--     API: `condexp_indicator_eq_of_dist_eq_and_le`.
-- (4) `(fun n => M k B n ω)` is a reverse martingale that converges
--     to `μ[Set.indicator B (fun _ => (1 : ℝ)) ∘ (X k) | tailSigma X] ω`.
--     API: `condexp_tendsto_condexp_iInf` (Lévy's downward theorem) together with
--     `filtration_antitone` and `tailSigmaFuture_eq_iInf`.

end reverse_martingale

end Exchangeability.DeFinetti.ViaMartingale
