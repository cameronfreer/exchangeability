/-
Copyright (c) 2025 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.Probability.Martingale.Basic
import Mathlib.Probability.Martingale.Convergence
import Mathlib.Probability.Process.Filtration
import Mathlib.Tactic
import Exchangeability.Probability.Martingale.Crossings

/-!
# Martingale Convergence Theorems

The two key results: Lévy's upward and downward theorems for conditional expectations.

## Main Results

- `condExp_tendsto_iInf`: Lévy downward theorem (decreasing filtration)

## References

* Kallenberg, *Probabilistic Symmetries and Invariance Principles* (2005), Section 1
* Durrett, *Probability: Theory and Examples* (2019), Section 5.5
* Williams, *Probability with Martingales* (1991), Theorem 12.12
-/

open Filter MeasureTheory
open scoped Topology ENNReal BigOperators

noncomputable section
open scoped MeasureTheory ProbabilityTheory Topology
open MeasureTheory Filter Set Function

namespace Exchangeability.Probability

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- **Conditional expectation converges along decreasing filtration (Lévy's downward theorem).**

For a decreasing filtration 𝔽ₙ and integrable f, the sequence
  Mₙ := E[f | 𝔽ₙ]
converges a.s. to E[f | ⨅ₙ 𝔽ₙ].

**Proof strategy:** Use the upcrossing inequality approach:
1. Define upcrossings for interval [a,b]
2. Prove upcrossing inequality: E[# upcrossings] ≤ E[|X₀ - a|] / (b - a)
3. Show: finitely many upcrossings a.e. for all rational [a,b]
4. Deduce: the sequence {E[f | 𝔽 n]} converges a.e.
5. Identify the limit as E[f | ⨅ 𝔽 n] using tower property

**Why not use OrderDual reindexing?** See `iSup_ofAntitone_eq_F0`: for antitone F,
we have ⨆ i, F i.ofDual = F 0, not ⨅ n, F n. Applying Lévy's upward theorem would
give convergence to the wrong limit. -/
theorem condExp_tendsto_iInf
    [IsProbabilityMeasure μ]
    {𝔽 : ℕ → MeasurableSpace Ω}
    (h_filtration : Antitone 𝔽)
    (h_le : ∀ n, 𝔽 n ≤ (inferInstance : MeasurableSpace Ω))
    (f : Ω → ℝ) (h_f_int : Integrable f μ) :
    ∀ᵐ ω ∂μ, Tendsto
      (fun n => μ[f | 𝔽 n] ω)
      atTop
      (𝓝 (μ[f | ⨅ n, 𝔽 n] ω)) :=
  ae_limit_is_condexp_iInf h_filtration h_le f h_f_int

/-! ## Implementation notes

`condExp_tendsto_iInf` is proved via the chain:

1. `revFiltration`, `revCEFinite`: Time-reversal infrastructure (`Martingale/Reverse.lean`)
2. `revCE_martingale`: Reversed process is a forward martingale
3. `condExp_exists_ae_limit_antitone`: A.S. existence via upcrossing bounds
   (`Martingale/Crossings.lean`)
4. `uniformIntegrable_condexp_antitone`: Uniform integrability via de la Vallée-Poussin
5. `ae_limit_is_condexp_iInf`: Limit identification via Vitali convergence + tower
6. `condExp_tendsto_iInf`: Wraps step 5

Mathlib dependencies: `Filtration`, `condExp_condExp_of_le` (tower property).
Reverse martingale convergence is *not* available in mathlib; the chain above proves it
locally for the Lévy downward case. -/

end Exchangeability.Probability
