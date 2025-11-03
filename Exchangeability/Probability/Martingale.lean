/-
Copyright (c) 2025 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.Probability.Martingale.Basic
import Mathlib.Probability.Martingale.Convergence
import Mathlib.Probability.Process.Filtration
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

/-!
# Martingale Convergence for De Finetti

This file provides Lévy's upward and downward theorems needed for the martingale proof
of de Finetti's theorem.

## Main Results

- `condExp_tendsto_iSup`: Lévy upward theorem (complete - wraps mathlib)
- `condExp_tendsto_iInf`: Lévy downward theorem (to be proved)

## Implementation Status

Mathlib (as of v4.25.0-rc2) provides:
- `MeasureTheory.tendsto_ae_condExp`: Lévy's upward theorem for increasing filtrations
- No reverse martingale convergence for decreasing filtrations

This file:
- ✅ `condExp_tendsto_iSup`: Wraps mathlib's upward theorem
- ⚠️ `condExp_tendsto_iInf`: To be proved using upcrossing inequality approach

## References

* Kallenberg, *Probabilistic Symmetries and Invariance Principles* (2005), Section 1
* Durrett, *Probability: Theory and Examples* (2019), Section 5.5
* Williams, *Probability with Martingales* (1991), Theorem 12.12
-/

noncomputable section
open scoped MeasureTheory ProbabilityTheory Topology
open MeasureTheory Filter Set Function

namespace Exchangeability.Probability

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-! ## OrderDual Infrastructure

This section shows why reindexing via OrderDual ℕ cannot convert Lévy's upward theorem
into the downward theorem. -/

/-- Package a decreasing family of σ-algebras on `ℕ` as an increasing filtration on `ℕᵒᵈ`.

For a decreasing sequence (𝔽 n) of σ-algebras, this creates an increasing filtration on
`OrderDual ℕ` where `𝔾 i := 𝔽 (ofDual i)`. Since `i ≤ j` in `ℕᵒᵈ` iff `ofDual j ≤ ofDual i`
in `ℕ`, antitonicity of 𝔽 becomes monotonicity of 𝔾. -/
def Filtration.ofAntitone (F : ℕ → MeasurableSpace Ω) (hF : Antitone F)
    (hle : ∀ n, F n ≤ (inferInstance : MeasurableSpace Ω)) :
    Filtration (OrderDual ℕ) (inferInstance : MeasurableSpace Ω) where
  seq := fun i => F (OrderDual.ofDual i)
  mono' := by
    intro i j hij
    exact hF hij
  le' := fun i => hle (OrderDual.ofDual i)

@[simp]
lemma Filtration.ofAntitone_apply (F : ℕ → MeasurableSpace Ω) (hF : Antitone F)
    (hle : ∀ n, F n ≤ (inferInstance : MeasurableSpace Ω)) (i : OrderDual ℕ) :
    (Filtration.ofAntitone F hF hle) i = F (OrderDual.ofDual i) := rfl

/-- For an antitone chain of σ-algebras, the supremum equals the first term.

**Key insight:** For an antitone sequence F : ℕ → MeasurableSpace Ω, we have
  ⨆ i : ℕᵒᵈ, F i.ofDual = F 0
because F n ≤ F 0 for all n (by antitonicity), and F 0 is one of the terms.

**Why the OrderDual approach fails:** This shows that reindexing via ℕᵒᵈ cannot turn
⨆ into ⨅. For example, if F 0 = ⊤ and F n = ⊥ for n > 0, then:
  ⨆ i, F i.ofDual = ⊤  but  ⨅ n, F n = ⊥
Therefore, applying Lévy's upward theorem to the OrderDual filtration would give
convergence to μ[f | F 0], not μ[f | ⨅ n, F n]. -/
lemma iSup_ofAntitone_eq_F0
    (F : ℕ → MeasurableSpace Ω) (hF : Antitone F) :
    (⨆ i : OrderDual ℕ, F i.ofDual) = F 0 := by
  refine le_antisymm ?_ ?_
  · refine iSup_le (fun i => ?_)
    have : (0 : ℕ) ≤ i.ofDual := Nat.zero_le _
    exact hF this
  · have : F 0 ≤ F (OrderDual.ofDual (OrderDual.toDual 0)) := le_rfl
    simpa using (le_iSup_of_le (OrderDual.toDual 0) this)

/-! ## Main Theorems

The two key results: Lévy's upward and downward theorems for conditional expectations. -/

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
      (𝓝 (μ[f | ⨅ n, 𝔽 n] ω)) := by
  sorry -- To be proved using upcrossing inequality

/-- **Conditional expectation converges along increasing filtration (Lévy's upward theorem).**

For an increasing filtration 𝔽ₙ and integrable f, the sequence
  Mₙ := E[f | 𝔽ₙ]
converges a.s. to E[f | ⨆ₙ 𝔽ₙ].

**Implementation:** Direct wrapper around mathlib's `MeasureTheory.tendsto_ae_condExp`
from `Mathlib.Probability.Martingale.Convergence`. -/
theorem condExp_tendsto_iSup
    [IsProbabilityMeasure μ]
    {𝔽 : ℕ → MeasurableSpace Ω}
    (h_filtration : Monotone 𝔽)
    (h_le : ∀ n, 𝔽 n ≤ (inferInstance : MeasurableSpace Ω))
    (f : Ω → ℝ) (h_f_int : Integrable f μ) :
    ∀ᵐ ω ∂μ, Tendsto
      (fun n => μ[f | 𝔽 n] ω)
      atTop
      (𝓝 (μ[f | ⨆ n, 𝔽 n] ω)) := by
  classical
  -- Package 𝔽 as a Filtration
  let ℱ : Filtration ℕ (inferInstance : MeasurableSpace Ω) :=
    { seq   := 𝔽
      mono' := h_filtration
      le'   := h_le }
  -- Apply mathlib's Lévy upward theorem
  exact MeasureTheory.tendsto_ae_condExp (μ := μ) (ℱ := ℱ) f

/-! ## Implementation Notes

**Current Status:**

- ✅ `condExp_tendsto_iSup` (Lévy upward): Complete wrapper around mathlib
- ⚠️ `condExp_tendsto_iInf` (Lévy downward): To be proved

**Unused axioms and infrastructure:** Moved to `MartingaleUnused.lean` for:
- `reverseMartingaleLimit` axiom family
- Uniform integrability infrastructure
- Helper definitions (`revCE`, etc.)

These were exploratory and not used in the critical path (ViaMartingale.lean only
uses `condExp_tendsto_iSup` and `condExp_tendsto_iInf`).

**Path forward for `condExp_tendsto_iInf`:**
Prove using the standard upcrossing inequality approach (~100-200 lines estimated).

**Dependencies from Mathlib:**
- ✅ `MeasureTheory.tendsto_ae_condExp`: Lévy upward (used)
- ✅ `Filtration`: Filtration structure (used)
- ✅ `condExp_condExp_of_le`: Tower property (available)
- ❌ Reverse martingale convergence: Not available (we'll prove it) -/

end Exchangeability.Probability
