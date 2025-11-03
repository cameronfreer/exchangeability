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

/-! ## Reverse Martingale Infrastructure

To prove Lévy's downward theorem, we reverse time on finite horizons to obtain
forward martingales, then apply the upcrossing inequality. -/

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
    have : N - j ≤ N - i := Nat.sub_le_sub_left N hij
    exact h_antitone this
  le' := fun _ => h_le _

/-- Reverse conditional expectation process at finite horizon `N`.

For `n ≤ N`, this is just `μ[f | 𝔽_{N-n}]`. -/
noncomputable def revCE (f : Ω → ℝ) (𝔽 : ℕ → MeasurableSpace Ω) (N n : ℕ) : Ω → ℝ :=
  μ[f | 𝔽 (N - n)]

/-- The reversed process `revCE f 𝔽 N` is a martingale w.r.t. `revFiltration 𝔽 N`.

**Proof:** For `i ≤ j`, we have `𝔽 (N - j) ≤ 𝔽 (N - i)`, so by the tower property:
  E[revCE N j | revFiltration N i] = E[μ[f | 𝔽_{N-j}] | 𝔽_{N-i}] = μ[f | 𝔽_{N-i}] = revCE N i
-/
lemma revCE_martingale
    [IsProbabilityMeasure μ]
    (h_antitone : Antitone 𝔽) (h_le : ∀ n, 𝔽 n ≤ (inferInstance : MeasurableSpace Ω))
    (f : Ω → ℝ) (hf : Integrable f μ) (N : ℕ) :
    Martingale (fun n => revCE (μ := μ) f 𝔽 N n) (revFiltration 𝔽 h_antitone h_le N) μ := by
  constructor
  · -- Adapted: revCE N n is 𝔽_{N-n}-measurable
    intro n
    exact stronglyMeasurable_condExp
  · -- Martingale property
    intro i j hij
    simp only [revCE, revFiltration]
    -- Tower: E[μ[f | 𝔽_{N-j}] | 𝔽_{N-i}] = μ[f | 𝔽_{N-i}]
    have : 𝔽 (N - j) ≤ 𝔽 (N - i) := by
      have : N - j ≤ N - i := Nat.sub_le_sub_left N hij
      exact h_antitone this
    exact condExp_condExp_of_le this (h_le (N - j))

/-- L¹ boundedness of conditional expectations.

This is a standard property: `‖μ[f | m]‖₁ ≤ ‖f‖₁`. -/
lemma eLpNorm_one_condExp_le_of_integrable
    {m : MeasurableSpace Ω} (f : Ω → ℝ) (hf : Integrable f μ) :
    eLpNorm (μ[f | m]) 1 μ ≤ eLpNorm f 1 μ :=
  eLpNorm_one_condExp_le_eLpNorm f

/-- A.S. existence of the limit of `μ[f | 𝔽 n]` along an antitone filtration.

This uses the upcrossing inequality applied to the time-reversed martingales to show
that the original sequence has finitely many upcrossings and downcrossings a.e.,
hence converges a.e. -/
lemma condExp_exists_ae_limit_antitone
    [IsProbabilityMeasure μ]
    (h_antitone : Antitone 𝔽) (h_le : ∀ n, 𝔽 n ≤ (inferInstance : MeasurableSpace Ω))
    (f : Ω → ℝ) (hf : Integrable f μ) :
    ∃ X∞, (Integrable X∞ μ ∧
           ∀ᵐ ω ∂μ, Tendsto (fun n => μ[f | 𝔽 n] ω) atTop (𝓝 (X∞ ω))) := by
  sorry  -- TODO: Use upcrossing bounds on reversed martingales

/-- Uniform integrability of `{μ[f | 𝔽 n]}ₙ` for antitone filtration.

This is a direct application of mathlib's `Integrable.uniformIntegrable_condExp`,
which works for any family of sub-σ-algebras (not just filtrations). -/
lemma uniformIntegrable_condexp_antitone
    [IsProbabilityMeasure μ]
    (h_antitone : Antitone 𝔽) (h_le : ∀ n, 𝔽 n ≤ (inferInstance : MeasurableSpace Ω))
    (f : Ω → ℝ) (hf : Integrable f μ) :
    UniformIntegrable (fun n => μ[f | 𝔽 n]) 1 μ :=
  hf.uniformIntegrable_condExp h_le

/-- Identification: the a.s. limit equals `μ[f | ⨅ n, 𝔽 n]`.

Uses uniform integrability to pass from a.e. convergence to L¹ convergence,
then uses L¹-continuity of conditional expectation to identify the limit. -/
lemma ae_limit_is_condexp_iInf
    [IsProbabilityMeasure μ]
    (h_antitone : Antitone 𝔽) (h_le : ∀ n, 𝔽 n ≤ (inferInstance : MeasurableSpace Ω))
    (f : Ω → ℝ) (hf : Integrable f μ) :
    ∀ᵐ ω ∂μ, Tendsto (fun n => μ[f | 𝔽 n] ω) atTop (𝓝 (μ[f | ⨅ n, 𝔽 n] ω)) := by
  classical
  -- 1) Get a.s. limit X∞
  obtain ⟨X∞, hX∞int, h_tendsto⟩ :=
    condExp_exists_ae_limit_antitone (μ := μ) h_antitone h_le f hf

  -- 2) UI ⟹ L¹ convergence via Vitali
  have hUI := uniformIntegrable_condexp_antitone (μ := μ) h_antitone h_le f hf

  -- Apply Vitali: UI + a.e. tendsto ⟹ L¹ tendsto
  have hL1_conv : Tendsto (fun n => eLpNorm (μ[f | 𝔽 n] - X∞) 1 μ) atTop (𝓝 0) := by
    apply tendsto_Lp_finite_of_tendsto_ae (hp := le_refl 1) (hp' := ENNReal.one_ne_top)
    · intro n; exact integrable_condExp.aestronglyMeasurable
    · exact memℒp_one_iff_integrable.2 hX∞int
    · exact hUI.unifIntegrable
    · exact h_tendsto

  -- 3) Pass limit through condExp at 𝔽∞ := ⨅ n, 𝔽 n
  set 𝔽∞ := iInf 𝔽 with h𝔽∞_def

  -- Tower property: For every n, μ[μ[f | 𝔽 n] | 𝔽∞] = μ[f | 𝔽∞]
  have h_tower : ∀ n, μ[μ[f | 𝔽 n] | 𝔽∞] =ᵐ[μ] μ[f | 𝔽∞] := by
    intro n
    have : 𝔽∞ ≤ 𝔽 n := iInf_le 𝔽 n
    exact condExp_condExp_of_le this (h_le n)

  sorry  -- TODO: Use L¹-continuity of condExp + tower to identify X∞ = μ[f | 𝔽∞]

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
      (𝓝 (μ[f | ⨅ n, 𝔽 n] ω)) :=
  ae_limit_is_condexp_iInf h_filtration h_le f h_f_int

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
- 🚧 `condExp_tendsto_iInf` (Lévy downward): Structure in place, 3 sorries remain

**Proof structure for downward theorem:**

1. ✅ `revFiltration`, `revCE`: Time-reversal infrastructure for finite horizons
2. ✅ `revCE_martingale`: Reversed process is a forward martingale
3. 🚧 `condExp_exists_ae_limit_antitone`: A.S. existence via upcrossing bounds
4. 🚧 `uniformIntegrable_condexp_antitone`: UI via de la Vallée-Poussin
5. 🚧 `ae_limit_is_condexp_iInf`: Limit identification via Vitali + tower
6. ✅ `condExp_tendsto_iInf`: Main theorem (wraps step 5)

**Remaining work (3 sorries):**
- Upcrossing bounds for reverse martingales (step 3)
- de la Vallée-Poussin + Jensen for UI (step 4)
- Vitali convergence + limit identification (step 5)

See `PROOF_PLAN_condExp_tendsto_iInf.md` for detailed mathematical strategy.

**Dependencies from Mathlib:**
- ✅ `MeasureTheory.tendsto_ae_condExp`: Lévy upward (used)
- ✅ `Filtration`: Filtration structure (used)
- ✅ `condExp_condExp_of_le`: Tower property (used)
- ❌ Reverse martingale convergence: Not available (proving it here)
- TODO: Upcrossing inequality, Vitali convergence, de la Vallée-Poussin -/

end Exchangeability.Probability
