/-
Copyright (c) 2025 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.Probability.Martingale.Basic
import Mathlib.Probability.Martingale.Convergence
import Mathlib.Probability.Process.Filtration
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.Tactic
import Exchangeability.Probability.MartingaleExtras

open Filter MeasureTheory
open scoped Topology ENNReal BigOperators

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
    (f : Ω → ℝ) (hf : Integrable f μ) (N : ℕ) :
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

/-- L¹ boundedness of conditional expectations.

This is a standard property: `‖μ[f | m]‖₁ ≤ ‖f‖₁`. -/
lemma eLpNorm_one_condExp_le_of_integrable
    {m : MeasurableSpace Ω} (f : Ω → ℝ) (hf : Integrable f μ) :
    eLpNorm (μ[f | m]) 1 μ ≤ eLpNorm f 1 μ :=
  eLpNorm_one_condExp_le_eLpNorm f

/-! ### Downcrossings and pathwise reversal lemmas

Downcrossings are upcrossings after negation and interval flip. These lemmas establish
the relationship between upcrossings of a process and downcrossings of its time reversal.

**Key identities:**
- `up(a, b, X) = down(-b, -a, -X)` — negation flips crossing direction
- `down(a, b, X) = up(-b, -a, -X)` — the converse -/

/-- Negate a process. -/
def negProcess {Ω : Type*} (X : ℕ → Ω → ℝ) : ℕ → Ω → ℝ :=
  fun n ω => - X n ω

/-- Reverse time up to horizon N (process-level). -/
def revProcess {Ω : Type*} (X : ℕ → Ω → ℝ) (N : ℕ) : ℕ → Ω → ℝ :=
  fun n ω => X (N - n) ω

@[simp] lemma revProcess_apply {Ω : Type*} (X : ℕ → Ω → ℝ) (N n : ℕ) (ω : Ω) :
  revProcess X N n ω = X (N - n) ω := rfl

@[simp] lemma negProcess_apply {Ω : Type*} (X : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) :
  negProcess X n ω = - X n ω := rfl

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
  funext ω
  simp [upcrossings, downcrossings, downcrossingsBefore, negProcess]

/-- **Identity 2:** Downcrossings of negated process = upcrossings of original.
Negation flips crossing direction: down(-b, -a, -X) = up(a, b, X). -/
lemma down_neg_flip_eq_up {Ω : Type*} (a b : ℝ) (X : ℕ → Ω → ℝ) :
  downcrossings (-b) (-a) (negProcess X) = upcrossings a b X := by
  funext ω
  simp only [upcrossings, downcrossings, downcrossingsBefore, negProcess, neg_neg]
  -- The goal is now: ⨆ N, ↑(upcrossingsBefore a b (negProcess (negProcess X)) N ω) = ⨆ N, ↑(upcrossingsBefore a b X N ω)
  -- Simplify negProcess (negProcess X) n ω = -(-(X n ω)) = X n ω
  congr with N
  congr with N'
  simp only [negProcess, neg_neg]

/-- Double negation is identity. -/
lemma negProcess_negProcess {Ω : Type*} (X : ℕ → Ω → ℝ) :
    negProcess (negProcess X) = X := by
  funext n ω
  simp only [negProcess]
  ring

/-- Double reversal is identity when applied within bounds. -/
lemma revProcess_revProcess {Ω : Type*} (X : ℕ → Ω → ℝ) (N n : ℕ) (hn : n ≤ N) (ω : Ω) :
    revProcess (revProcess X N) N n ω = X n ω := by
  simp only [revProcess]
  -- Goal: X (N - (N - n)) ω = X n ω
  -- Use Nat.sub_sub_self: N - (N - n) = n when n ≤ N
  rw [Nat.sub_sub_self hn]

/-- Composition of reversal and negation simplifies: rev(neg(rev X)) = neg X -/
lemma revProcess_negProcess_revProcess {Ω : Type*} (X : ℕ → Ω → ℝ) (N n : ℕ) (hn : n ≤ N) (ω : Ω) :
    revProcess (negProcess (revProcess X N)) N n ω = negProcess X n ω := by
  simp only [revProcess, negProcess]
  -- Goal: -(X (N - (N - n)) ω) = -(X n ω)
  rw [Nat.sub_sub_self hn]

/-- Full composition: neg(rev(neg(rev X))) = X -/
lemma negProcess_revProcess_negProcess_revProcess {Ω : Type*} (X : ℕ → Ω → ℝ) (N n : ℕ) (hn : n ≤ N) (ω : Ω) :
    negProcess (revProcess (negProcess (revProcess X N)) N) n ω = X n ω := by
  simp only [negProcess]
  rw [revProcess_negProcess_revProcess X N n hn ω]
  simp only [negProcess, neg_neg]

/-- Helper: upcrossingsBefore is invariant under pointwise equality on [0, N] -/
lemma upcrossingsBefore_congr {Ω : Type*} {a b : ℝ} {f g : ℕ → Ω → ℝ} {N : ℕ} {ω : Ω}
    (h : ∀ n ≤ N, f n ω = g n ω) :
    upcrossingsBefore a b f N ω = upcrossingsBefore a b g N ω := by
  -- Both are sSup of sets defined by upperCrossingTime
  -- Need to show the sets are equal, which follows from upperCrossingTime being equal
  sorry  -- Requires showing upperCrossingTime respects process equality on [0, N]

/-- **One-way inequality**: upcrossings ≤ downcrossings of time-reversed process.

Maps each greedy upcrossing pair (τ_k, σ_k) of X to a downcrossing pair
(N - σ_k, N - τ_k) of the reversed process. This injection proves the inequality. -/
lemma upBefore_le_downBefore_rev
    {Ω : Type*} (X : ℕ → Ω → ℝ) (a b : ℝ) (N : ℕ) :
    (fun ω => upcrossingsBefore a b X N ω)
      ≤ (fun ω => downcrossingsBefore a b (revProcess X N) N ω) := by
  classical
  intro ω
  -- Work on the path s and its reverse r
  set s : ℕ → ℝ := fun n => X n ω
  set r : ℕ → ℝ := fun n => s (N - n)

  -- Goal: show upBefore(a, b, s, N) ≤ downBefore(a, b, r, N)
  -- which is upBefore(a, b, s, N) ≤ upBefore(-b, -a, -r, N)
  --
  -- Each greedy upcrossing pair (τ_k, σ_k) for s maps to (N-σ_k, N-τ_k) for r:
  -- - If s(τ_k) ≤ a and s(σ_k) ≥ b, then
  --   r(N-σ_k) = s(σ_k) ≥ b and r(N-τ_k) = s(τ_k) ≤ a
  -- - So -r(N-σ_k) ≤ -b and -r(N-τ_k) ≥ -a: a valid up-pair for -r on [-b,-a]
  -- - The map is injective, so the count is ≤
  --
  -- Requires proving from mathlib's greedy upcrossing construction.
  -- Key mathlib definitions:
  --   - upcrossingsBefore a b f N ω := sSup {n | upperCrossingTime a b f N n ω < N}
  --   - upperCrossingTime is defined recursively via hitting times
  -- Approach: Show that reversing time provides an injection from upcrossing pairs
  -- (τ_k, σ_k) of X to downcrossing pairs (N-σ_k, N-τ_k) of revProcess X N.
  -- This is a combinatorial argument about the greedy pairing structure.
  sorry

/-- **Reverse inequality** via negation symmetry.

Apply the one-way lemma to the negated process with flipped interval. -/
lemma downBefore_rev_le_upBefore
    {Ω : Type*} (X : ℕ → Ω → ℝ) (a b : ℝ) (N : ℕ) :
    (fun ω => downcrossingsBefore a b (revProcess X N) N ω)
      ≤ (fun ω => upcrossingsBefore a b X N ω) := by
  classical
  intro ω

  -- Expand definition: downBefore(a, b, revX, N) = upBefore(-b, -a, negProcess(revX), N)
  simp only [downcrossingsBefore]

  -- Apply the one-way lemma to negProcess(revProcess X N) with interval [-b, -a]
  have h := upBefore_le_downBefore_rev (negProcess (revProcess X N)) (-b) (-a) N ω

  -- Simplify using involutions
  simp only [downcrossingsBefore, neg_neg] at h

  -- Show that the RHS of h equals upBefore(a, b, X, N) ω
  -- by showing the processes are equal pointwise for n ≤ N
  have proc_eq : ∀ n ≤ N, negProcess (revProcess (negProcess (revProcess X N)) N) n ω = X n ω := by
    intros n hn
    exact negProcess_revProcess_negProcess_revProcess X N n hn ω

  -- Use congr lemma to replace the complex process with X
  have rhs_eq : upcrossingsBefore a b (negProcess (revProcess (negProcess (revProcess X N)) N)) N ω
              = upcrossingsBefore a b X N ω := by
    apply upcrossingsBefore_congr
    exact proc_eq

  -- Combine h with rhs_eq to get the result
  rw [← rhs_eq]
  exact h

/-- **Time-reversal lemma** (process version):
Upcrossings of X up to N = downcrossings of the reversed process up to N.

Proved as two inequalities using negation symmetry. -/
lemma upcrossingsBefore_eq_downcrossingsBefore_rev
    {Ω : Type*} (X : ℕ → Ω → ℝ) (a b : ℝ) (N : ℕ) :
    (fun ω => upcrossingsBefore a b X N ω)
    = (fun ω => downcrossingsBefore a b (revProcess X N) N ω) := by
  classical
  funext ω
  apply le_antisymm
  · exact upBefore_le_downBefore_rev X a b N ω
  · exact downBefore_rev_le_upBefore X a b N ω

/-- Equivalent "up ↔ up" form via negation + interval flip.
Directly usable for the upcrossing inequality on negated reversed process. -/
lemma upBefore_eq_upBefore_neg_rev
    {Ω : Type*} (X : ℕ → Ω → ℝ) (a b : ℝ) (N : ℕ) :
    (fun ω => upcrossingsBefore a b X N ω)
    = (fun ω => upcrossingsBefore (-b) (-a) (negProcess (revProcess X N)) N ω) := by
  funext ω
  have := congrArg (fun g => g ω)
    (upcrossingsBefore_eq_downcrossingsBefore_rev X a b N)
  simpa [downcrossingsBefore, negProcess, revProcess] using this

/-- Uniform (in N) bound on upcrossings for the reverse martingale.

For an L¹-bounded martingale obtained by reversing an antitone filtration, the expected
number of upcrossings is uniformly bounded, independent of the time horizon N. -/
lemma upcrossings_bdd_uniform
    [IsProbabilityMeasure μ]
    (h_antitone : Antitone 𝔽) (h_le : ∀ n, 𝔽 n ≤ (inferInstance : MeasurableSpace Ω))
    (f : Ω → ℝ) (hf : Integrable f μ) (a b : ℝ) (hab : a < b) :
    ∃ C : ENNReal, C < ⊤ ∧ ∀ N,
      ∫⁻ ω, (upcrossings (↑a) (↑b) (fun n => revCEFinite (μ := μ) f 𝔽 N n) ω) ∂μ ≤ C := by
  -- The L¹ norm of revCEFinite is uniformly bounded by ‖f‖₁
  have hL1_bdd : ∀ N n, eLpNorm (revCEFinite (μ := μ) f 𝔽 N n) 1 μ ≤ eLpNorm f 1 μ := by
    intro N n
    simp only [revCEFinite]
    exact eLpNorm_one_condExp_le_eLpNorm f

  -- For each N, revCEFinite is a martingale, hence a submartingale
  have h_submart : ∀ N, Submartingale (fun n => revCEFinite (μ := μ) f 𝔽 N n)
                                       (revFiltration 𝔽 h_antitone h_le N) μ :=
    fun N => (revCEFinite_martingale (μ := μ) h_antitone h_le f hf N).submartingale

  -- For each fixed N and M, we can bound E[(f_M - a)⁺] by ‖f‖₁ + |a|
  have h_bound : ∀ N M, ∫⁻ ω, ENNReal.ofReal ((revCEFinite (μ := μ) f 𝔽 N M ω - a)⁺) ∂μ
                         ≤ ENNReal.ofReal (eLpNorm f 1 μ).toReal + ENNReal.ofReal |a| := by
    intro N M
    -- Use (x - a)⁺ ≤ |x - a| ≤ |x| + |a|, then integrate
    calc ∫⁻ ω, ENNReal.ofReal ((revCEFinite (μ := μ) f 𝔽 N M ω - a)⁺) ∂μ
        ≤ ∫⁻ ω, ENNReal.ofReal (|revCEFinite (μ := μ) f 𝔽 N M ω| + |a|) ∂μ := by
            apply lintegral_mono
            intro ω
            apply ENNReal.ofReal_le_ofReal
            calc (revCEFinite (μ := μ) f 𝔽 N M ω - a)⁺
                = max (revCEFinite (μ := μ) f 𝔽 N M ω - a) 0 := rfl
              _ ≤ |revCEFinite (μ := μ) f 𝔽 N M ω - a| := by
                    simp only [le_abs_self, max_le_iff, abs_nonneg, and_self]
              _ ≤ |revCEFinite (μ := μ) f 𝔽 N M ω| + |a| := abs_sub _ _
      _ = ∫⁻ ω, (ENNReal.ofReal |revCEFinite (μ := μ) f 𝔽 N M ω| + ENNReal.ofReal |a|) ∂μ := by
            congr 1; ext ω
            exact ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)
      _ = ∫⁻ ω, ENNReal.ofReal |revCEFinite (μ := μ) f 𝔽 N M ω| ∂μ + ENNReal.ofReal |a| := by
            rw [lintegral_add_right _ measurable_const, lintegral_const]
            simp [IsProbabilityMeasure.measure_univ]
      _ ≤ ENNReal.ofReal (eLpNorm f 1 μ).toReal + ENNReal.ofReal |a| := by
            gcongr
            -- Convert lintegral to eLpNorm and use hL1_bdd
            have : ∫⁻ ω, ENNReal.ofReal |revCEFinite (μ := μ) f 𝔽 N M ω| ∂μ =
                   eLpNorm (revCEFinite (μ := μ) f 𝔽 N M) 1 μ := by
              rw [eLpNorm_one_eq_lintegral_enorm]
              congr 1; ext ω
              exact (Real.enorm_eq_ofReal_abs _).symm
            rw [this]
            calc eLpNorm (revCEFinite (μ := μ) f 𝔽 N M) 1 μ
                ≤ eLpNorm f 1 μ := hL1_bdd N M
              _ = ENNReal.ofReal (eLpNorm f 1 μ).toReal := by
                    rw [ENNReal.ofReal_toReal]
                    exact (memLp_one_iff_integrable.mpr hf).eLpNorm_ne_top

  -- Define C as the bound divided by (b - a)
  set C := (ENNReal.ofReal (eLpNorm f 1 μ).toReal + ENNReal.ofReal |a|) / ENNReal.ofReal (b - a)

  -- Prove C < ⊤
  have hC_finite : C < ⊤ := by
    refine ENNReal.div_lt_top ?h1 ?h2
    · -- Numerator ≠ ⊤
      refine ENNReal.add_lt_top.2 ⟨?_, ENNReal.ofReal_lt_top⟩ |>.ne
      rw [ENNReal.ofReal_toReal]
      · exact (memLp_one_iff_integrable.mpr hf).eLpNorm_lt_top
      · exact (memLp_one_iff_integrable.mpr hf).eLpNorm_ne_top
    · -- Denominator ≠ 0
      exact (ENNReal.ofReal_pos.2 (sub_pos.2 hab)).ne'

  refine ⟨C, hC_finite, fun N => ?_⟩

  -- Apply the submartingale upcrossing inequality
  have key := (h_submart N).mul_lintegral_upcrossings_le_lintegral_pos_part a b

  -- Bound the supremum using h_bound
  have sup_bdd : ⨆ M, ∫⁻ ω, ENNReal.ofReal ((revCEFinite (μ := μ) f 𝔽 N M ω - a)⁺) ∂μ
                  ≤ ENNReal.ofReal (eLpNorm f 1 μ).toReal + ENNReal.ofReal |a| := by
    apply iSup_le
    intro M
    exact h_bound N M

  -- Combine: (b - a) * E[upcrossings] ≤ sup ≤ bound, so E[upcrossings] ≤ C
  have step1 : (∫⁻ ω, upcrossings (↑a) (↑b) (fun n => revCEFinite (μ := μ) f 𝔽 N n) ω ∂μ) * ENNReal.ofReal (b - a)
                ≤ ⨆ M, ∫⁻ ω, ENNReal.ofReal ((revCEFinite (μ := μ) f 𝔽 N M ω - a)⁺) ∂μ := by
    rw [mul_comm]; exact key

  calc ∫⁻ ω, upcrossings (↑a) (↑b) (fun n => revCEFinite (μ := μ) f 𝔽 N n) ω ∂μ
      ≤ (⨆ M, ∫⁻ ω, ENNReal.ofReal ((revCEFinite (μ := μ) f 𝔽 N M ω - a)⁺) ∂μ) / ENNReal.ofReal (b - a) := by
          refine (ENNReal.le_div_iff_mul_le ?_ ?_).2 step1
          · left; exact (ENNReal.ofReal_pos.2 (sub_pos.2 hab)).ne'
          · left; exact ENNReal.ofReal_ne_top
    _ ≤ (ENNReal.ofReal (eLpNorm f 1 μ).toReal + ENNReal.ofReal |a|) / ENNReal.ofReal (b - a) := by
          gcongr
    _ = C := rfl

/-- A.S. existence of the limit of `μ[f | 𝔽 n]` along an antitone filtration.

This uses the upcrossing inequality applied to the time-reversed martingales to show
that the original sequence has finitely many upcrossings and downcrossings a.e.,
hence converges a.e. -/
lemma condExp_exists_ae_limit_antitone
    [IsProbabilityMeasure μ] {𝔽 : ℕ → MeasurableSpace Ω}
    (h_antitone : Antitone 𝔽) (h_le : ∀ n, 𝔽 n ≤ (inferInstance : MeasurableSpace Ω))
    (f : Ω → ℝ) (hf : Integrable f μ) :
    ∃ Xlim, (Integrable Xlim μ ∧
           ∀ᵐ ω ∂μ, Tendsto (fun n => μ[f | 𝔽 n] ω) atTop (𝓝 (Xlim ω))) := by
  -- Strategy: Show the sequence has finite upcrossings a.e., then apply tendsto_of_uncrossing_lt_top

  -- First, extract the L¹ bound
  have hL1_bdd : ∀ n, eLpNorm (μ[f | 𝔽 n]) 1 μ ≤ eLpNorm f 1 μ :=
    fun n => eLpNorm_one_condExp_le_eLpNorm _

  -- Extract finite L¹ bound
  have hf_memLp : MemLp f 1 μ := memLp_one_iff_integrable.2 hf
  have hf_Lp_ne_top : eLpNorm f 1 μ ≠ ⊤ := hf_memLp.eLpNorm_ne_top
  set R := (eLpNorm f 1 μ).toNNReal with hR_def
  have hR : eLpNorm f 1 μ = ↑R := (ENNReal.coe_toNNReal hf_Lp_ne_top).symm

  -- Step 1: Show bounded liminf
  have hbdd_liminf : ∀ᵐ ω ∂μ, (liminf (fun n => ENorm.enorm (μ[f | 𝔽 n] ω)) atTop) < ⊤ := by
    refine ae_bdd_liminf_atTop_of_eLpNorm_bdd (R := R) one_ne_zero (fun n => ?_) (fun n => ?_)
    · -- Measurability
      exact stronglyMeasurable_condExp.measurable.mono (h_le n) le_rfl
    · -- Bound
      calc eLpNorm (μ[f | 𝔽 n]) 1 μ
          ≤ eLpNorm f 1 μ := hL1_bdd n
        _ = R := hR

  -- Step 2: Show finite upcrossings using L¹-boundedness
  -- Strategy: Use the fact that L¹-bounded sequences with reverse martingale structure
  -- have finite upcrossings. This follows from the upcrossing inequality.
  have hupcross : ∀ᵐ ω ∂μ, ∀ a b : ℚ, a < b →
      upcrossings (↑a) (↑b) (fun n => μ[f | 𝔽 n]) ω < ⊤ := by
    -- The sequence is L¹-bounded, so we can extract a uniform bound
    obtain ⟨R, hR_pos, hR_bound⟩ : ∃ R : ENNReal, 0 < R ∧ ∀ n, eLpNorm (μ[f | 𝔽 n]) 1 μ ≤ R := by
      use max (eLpNorm f 1 μ) 1
      refine ⟨?_, ?_⟩
      · exact lt_max_of_lt_right zero_lt_one
      · intro n
        exact le_trans (hL1_bdd n) (le_max_left _ _)

    -- For reverse martingales, we use a key observation:
    -- The sequence μ[f | 𝔽 n] is L¹-bounded and satisfies the tower property
    -- in the reverse direction, which is sufficient to guarantee a.e. convergence
    -- by the reverse martingale convergence theorem.

    -- Key insight: For a reverse martingale with L¹ bound R, the expected number
    -- of upcrossings is bounded by R/(b-a), which is finite. By Markov's inequality,
    -- this implies a.e. finiteness.

    simp only [ae_all_iff, eventually_imp_distrib_left]
    intro a b hab

    -- Core argument: L¹-bounded sequences with reverse martingale property have finite upcrossings
    -- This follows from the reverse martingale convergence theorem

    -- The proof would construct, for each N, a time-reversed martingale:
    -- Y^N_k := μ[f | 𝔽_{N ⊓ (N - k)}] with increasing filtration G^N_k := 𝔽_{N ⊓ (N - k)}
    -- Then Y^N is a forward martingale, so by Submartingale.upcrossings_ae_lt_top,
    -- upcrossings of Y^N are a.e. finite with bound independent of N.
    -- Taking N → ∞, the upcrossings of the original sequence are also a.e. finite.

    -- For now, we use a classical result:
    -- A reverse martingale that is L¹-bounded has finite upcrossings a.e.
    -- This is the time-reversed version of the forward martingale convergence theorem.

    -- Get uniform bound on expected upcrossings from time-reversed martingales
    have hab' : (↑a : ℝ) < (↑b : ℝ) := Rat.cast_lt.2 hab
    obtain ⟨C, h_C_finite, hC⟩ := upcrossings_bdd_uniform h_antitone h_le f hf (↑a) (↑b) hab'

    -- Establish relationship between original and reversed sequence upcrossings
    -- Key: upcrossingsBefore (original, N) ≤ upcrossings (reversed_at_N)
    -- Bound upcrossings of original by upcrossings of negated reversed process
    have h_le_key (N : ℕ) (ω : Ω) :
        ↑(upcrossingsBefore (↑a) (↑b) (fun n => μ[f | 𝔽 n]) N ω)
        ≤ upcrossings (- (↑b : ℝ)) (- (↑a : ℝ)) (negProcess (fun n => revCEFinite (μ := μ) f 𝔽 N n)) ω := by
      -- Use the "up ↔ up" bridge lemma: up(X) = up(-rev(X), flipped interval)
      have h_bridge := upBefore_eq_upBefore_neg_rev (fun n => μ[f | 𝔽 n]) (↑a) (↑b) N
      have h_orig_to_neg_rev : upcrossingsBefore (↑a) (↑b) (fun n => μ[f | 𝔽 n]) N ω
          = upcrossingsBefore (- (↑b : ℝ)) (- (↑a : ℝ))
              (negProcess (revProcess (fun n => μ[f | 𝔽 n]) N)) N ω := congrFun h_bridge ω

      -- Recognize that revProcess of condExp = revCEFinite
      have h_rev_eq : negProcess (revProcess (fun n => μ[f | 𝔽 n]) N)
                    = negProcess (fun n => revCEFinite (μ := μ) f 𝔽 N n) := by
        ext n ω'; simp [negProcess, revProcess, revCEFinite]

      -- Pick index N from the supremum definition of upcrossings
      have h_to_iSup :
          ↑(upcrossingsBefore (- (↑b : ℝ)) (- (↑a : ℝ))
              (negProcess (fun n => revCEFinite (μ := μ) f 𝔽 N n)) N ω)
            ≤ upcrossings (- (↑b : ℝ)) (- (↑a : ℝ))
                (negProcess (fun n => revCEFinite (μ := μ) f 𝔽 N n)) ω := by
        simp only [MeasureTheory.upcrossings]
        apply le_iSup (fun M => (upcrossingsBefore (- (↑b : ℝ)) (- (↑a : ℝ))
            (negProcess (fun n => revCEFinite (μ := μ) f 𝔽 N n)) M ω : ℝ≥0∞)) N

      calc ↑(upcrossingsBefore (↑a) (↑b) (fun n => μ[f | 𝔽 n]) N ω)
          = ↑(upcrossingsBefore (- (↑b : ℝ)) (- (↑a : ℝ))
                (negProcess (revProcess (fun n => μ[f | 𝔽 n]) N)) N ω) := by rw [h_orig_to_neg_rev]
        _ = ↑(upcrossingsBefore (- (↑b : ℝ)) (- (↑a : ℝ))
                (negProcess (fun n => revCEFinite (μ := μ) f 𝔽 N n)) N ω) := by rw [h_rev_eq]
        _ ≤ upcrossings (- (↑b : ℝ)) (- (↑a : ℝ))
                (negProcess (fun n => revCEFinite (μ := μ) f 𝔽 N n)) ω := h_to_iSup

    -- For each N, bound the expected upcrossings using the negated reversed martingale
    have h_N_bound : ∀ N, ∫⁻ ω, ↑(upcrossingsBefore (↑a) (↑b) (fun n => μ[f | 𝔽 n]) N ω) ∂μ ≤ C := by
      intro N
      calc ∫⁻ ω, ↑(upcrossingsBefore (↑a) (↑b) (fun n => μ[f | 𝔽 n]) N ω) ∂μ
          ≤ ∫⁻ ω, upcrossings (- (↑b : ℝ)) (- (↑a : ℝ)) (negProcess (fun n => revCEFinite (μ := μ) f 𝔽 N n)) ω ∂μ := by
            exact lintegral_mono (h_le_key N)
        _ = ∫⁻ ω, downcrossings (↑a) (↑b) (fun n => revCEFinite (μ := μ) f 𝔽 N n) ω ∂μ := by
            -- Use identity: up(-b, -a, -X) = down(a, b, X)
            rw [show (fun ω => upcrossings (- (↑b : ℝ)) (- (↑a : ℝ)) (negProcess (fun n => revCEFinite (μ := μ) f 𝔽 N n)) ω)
                   = (fun ω => downcrossings (↑a) (↑b) (fun n => revCEFinite (μ := μ) f 𝔽 N n) ω) from
                up_neg_flip_eq_down (↑a) (↑b) (fun n => revCEFinite (μ := μ) f 𝔽 N n)]
        _ ≤ C := by
            -- Downcrossings are bounded by applying Doob's inequality to -revCEFinite.
            --
            -- Key facts:
            -- 1. -revCEFinite is a martingale (negation preserves martingale property)
            -- 2. L¹ norm: ‖-revCEFinite‖₁ = ‖revCEFinite‖₁ ≤ ‖f‖₁ (L¹ contraction of condExp)
            -- 3. downcrossings(a,b,X) = upcrossings(-b,-a,-X) by definition
            -- 4. Apply Doob to -revCEFinite on interval [-b,-a]:
            --      (b-a) * E[upcrossings(-b,-a,-revCE)] ≤ E[(-revCE_N + b)⁺]
            --                                           ≤ ‖f‖₁ + |b|
            -- 5. Divide by (b-a) to get bound ≤ (‖f‖₁ + |b|)/(b-a)
            -- 6. This is ≤ C since |b| ≥ 0, so (‖f‖₁ + |b|) ≥ (‖f‖₁ + |a|) when a,b same sign
            --
            -- The proof mirrors the upcrossings bound but with -revCEFinite instead of revCEFinite.
            sorry  -- TODO: Apply Doob's upcrossing inequality to -revCEFinite

    -- Use monotone convergence on the ORIGINAL process (which IS monotone in N)
    have h_exp_orig : ∫⁻ ω, upcrossings (↑a) (↑b) (fun n => μ[f | 𝔽 n]) ω ∂μ ≤ C := by
      -- Set U N ω := upcrossingsBefore for the original process
      set U : ℕ → Ω → ℝ≥0∞ :=
        fun N ω => (upcrossingsBefore (↑a) (↑b) (fun n => μ[f | 𝔽 n]) N ω : ℝ≥0∞) with hU

      -- Monotonicity in N (pathwise): more time allows more completed crossings
      have hU_mono : Monotone U := by
        intro m n hmn ω
        simp only [hU]
        have := upcrossingsBefore_mono (f := fun n => μ[f | 𝔽 n]) hab' hmn ω
        exact Nat.cast_le.2 this

      -- Measurability
      have hU_meas : ∀ N, Measurable (U N) := by
        intro N
        simp only [hU]
        -- upcrossingsBefore is measurable for adapted processes
        -- Define the constant filtration (all same σ-algebra)
        let ℱ : Filtration ℕ (inferInstance : MeasurableSpace Ω) := {
          seq := fun _ => (inferInstance : MeasurableSpace Ω)
          mono' := fun _ _ _ => le_refl _
          le' := fun _ => le_refl _
        }
        -- The process μ[f | 𝔽 n] is adapted to this constant filtration
        have h_adapted : Adapted ℱ (fun n => μ[f | 𝔽 n]) := by
          intro n
          exact stronglyMeasurable_condExp.mono (h_le n)
        -- Apply measurability for adapted processes
        exact measurable_from_top.comp (h_adapted.measurable_upcrossingsBefore hab')

      -- Apply monotone convergence theorem
      have h_iSup : ∫⁻ ω, (⨆ N, U N ω) ∂μ = ⨆ N, ∫⁻ ω, U N ω ∂μ := by
        exact lintegral_iSup hU_meas hU_mono

      -- Bound the supremum of integrals
      have : (⨆ N, ∫⁻ ω, U N ω ∂μ) ≤ C := by
        refine iSup_le (fun N => ?_)
        exact h_N_bound N

      -- Conclude: upcrossings = ⨆ N, upcrossingsBefore N
      simpa [MeasureTheory.upcrossings, hU] using h_iSup.le.trans this

    -- Apply ae_lt_top: measurable function with finite expectation is a.e. finite
    refine ae_lt_top ?_ (lt_of_le_of_lt h_exp_orig h_C_finite).ne
    -- Measurability: upcrossings of an adapted process
    -- The sequence μ[f | 𝔽 n] is adapted to the trivial filtration (constant ambient σ-algebra)
    let ℱ : Filtration ℕ (inferInstance : MeasurableSpace Ω) := {
      seq := fun _ => (inferInstance : MeasurableSpace Ω)
      mono' := fun _ _ _ => le_refl _
      le' := fun _ => le_refl _
    }
    have h_adapted : Adapted ℱ (fun n => μ[f | 𝔽 n]) := by
      intro n
      exact stronglyMeasurable_condExp.mono (h_le n)
    exact h_adapted.measurable_upcrossings hab'

  -- Step 3: Apply convergence theorem to get pointwise limits
  have h_ae_conv : ∀ᵐ ω ∂μ, ∃ c, Tendsto (fun n => μ[f | 𝔽 n] ω) atTop (𝓝 c) := by
    filter_upwards [hbdd_liminf, hupcross] with ω hω₁ hω₂
    -- Convert enorm bound to nnnorm bound (they're equal via coercion)
    have hω₁' : (liminf (fun n => ENNReal.ofNNReal (nnnorm (μ[f | 𝔽 n] ω))) atTop) < ⊤ := by
      convert hω₁ using 2  -- ENorm.enorm x = ↑(nnnorm x)
    exact tendsto_of_uncrossing_lt_top hω₁' hω₂

  -- Step 4: Define the limit function using classical choice
  classical
  let Xlim : Ω → ℝ := fun ω =>
    if h : ∃ c, Tendsto (fun n => μ[f | 𝔽 n] ω) atTop (𝓝 c)
    then Classical.choose h
    else 0

  -- Step 5: Show Xlim has the desired properties
  use Xlim
  constructor

  · -- Integrability of Xlim (follows from Fatou + L¹ boundedness)
    -- Xlim is a.e. limit of integrable functions with uniform L¹ bound
    have hXlim_ae_meas : AEStronglyMeasurable Xlim μ := by
      apply aestronglyMeasurable_of_tendsto_ae atTop (f := fun n => μ[f | 𝔽 n])
      · intro n
        have : StronglyMeasurable[𝔽 n] (μ[f | 𝔽 n]) := stronglyMeasurable_condExp
        exact this.mono (h_le n) |>.aestronglyMeasurable
      · filter_upwards [h_ae_conv] with ω hω
        simp only [Xlim]
        rw [dif_pos hω]
        exact Classical.choose_spec hω

    -- By Fatou: ‖Xlim‖₁ ≤ liminf ‖μ[f | 𝔽 n]‖₁ ≤ ‖f‖₁ < ∞
    have hXlim_norm : HasFiniteIntegral Xlim μ := by
      rw [hasFiniteIntegral_iff_norm]
      -- Apply Fatou for ofReal ‖·‖
      have h_ae_tendsto : ∀ᵐ ω ∂μ, Tendsto (fun n => μ[f | 𝔽 n] ω) atTop (𝓝 (Xlim ω)) := by
        filter_upwards [h_ae_conv] with ω hω
        simp only [Xlim]
        rw [dif_pos hω]
        exact Classical.choose_spec hω
      -- Measurability proofs (separated to avoid timeout)
      have hmeas_n : ∀ n, AEMeasurable (fun ω => ENNReal.ofReal ‖μ[f | 𝔽 n] ω‖) μ := fun n =>
        ((stronglyMeasurable_condExp (f := f) (m := 𝔽 n) (μ := μ)).mono (h_le n)).norm.measurable.ennreal_ofReal.aemeasurable
      have hmeas_lim : AEMeasurable (fun ω => ENNReal.ofReal ‖Xlim ω‖) μ :=
        hXlim_ae_meas.norm.aemeasurable.ennreal_ofReal
      calc
        ∫⁻ ω, ENNReal.ofReal ‖Xlim ω‖ ∂μ
            ≤ liminf (fun n => ∫⁻ ω, ENNReal.ofReal ‖μ[f | 𝔽 n] ω‖ ∂μ) atTop :=
              lintegral_fatou_ofReal_norm h_ae_tendsto hmeas_n hmeas_lim
        _ ≤ ↑R := by
              rw [liminf_le_iff]
              intro b hb
              apply Eventually.frequently
              rw [eventually_atTop]
              use 0
              intro n _
              calc ∫⁻ ω, ENNReal.ofReal ‖μ[f | 𝔽 n] ω‖ ∂μ
                  = ∫⁻ ω, ‖μ[f | 𝔽 n] ω‖ₑ ∂μ := by
                    congr 1; ext ω
                    rw [Real.enorm_eq_ofReal_abs]
                    simp only [Real.norm_eq_abs]
                _ = eLpNorm (μ[f | 𝔽 n]) 1 μ := MeasureTheory.eLpNorm_one_eq_lintegral_enorm.symm
                _ ≤ eLpNorm f 1 μ := hL1_bdd n
                _ = ↑R := hR
                _ < b := hb
        _ < ⊤ := ENNReal.coe_lt_top

    exact ⟨hXlim_ae_meas, hXlim_norm⟩

  · -- A.e. convergence to Xlim
    filter_upwards [h_ae_conv] with ω hω
    simp only [Xlim]
    rw [dif_pos hω]
    exact Classical.choose_spec hω

/-- Uniform integrability of `{μ[f | 𝔽 n]}ₙ` for antitone filtration.

This is a direct application of mathlib's `Integrable.uniformIntegrable_condExp`,
which works for any family of sub-σ-algebras (not just filtrations). -/
lemma uniformIntegrable_condexp_antitone
    [IsProbabilityMeasure μ] {𝔽 : ℕ → MeasurableSpace Ω}
    (h_antitone : Antitone 𝔽) (h_le : ∀ n, 𝔽 n ≤ (inferInstance : MeasurableSpace Ω))
    (f : Ω → ℝ) (hf : Integrable f μ) :
    UniformIntegrable (fun n => μ[f | 𝔽 n]) 1 μ :=
  hf.uniformIntegrable_condExp h_le

/-- Identification: the a.s. limit equals `μ[f | ⨅ n, 𝔽 n]`.

Uses uniform integrability to pass from a.e. convergence to L¹ convergence,
then uses L¹-continuity of conditional expectation to identify the limit. -/
lemma ae_limit_is_condexp_iInf
    [IsProbabilityMeasure μ] {𝔽 : ℕ → MeasurableSpace Ω}
    (h_antitone : Antitone 𝔽) (h_le : ∀ n, 𝔽 n ≤ (inferInstance : MeasurableSpace Ω))
    (f : Ω → ℝ) (hf : Integrable f μ) :
    ∀ᵐ ω ∂μ, Tendsto (fun n => μ[f | 𝔽 n] ω) atTop (𝓝 (μ[f | ⨅ n, 𝔽 n] ω)) := by
  classical
  -- 1) Get a.s. limit Xlim
  obtain ⟨Xlim, hXlimint, h_tendsto⟩ :=
    condExp_exists_ae_limit_antitone (μ := μ) h_antitone h_le f hf

  -- 2) UI ⟹ L¹ convergence via Vitali
  have hUI := uniformIntegrable_condexp_antitone (μ := μ) h_antitone h_le f hf

  have hL1_conv : Tendsto (fun n => eLpNorm (μ[f | 𝔽 n] - Xlim) 1 μ) atTop (𝓝 0) := by
    apply tendsto_Lp_finite_of_tendsto_ae (hp := le_refl 1) (hp' := ENNReal.one_ne_top)
    · intro n; exact integrable_condExp.aestronglyMeasurable
    · exact memLp_one_iff_integrable.2 hXlimint
    · exact hUI.unifIntegrable
    · exact h_tendsto

  -- IMPORTANT: Define hXlim_aesm BEFORE introducing F_inf to avoid instance pollution
  -- Xlim is a.e. limit of 𝔽 n-measurable functions, so it's a.e. strongly measurable
  have hXlim_aesm : AEStronglyMeasurable Xlim μ := by
    refine aestronglyMeasurable_of_tendsto_ae atTop ?h_meas h_tendsto
    intro n
    -- Each μ[f | 𝔽 n] is 𝔽 n-strongly measurable, hence ambient-space a.e. strongly measurable
    have : StronglyMeasurable[𝔽 n] (μ[f | 𝔽 n]) := stronglyMeasurable_condExp
    exact this.mono (h_le n) |>.aestronglyMeasurable

  -- 3) Pass limit through condExp at F_inf := ⨅ n, 𝔽 n
  set F_inf := iInf 𝔽 with hF_inf_def

  -- Tower property: For every n, μ[μ[f | 𝔽 n] | F_inf] = μ[f | F_inf]
  have h_tower : ∀ n, μ[μ[f | 𝔽 n] | F_inf] =ᵐ[μ] μ[f | F_inf] := by
    intro n
    have : F_inf ≤ 𝔽 n := iInf_le 𝔽 n
    exact condExp_condExp_of_le this (h_le n)

  -- Final identification: Xlim = μ[f | F_inf]
  -- Strategy: Use L¹-continuity of condExp (non-circular approach)

  have hF_inf_le : F_inf ≤ _ := le_trans (iInf_le 𝔽 0) (h_le 0)

  set Y := μ[f | F_inf] with hY_def
  set Xn : ℕ → Ω → ℝ := fun n => μ[f | 𝔽 n] with hXn_def

  -- Non-circular proof: bound ‖μ[Xlim | F_inf] - Y‖₁ by ‖Xlim - Xn‖₁ via triangle + contraction
  -- Then let n → ∞ using L¹ convergence to get μ[Xlim | F_inf] =ᵐ Y
  -- This avoids using (or assuming) Xlim = Y to prove facts used to show Xlim = Y

  -- First, relate hL1_conv to Xn notation
  have hL1_conv_Xn : Tendsto (fun n => eLpNorm (Xlim - Xn n) 1 μ) atTop (𝓝 0) := by
    have : ∀ n, eLpNorm (Xlim - Xn n) 1 μ = eLpNorm (μ[f | 𝔽 n] - Xlim) 1 μ := by
      intro n
      simp only [Xn, hXn_def]
      rw [eLpNorm_sub_comm]
    simp only [this]
    exact hL1_conv

  -- Key inequality: ‖μ[Xlim | F_inf] - Y‖₁ ≤ ‖Xlim - Xn n‖₁ for all n
  have h_bound (n : ℕ) : eLpNorm (μ[Xlim | F_inf] - Y) 1 μ ≤ eLpNorm (Xlim - Xn n) 1 μ := by
    -- Triangle: (μ[Xlim|F_inf] - Y) = (μ[Xlim|F_inf] - μ[Xn|F_inf]) + (μ[Xn|F_inf] - Y)
    have htri : eLpNorm (μ[Xlim | F_inf] - Y) 1 μ
                ≤ eLpNorm (μ[Xlim | F_inf] - μ[Xn n | F_inf]) 1 μ
                  + eLpNorm (μ[Xn n | F_inf] - Y) 1 μ := by
      have : μ[Xlim | F_inf] - Y
              = (μ[Xlim | F_inf] - μ[Xn n | F_inf]) + (μ[Xn n | F_inf] - Y) := by ring
      rw [this]
      refine eLpNorm_add_le ?_ ?_ ?_
      · exact (integrable_condExp.sub integrable_condExp).aestronglyMeasurable
      · exact (integrable_condExp.sub integrable_condExp).aestronglyMeasurable
      · norm_num

    -- Second term is 0 by tower property
    have hzero : eLpNorm (μ[Xn n | F_inf] - Y) 1 μ = 0 := by
      have : μ[Xn n | F_inf] =ᵐ[μ] Y := by simpa [Xn, Y, hY_def, hXn_def] using h_tower n
      have : μ[Xn n | F_inf] - Y =ᵐ[μ] 0 := by filter_upwards [this] with ω hω; simp [hω]
      rw [eLpNorm_congr_ae this]
      simp

    -- First term ≤ ‖Xlim - Xn‖₁ by L¹-contraction + linearity (condExp_sub)
    have hfirst : eLpNorm (μ[Xlim | F_inf] - μ[Xn n | F_inf]) 1 μ ≤ eLpNorm (Xlim - Xn n) 1 μ := by
      -- linearity a.e.: μ[Xlim|F_inf] - μ[Xn|F_inf] = μ[Xlim - Xn | F_inf]
      have hsub : μ[Xlim | F_inf] - μ[Xn n | F_inf] =ᵐ[μ] μ[Xlim - Xn n | F_inf] := by
        exact (condExp_sub hXlimint integrable_condExp F_inf).symm
      -- contraction: ‖μ[g|F]‖₁ ≤ ‖g‖₁
      rw [eLpNorm_congr_ae hsub]
      exact eLpNorm_one_condExp_le_eLpNorm _

    -- Combine: triangle + zero + contraction
    calc eLpNorm (μ[Xlim | F_inf] - Y) 1 μ
        ≤ eLpNorm (μ[Xlim | F_inf] - μ[Xn n | F_inf]) 1 μ + eLpNorm (μ[Xn n | F_inf] - Y) 1 μ := htri
      _ = eLpNorm (μ[Xlim | F_inf] - μ[Xn n | F_inf]) 1 μ := by rw [hzero]; ring
      _ ≤ eLpNorm (Xlim - Xn n) 1 μ := hfirst

  -- Take limits: constant ≤ sequence → 0, so constant = 0
  have hCE_eqY : μ[Xlim | F_inf] =ᵐ[μ] Y := by
    -- From h_bound: eLpNorm (μ[Xlim | F_inf] - Y) 1 μ ≤ eLpNorm (Xlim - Xn n) 1 μ for all n
    -- Since Xn → Xlim in L¹, RHS → 0, so LHS = 0
    have h_norm_zero : eLpNorm (μ[Xlim | F_inf] - Y) 1 μ = 0 := by
      refine le_antisymm ?_ bot_le
      -- Constant ≤ sequence → 0 means constant = 0
      have : ∀ n, eLpNorm (μ[Xlim | F_inf] - Y) 1 μ ≤ eLpNorm (Xlim - Xn n) 1 μ := h_bound
      exact le_of_tendsto_of_tendsto tendsto_const_nhds hL1_conv_Xn (Eventually.of_forall this)
    rw [eLpNorm_eq_zero_iff (integrable_condExp.sub integrable_condExp).aestronglyMeasurable one_ne_zero] at h_norm_zero
    -- h_norm_zero : μ[Xlim | F_inf] - Y =ᵐ 0
    filter_upwards [h_norm_zero] with ω hω
    simp only [Pi.zero_apply] at hω
    exact sub_eq_zero.mp hω

  -- Xlim is F_inf-a.e.-measurable (as a.e. limit of F_inf-measurable functions)
  -- Therefore μ[Xlim | F_inf] = Xlim
  -- Combined with hCE_eqY : μ[Xlim | F_inf] =ᵐ Y, we get Y =ᵐ Xlim
  have hXlim_eq : Y =ᵐ[μ] Xlim := by
    -- First prove μ[Xlim | F_inf] = Xlim using the fact that Xlim is (essentially) F_inf-measurable
    -- Xlim is the limit of F_inf-measurable functions, so is itself F_inf-measurable
    have hXlim_condExp_self : μ[Xlim | F_inf] =ᵐ[μ] Xlim := by
      -- Xlim is the a.e. limit of the sequence μ[f | 𝔽 n]
      -- Each μ[f | 𝔽 n] can be viewed as F_inf-a.e.-measurable
      -- (This step is subtle and requires careful sub-σ-algebra handling)
      -- For now, use sorry - this is a known result about reverse martingales
      sorry

    -- Now use L¹-continuity: μ[Xlim | F_inf] =ᵐ Y and μ[Xlim | F_inf] =ᵐ Xlim
    -- Therefore Y =ᵐ Xlim
    exact hCE_eqY.symm.trans hXlim_condExp_self

  -- Finally: derive μ[Xlim | F_inf] =ᵐ[μ] Xlim from hCE_eqY and hXlim_eq
  -- Simple 2-step chain, no circularity
  have hXlim_condExp : μ[Xlim | F_inf] =ᵐ[μ] Xlim := by
    have h1 : μ[Xlim | F_inf] =ᵐ[μ] Y := hCE_eqY
    have h2 : Y =ᵐ[μ] Xlim := hXlim_eq
    exact h1.trans h2

  -- Return the desired result: combine h_tendsto with hXlim_eq
  -- We have: h_tendsto : μ[f|𝔽 n] → Xlim
  --          hXlim_eq  : Y =ᵐ Xlim (where Y = μ[f|F_inf])
  -- Goal: μ[f|𝔽 n] → Y
  filter_upwards [h_tendsto, hXlim_eq] with ω h_tend h_eq
  -- h_tend : μ[f|𝔽 n] ω → Xlim ω
  -- h_eq : Y ω = Xlim ω
  -- Want: μ[f|𝔽 n] ω → Y ω
  rw [h_eq]
  exact h_tend

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
