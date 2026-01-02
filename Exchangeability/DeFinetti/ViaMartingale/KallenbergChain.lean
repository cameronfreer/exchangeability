/-
Copyright (c) 2025 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Exchangeability.Contractability
import Exchangeability.Core
import Exchangeability.DeFinetti.ViaMartingale.RevFiltration
import Exchangeability.DeFinetti.ViaMartingale.ShiftOperations
import Exchangeability.Probability.TripleLawDropInfo.DropInfo
import Exchangeability.Probability.Martingale.Convergence

/-!
# Kallenberg Chain Lemma for Reverse Filtration

This file implements the core "Kallenberg chain" step from page 28 of Kallenberg (2005).

## Main Results

* `pair_law_shift_eq_of_contractable` - For contractable X with k < m ≤ n:
  `(X k, shiftRV X m) =^d (X k, shiftRV X n)`

* `condExp_indicator_revFiltration_eq_of_le` - The main Kallenberg chain lemma:
  For contractable X with k < m ≤ n and measurable B:
  `μ[(B.indicator 1) ∘ X k | revFiltration X m] =ᵐ[μ] μ[(B.indicator 1) ∘ X k | revFiltration X n]`

## Mathematical Background

**Kallenberg's argument (page 28):**

For a contractable sequence ξ with k < m ≤ n:
```
P[ξ_k ∈ B | θ_m ξ] = P[ξ_k ∈ B | θ_n ξ]   (a.s.)
```

where θ_m ξ = (ξ_m, ξ_{m+1}, ...) is the m-shifted sequence.

**Proof ingredients:**
1. Contractability → pair law: `(ξ_k, θ_m ξ) =^d (ξ_k, θ_n ξ)` (same strictly increasing subsequence)
2. `σ(θ_n ξ) ⊆ σ(θ_m ξ)` when m ≤ n (`revFiltration_antitone`)
3. Kallenberg Lemma 1.3 (`condExp_indicator_eq_of_law_eq_of_comap_le`)

## Notation

In Kallenberg's notation:
- `shiftRV X m` = θ_m ξ (the m-shifted sequence)
- `revFiltration X m` = σ(θ_m ξ) (the reverse filtration)
- `tailSigma X` = T_ξ (the tail σ-algebra)

## References

* Kallenberg (2005), *Probabilistic Symmetries and Invariance Principles*, page 28
-/

open MeasureTheory MeasurableSpace Filter
open scoped ENNReal Topology

namespace Exchangeability.DeFinetti.ViaMartingale

variable {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]

/-! ### Pair Law for Shifted Sequences

For contractable X with k < m ≤ n, the pairs (X k, shiftRV X m) and (X k, shiftRV X n)
have the same distribution. This follows from contractability by viewing each pair
as a strictly increasing subsequence of X.
-/

/-- Embedding of `α × (ℕ → α)` into `ℕ → α` by placing the first element at position 0
and the sequence at positions 1, 2, 3, ... -/
def embedPairSeq : α × (ℕ → α) → ℕ → α
  | (a, _), 0 => a
  | (_, f), n + 1 => f n

/-- Projection from `ℕ → α` to `α × (ℕ → α)` by extracting position 0 and the tail. -/
def projectPairSeq : (ℕ → α) → α × (ℕ → α) :=
  fun f => (f 0, fun n => f (n + 1))

omit [MeasurableSpace Ω] [MeasurableSpace α] in
lemma projectPairSeq_embedPairSeq (p : α × (ℕ → α)) : projectPairSeq (embedPairSeq p) = p := by
  rcases p with ⟨a, f⟩
  simp only [projectPairSeq, embedPairSeq]

lemma embedPairSeq_measurable : Measurable (embedPairSeq : α × (ℕ → α) → ℕ → α) := by
  rw [measurable_pi_iff]
  intro n
  cases n with
  | zero => exact measurable_fst
  | succ k => exact (measurable_pi_apply k).comp measurable_snd

lemma projectPairSeq_measurable : Measurable (projectPairSeq : (ℕ → α) → α × (ℕ → α)) :=
  Measurable.prod (measurable_pi_apply 0)
    (measurable_pi_iff.mpr fun n => measurable_pi_apply (n + 1))

/-- The injection `k, m, m+1, m+2, ...` for pair law argument.
This is strictly increasing when k < m. -/
def pairInjection (k m : ℕ) : ℕ → ℕ
  | 0 => k
  | n + 1 => m + n

omit [MeasurableSpace Ω] [MeasurableSpace α] in
lemma pairInjection_strictMono (k m : ℕ) (hk : k < m) : StrictMono (pairInjection k m) := by
  intro i j hij
  cases i with
  | zero =>
    cases j with
    | zero => exact (Nat.lt_irrefl 0 hij).elim
    | succ j' =>
      simp only [pairInjection]
      omega
  | succ i' =>
    cases j with
    | zero => exact (Nat.not_lt_zero _ hij).elim
    | succ j' =>
      simp only [pairInjection]
      have : i' < j' := Nat.lt_of_succ_lt_succ hij
      omega

omit [MeasurableSpace Ω] [MeasurableSpace α] in
/-- The pair (X k, shiftRV X m) factors through embedPairSeq and reindexing. -/
lemma pair_eq_embedPairSeq_comp (X : ℕ → Ω → α) (k m : ℕ) :
    (fun ω => embedPairSeq (X k ω, shiftRV X m ω)) =
    (fun ω n => X (pairInjection k m n) ω) := by
  ext ω n
  cases n with
  | zero => rfl
  | succ n' => simp only [embedPairSeq, shiftRV, pairInjection]

/-- **Pair law for shifted sequences from contractability.**

For contractable X with k < m ≤ n, the pairs `(X k, shiftRV X m)` and `(X k, shiftRV X n)`
have the same distribution.

**Proof:** Both pairs correspond to strictly increasing subsequences of X:
- `(X k, shiftRV X m)` corresponds to indices `k, m, m+1, m+2, ...`
- `(X k, shiftRV X n)` corresponds to indices `k, n, n+1, n+2, ...`

By contractability, these have equal finite marginals, hence equal measures. -/
lemma pair_law_shift_eq_of_contractable
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → α} (hContr : Contractable μ X) (hX : ∀ n, Measurable (X n))
    {k m n : ℕ} (hkm : k < m) (hmn : m ≤ n) :
    Measure.map (fun ω => (X k ω, shiftRV X m ω)) μ =
    Measure.map (fun ω => (X k ω, shiftRV X n ω)) μ := by
  have hkn : k < n := Nat.lt_of_lt_of_le hkm hmn

  -- Reindexed sequences
  let seqM : Ω → ℕ → α := fun ω i => X (pairInjection k m i) ω
  let seqN : Ω → ℕ → α := fun ω i => X (pairInjection k n i) ω

  have hSeqM_meas : Measurable seqM := measurable_pi_iff.mpr fun _ => hX _
  have hSeqN_meas : Measurable seqN := measurable_pi_iff.mpr fun _ => hX _

  -- Both reindexed sequences have the same distribution by contractability
  -- (π-system uniqueness on finite marginals)
  have h_seq_eq : Measure.map seqM μ = Measure.map seqN μ := by
    haveI : IsProbabilityMeasure (Measure.map seqM μ) :=
      Measure.isProbabilityMeasure_map hSeqM_meas.aemeasurable
    haveI : IsProbabilityMeasure (Measure.map seqN μ) :=
      Measure.isProbabilityMeasure_map hSeqN_meas.aemeasurable
    apply Exchangeability.measure_eq_of_fin_marginals_eq_prob
    intro r S _hS
    -- Need to show: map (prefixProj r) (map seqM μ) S = map (prefixProj r) (map seqN μ) S
    rw [Measure.map_map (measurable_prefixProj (α := α)) hSeqM_meas,
        Measure.map_map (measurable_prefixProj (α := α)) hSeqN_meas]
    -- prefixProj r ∘ seqM = fun ω i => X (pairInjection k m i) ω
    have hcompM : (prefixProj (α := α) r) ∘ seqM = fun ω (i : Fin r) => X (pairInjection k m i) ω := rfl
    have hcompN : (prefixProj (α := α) r) ∘ seqN = fun ω (i : Fin r) => X (pairInjection k n i) ω := rfl
    rw [hcompM, hcompN]
    -- Both finite marginals come from strictly increasing subsequences
    have h1 := hContr.allStrictMono_eq r
      (fun i : Fin r => pairInjection k m i.val)
      (fun i : Fin r => pairInjection k n i.val)
      (fun i j hij => pairInjection_strictMono k m hkm hij)
      (fun i j hij => pairInjection_strictMono k n hkn hij)
    exact congrArg (· S) h1

  -- Factor the pair maps through projectPairSeq
  -- Key: (X k ω, shiftRV X m ω) = projectPairSeq (seqM ω)
  have h_factorM : ∀ ω, (X k ω, shiftRV X m ω) = projectPairSeq (seqM ω) := fun ω => by
    simp only [projectPairSeq, seqM, pairInjection, Prod.mk.injEq]
    exact ⟨trivial, rfl⟩
  have h_factorN : ∀ ω, (X k ω, shiftRV X n ω) = projectPairSeq (seqN ω) := fun ω => by
    simp only [projectPairSeq, seqN, pairInjection, Prod.mk.injEq]
    exact ⟨trivial, rfl⟩

  have h_eqM : (fun ω => (X k ω, shiftRV X m ω)) = (projectPairSeq ∘ seqM) :=
    funext h_factorM
  have h_eqN : (fun ω => (X k ω, shiftRV X n ω)) = (projectPairSeq ∘ seqN) :=
    funext h_factorN

  -- Rewrite the LHS and RHS using the factorizations
  calc Measure.map (fun ω => (X k ω, shiftRV X m ω)) μ
      = Measure.map (projectPairSeq ∘ seqM) μ := by rw [h_eqM]
    _ = Measure.map projectPairSeq (Measure.map seqM μ) :=
          (Measure.map_map projectPairSeq_measurable hSeqM_meas).symm
    _ = Measure.map projectPairSeq (Measure.map seqN μ) := by rw [h_seq_eq]
    _ = Measure.map (projectPairSeq ∘ seqN) μ :=
          Measure.map_map projectPairSeq_measurable hSeqN_meas
    _ = Measure.map (fun ω => (X k ω, shiftRV X n ω)) μ := by rw [h_eqN]

/-! ### Main Kallenberg Chain Lemma

Using the pair law and the contraction structure σ(shiftRV X n) ⊆ σ(shiftRV X m),
we apply Kallenberg Lemma 1.3 to drop from revFiltration X m to revFiltration X n.
-/

/-- **Kallenberg Chain Lemma.**

For contractable X with k < m ≤ n and measurable B:
```
μ[(B.indicator 1) ∘ X k | revFiltration X m] =ᵐ[μ] μ[(B.indicator 1) ∘ X k | revFiltration X n]
```

This is Kallenberg's key observation (page 28): conditioning X_k on the finer
σ-algebra σ(θ_n ξ) gives the same result as conditioning on the coarser σ(θ_m ξ).

**Proof:**
1. `(X k, shiftRV X m) =^d (X k, shiftRV X n)` by `pair_law_shift_eq_of_contractable`
2. `revFiltration X n ≤ revFiltration X m` by `revFiltration_antitone`
3. Apply Kallenberg Lemma 1.3 (`condExp_indicator_eq_of_law_eq_of_comap_le`)
-/
lemma condExp_indicator_revFiltration_eq_of_le
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → α} (hContr : Contractable μ X) (hX : ∀ n, Measurable (X n))
    {k m n : ℕ} (hkm : k < m) (hmn : m ≤ n)
    {B : Set α} (hB : MeasurableSet B) :
    μ[Set.indicator (X k ⁻¹' B) (fun _ => (1 : ℝ)) | revFiltration X m]
      =ᵐ[μ]
    μ[Set.indicator (X k ⁻¹' B) (fun _ => (1 : ℝ)) | revFiltration X n] := by
  -- Step 1: Pair law from contractability (symmetric)
  have h_pair : Measure.map (fun ω => (X k ω, shiftRV X n ω)) μ =
                Measure.map (fun ω => (X k ω, shiftRV X m ω)) μ :=
    (pair_law_shift_eq_of_contractable hContr hX hkm hmn).symm

  -- Step 2: Contraction structure: σ(shiftRV X n) ⊆ σ(shiftRV X m)
  -- revFiltration_antitone says: m ≤ n → revFiltration X n ≤ revFiltration X m
  -- So comap (shiftRV X n) ≤ comap (shiftRV X m) when m ≤ n
  have h_le : MeasurableSpace.comap (shiftRV X n) inferInstance ≤
              MeasurableSpace.comap (shiftRV X m) inferInstance :=
    revFiltration_antitone X hmn

  -- Measurability
  have hXk : Measurable (X k) := hX k
  have hWm : Measurable (shiftRV X m) := measurable_shiftRV hX
  have hWn : Measurable (shiftRV X n) := measurable_shiftRV hX

  -- Step 3: Apply Kallenberg Lemma 1.3
  -- condExp_indicator_eq_of_law_eq_of_comap_le says:
  --   if (X, W) =^d (X, W') and comap W ≤ comap W'
  --   then μ[φ | comap W'] =ᵐ μ[φ | comap W]
  --
  -- In our case:
  -- - W = shiftRV X n, W' = shiftRV X m
  -- - comap (shiftRV X n) ≤ comap (shiftRV X m) from h_le
  -- - pair law: (X k, shiftRV X n) =^d (X k, shiftRV X m)
  --
  -- This gives μ[φ | comap (shiftRV X m)] =ᵐ μ[φ | comap (shiftRV X n)]
  -- which is μ[φ | revFiltration X m] =ᵐ μ[φ | revFiltration X n]
  exact condExp_indicator_eq_of_law_eq_of_comap_le
    (X k) (shiftRV X n) (shiftRV X m) hXk hWn hWm h_pair h_le hB

/-- **Trivial case: k = m.**

When k = m, X_k is measurable with respect to revFiltration X m, so the conditional
expectation equals the function itself. This handles the boundary case k ≤ m. -/
lemma condExp_indicator_revFiltration_eq_self_of_eq
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → α} (hX : ∀ n, Measurable (X n))
    (m : ℕ) {B : Set α} (hB : MeasurableSet B) :
    μ[Set.indicator (X m ⁻¹' B) (fun _ => (1 : ℝ)) | revFiltration X m]
      =ᵐ[μ]
    Set.indicator (X m ⁻¹' B) (fun _ => (1 : ℝ)) := by
  -- X m is measurable with respect to revFiltration X m
  -- because X m = (shiftRV X m) 0
  have hXm_meas : @Measurable Ω α (revFiltration X m) _ (X m) := by
    -- revFiltration X m = comap (shiftRV X m) (product σ-algebra on ℕ → α)
    -- X m = (shiftRV X m ω) 0
    have h_eq : X m = (fun ω => (shiftRV X m ω) 0) := by
      ext ω
      simp only [shiftRV, add_zero]
    rw [h_eq]
    have hIdent : @Measurable Ω (ℕ → α) (revFiltration X m) _ (shiftRV X m) :=
      measurable_iff_comap_le.mpr le_rfl
    exact (measurable_pi_apply 0).comp hIdent

  have hInd_meas : @Measurable Ω ℝ (revFiltration X m) _ (Set.indicator (X m ⁻¹' B) (fun _ => (1 : ℝ))) :=
    (measurable_const.indicator hB).comp hXm_meas

  -- Conditional expectation of a measurable function is itself
  have hm_le : revFiltration X m ≤ (inferInstance : MeasurableSpace Ω) := revFiltration_le X hX m
  haveI hσ : SigmaFinite (μ.trim hm_le) := by
    haveI : IsFiniteMeasure (μ.trim hm_le) := by
      constructor
      rw [trim_measurableSet_eq hm_le MeasurableSet.univ]
      exact measure_lt_top μ Set.univ
    infer_instance
  have heq := @condExp_of_stronglyMeasurable Ω ℝ (revFiltration X m) _ _ _ _ _ hm_le hσ
    _ hInd_meas.stronglyMeasurable (Integrable.indicator (integrable_const 1) ((hX m) hB))
  exact Filter.EventuallyEq.of_eq heq

/-! ### Convergence to Tail σ-algebra

Using the Kallenberg chain lemma and reverse martingale convergence, we show that
conditional expectations on revFiltration X m equal those on the tail σ-algebra.
-/

/-- **Conditional expectation on revFiltration equals tail.**

For contractable X with k < m, the conditional expectation of the indicator 1_{X_k ∈ B}
given revFiltration X m equals the conditional expectation given tailSigma X.

**Proof:**
1. By `condExp_indicator_revFiltration_eq_of_le`, the sequence `μ[φ | revFiltration X n]`
   is constant for n ≥ m.
2. By `condExp_tendsto_iInf`, this sequence converges a.e. to `μ[φ | tailSigma X]`.
3. A constant sequence converges to its value, so the value equals the limit.
-/
lemma condExp_indicator_revFiltration_eq_tail
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → α} (hContr : Contractable μ X) (hX : ∀ n, Measurable (X n))
    {k m : ℕ} (hkm : k < m)
    {B : Set α} (hB : MeasurableSet B) :
    μ[Set.indicator (X k ⁻¹' B) (fun _ => (1 : ℝ)) | revFiltration X m]
      =ᵐ[μ]
    μ[Set.indicator (X k ⁻¹' B) (fun _ => (1 : ℝ)) | tailSigma X] := by
  set φ : Ω → ℝ := Set.indicator (X k ⁻¹' B) (fun _ => (1 : ℝ)) with hφ_def
  set f := fun n => μ[φ | revFiltration X n]

  -- φ is integrable
  have hφ_int : Integrable φ μ := Integrable.indicator (integrable_const 1) ((hX k) hB)

  -- The filtration is antitone
  have h_anti : Antitone (fun n => revFiltration X n) := revFiltration_antitone X
  have h_le : ∀ n, revFiltration X n ≤ (inferInstance : MeasurableSpace Ω) := revFiltration_le X hX

  -- By reverse martingale convergence: f n → μ[φ | ⨅ n, revFiltration X n] a.e.
  have h_conv : ∀ᵐ ω ∂μ, Tendsto (fun n => f n ω) atTop (𝓝 (μ[φ | ⨅ n, revFiltration X n] ω)) :=
    Exchangeability.Probability.condExp_tendsto_iInf h_anti h_le φ hφ_int

  -- The infimum is tailSigma X
  have h_iInf_eq : (⨅ n, revFiltration X n) = tailSigma X := rfl

  -- Key: for n ≥ m, f n =ᵐ f m (the sequence is eventually constant)
  have h_const : ∀ n, m ≤ n → f n =ᵐ[μ] f m :=
    fun n hn => (condExp_indicator_revFiltration_eq_of_le hContr hX hkm hn hB).symm

  -- Combine all the a.e. equalities: on a set of full measure, f n ω = f m ω for all n ≥ m
  have h_ae_all_const : ∀ᵐ ω ∂μ, ∀ n, m ≤ n → f n ω = f m ω := by
    rw [ae_all_iff]
    intro n
    by_cases hn : m ≤ n
    · filter_upwards [h_const n hn] with ω hω
      intro _; exact hω
    · filter_upwards with ω
      intro hmn
      exact (hn hmn).elim

  -- Combine: on a set of full measure, the sequence is constant AND converges
  rw [h_iInf_eq] at h_conv
  filter_upwards [h_conv, h_ae_all_const] with ω h_tendsto h_all_const
  -- h_tendsto : Tendsto (fun n => f n ω) atTop (𝓝 (μ[φ | tailSigma X] ω))
  -- h_all_const : ∀ n, m ≤ n → f n ω = f m ω
  -- Goal: f m ω = μ[φ | tailSigma X] ω

  -- The sequence is eventually equal to f m ω
  have h_event_const : ∀ᶠ n in atTop, f n ω = f m ω :=
    eventually_atTop.mpr ⟨m, fun n hn => h_all_const n hn⟩

  -- A sequence converging to L that is eventually equal to c has L = c
  -- We need: f m ω = limit, i.e., f m ω = μ[φ | tailSigma X] ω
  -- From h_tendsto: f n ω → μ[φ | tailSigma X] ω
  -- From h_event_const: ∀ᶠ n, f n ω = f m ω
  -- So the constant sequence (f m ω) converges to μ[φ | tailSigma X] ω
  -- Therefore f m ω = μ[φ | tailSigma X] ω
  have h_const_tends : Tendsto (fun _ : ℕ => f m ω) atTop (𝓝 (μ[φ | tailSigma X] ω)) :=
    h_tendsto.congr' (h_event_const.mono fun _ h => h)
  exact tendsto_const_nhds_iff.mp h_const_tends

end Exchangeability.DeFinetti.ViaMartingale
