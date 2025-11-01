/-
Copyright (c) 2025 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.Probability.Martingale.Basic
import Mathlib.Probability.Martingale.Convergence
import Mathlib.Probability.Process.Filtration

/-!
# Martingale Convergence for De Finetti

This file develops reverse martingale convergence (Lévy's downward theorem) needed for the
martingale proof of de Finetti's theorem.

## Main Results

- `reverse_martingale_convergence_ae`: Reverse martingales converge a.e. to the conditional
  expectation with respect to the tail σ-algebra.

## Implementation Status

Mathlib (as of v4.24.0) provides:
- `Martingale`: Basic martingale definition
- `Submartingale`, `Supermartingale`: Sub/supermartingale definitions
- Various martingale properties

**Missing from mathlib:**
- Martingale convergence theorems
- Lévy's upward/downward theorems
- Doob's convergence theorem

These are fundamental results but not yet formalized in mathlib. We axiomatize them here
with detailed proof strategies for future implementation.

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

/-! ## Reverse Martingale Convergence (Lévy's Downward Theorem)

**Mathematical statement:**
Let (Xₙ) be a reverse martingale adapted to a decreasing filtration (𝔽ₙ), i.e.:
- 𝔽ₙ₊₁ ⊆ 𝔽ₙ for all n
- Xₙ is 𝔽ₙ-measurable
- E[Xₙ | 𝔽ₙ₊₁] = Xₙ₊₁ a.s.

Then Xₙ converges a.s. to X_∞ := E[X₀ | 𝔽_∞] where 𝔽_∞ = ⋂ₙ 𝔽ₙ.

**Proof strategy:**
1. **Upcrossing inequality**: Bound the number of upcrossings of any interval [a,b]
2. **Convergence**: Show that bounded number of upcrossings implies convergence
3. **Limit identification**: The limit equals the conditional expectation on tail σ-algebra

**Why needed for de Finetti:**
For contractable sequences X, the sequence
  Mₙ := E[1_{X₀∈B} | σ(θₙ₊₁ X)]
is a reverse martingale. Lévy's theorem gives:
  Mₙ → E[1_{X₀∈B} | ⋂ₙ σ(θₙ₊₁ X)] a.s.
This is the key to proving conditional i.i.d. -/

/-- **Reverse martingale limit witness.**

For a reverse martingale (Mₙ), provides the limit function M_∞. -/
axiom reverseMartingaleLimit
    {ι : Type*} [Preorder ι] [IsDirected ι (· ≥ ·)]
    [IsProbabilityMeasure μ]
    {𝔽 : ι → MeasurableSpace Ω}
    (h_filtration : Antitone 𝔽)
    (h_le : ∀ i, 𝔽 i ≤ (inferInstance : MeasurableSpace Ω))
    {M : ι → Ω → ℝ}
    (h_adapted : ∀ i, StronglyMeasurable[𝔽 i] (M i))
    (h_integrable : ∀ i, Integrable (M i) μ)
    (h_martingale : ∀ i j, i ≤ j → μ[M j | 𝔽 i] =ᵐ[μ] M i)
    (f₀ : Ω → ℝ) (h_f₀_int : Integrable f₀ μ) :
    Ω → ℝ

/-- The reverse martingale limit is tail-measurable. -/
axiom reverseMartingaleLimit_measurable
    {ι : Type*} [Preorder ι] [IsDirected ι (· ≥ ·)]
    [IsProbabilityMeasure μ]
    {𝔽 : ι → MeasurableSpace Ω}
    (h_filtration : Antitone 𝔽)
    (h_le : ∀ i, 𝔽 i ≤ (inferInstance : MeasurableSpace Ω))
    {M : ι → Ω → ℝ}
    (h_adapted : ∀ i, StronglyMeasurable[𝔽 i] (M i))
    (h_integrable : ∀ i, Integrable (M i) μ)
    (h_martingale : ∀ i j, i ≤ j → μ[M j | 𝔽 i] =ᵐ[μ] M i)
    (f₀ : Ω → ℝ) (h_f₀_int : Integrable f₀ μ) :
    StronglyMeasurable[⨅ i, 𝔽 i] (reverseMartingaleLimit h_filtration h_le h_adapted h_integrable h_martingale f₀ h_f₀_int)

/-- The reverse martingale limit equals the conditional expectation on tail σ-algebra. -/
axiom reverseMartingaleLimit_eq
    {ι : Type*} [Preorder ι] [IsDirected ι (· ≥ ·)]
    [IsProbabilityMeasure μ]
    {𝔽 : ι → MeasurableSpace Ω}
    (h_filtration : Antitone 𝔽)
    (h_le : ∀ i, 𝔽 i ≤ (inferInstance : MeasurableSpace Ω))
    {M : ι → Ω → ℝ}
    (h_adapted : ∀ i, StronglyMeasurable[𝔽 i] (M i))
    (h_integrable : ∀ i, Integrable (M i) μ)
    (h_martingale : ∀ i j, i ≤ j → μ[M j | 𝔽 i] =ᵐ[μ] M i)
    (f₀ : Ω → ℝ) (h_f₀_meas : Measurable f₀) (h_f₀_int : Integrable f₀ μ) :
    μ[f₀ | ⨅ i, 𝔽 i] =ᵐ[μ] (reverseMartingaleLimit h_filtration h_le h_adapted h_integrable h_martingale f₀ h_f₀_int)

/-- **Reverse martingale convergence (Lévy's downward theorem).**

For a reverse martingale (Mₙ) adapted to a decreasing filtration (𝔽ₙ),
the sequence converges a.e. to the conditional expectation with respect to
the tail σ-algebra 𝔽_∞ := ⋂ₙ 𝔽ₙ. -/
axiom reverseMartingale_convergence_ae
    {ι : Type*} [Preorder ι] [IsDirected ι (· ≥ ·)]
    [IsProbabilityMeasure μ]
    {𝔽 : ι → MeasurableSpace Ω}
    (h_filtration : Antitone 𝔽)
    (h_le : ∀ i, 𝔽 i ≤ (inferInstance : MeasurableSpace Ω))
    {M : ι → Ω → ℝ}
    (h_adapted : ∀ i, StronglyMeasurable[𝔽 i] (M i))
    (h_integrable : ∀ i, Integrable (M i) μ)
    (h_martingale : ∀ i j, i ≤ j → μ[M j | 𝔽 i] =ᵐ[μ] M i)
    (f₀ : Ω → ℝ) (h_f₀_int : Integrable f₀ μ) :
    ∀ᵐ ω ∂μ, Tendsto (fun i => M i ω) atTop (𝓝 ((reverseMartingaleLimit h_filtration h_le h_adapted h_integrable h_martingale f₀ h_f₀_int) ω))

/-- **Simplified version for ℕ-indexed reverse martingales - limit witness.** -/
axiom reverseMartingaleLimitNat
    [IsProbabilityMeasure μ]
    {𝔽 : ℕ → MeasurableSpace Ω}
    (h_filtration : Antitone 𝔽)
    (h_le : ∀ n, 𝔽 n ≤ (inferInstance : MeasurableSpace Ω))
    {M : ℕ → Ω → ℝ}
    (h_adapted : ∀ n, StronglyMeasurable[𝔽 n] (M n))
    (h_integrable : ∀ n, Integrable (M n) μ)
    (h_martingale : ∀ m n, m ≤ n → μ[M n | 𝔽 m] =ᵐ[μ] M m)
    (f₀ : Ω → ℝ) (h_f₀_int : Integrable f₀ μ) :
    Ω → ℝ

/-- The ℕ-indexed reverse martingale limit equals the conditional expectation. -/
axiom reverseMartingaleLimitNat_eq
    [IsProbabilityMeasure μ]
    {𝔽 : ℕ → MeasurableSpace Ω}
    (h_filtration : Antitone 𝔽)
    (h_le : ∀ n, 𝔽 n ≤ (inferInstance : MeasurableSpace Ω))
    {M : ℕ → Ω → ℝ}
    (h_adapted : ∀ n, StronglyMeasurable[𝔽 n] (M n))
    (h_integrable : ∀ n, Integrable (M n) μ)
    (h_martingale : ∀ m n, m ≤ n → μ[M n | 𝔽 m] =ᵐ[μ] M m)
    (f₀ : Ω → ℝ) (h_f₀_int : Integrable f₀ μ) :
    μ[f₀ | ⨅ n, 𝔽 n] =ᵐ[μ] (reverseMartingaleLimitNat h_filtration h_le h_adapted h_integrable h_martingale f₀ h_f₀_int)

/-- **ℕ-indexed reverse martingale convergence.** -/
axiom reverseMartingaleNat_convergence
    [IsProbabilityMeasure μ]
    {𝔽 : ℕ → MeasurableSpace Ω}
    (h_filtration : Antitone 𝔽)
    (h_le : ∀ n, 𝔽 n ≤ (inferInstance : MeasurableSpace Ω))
    {M : ℕ → Ω → ℝ}
    (h_adapted : ∀ n, StronglyMeasurable[𝔽 n] (M n))
    (h_integrable : ∀ n, Integrable (M n) μ)
    (h_martingale : ∀ m n, m ≤ n → μ[M n | 𝔽 m] =ᵐ[μ] M m)
    (f₀ : Ω → ℝ) (h_f₀_int : Integrable f₀ μ) :
    ∀ᵐ ω ∂μ, Tendsto (fun n => M n ω) atTop (𝓝 ((reverseMartingaleLimitNat h_filtration h_le h_adapted h_integrable h_martingale f₀ h_f₀_int) ω))

/-! ## OrderDual Infrastructure for Decreasing Filtrations

Package a decreasing family of σ-algebras on `ℕ` as an increasing filtration on `ℕᵒᵈ`.
This allows us to reuse the existing upward Lévy theorem for downward convergence. -/

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
    -- `i ≤ j` in `ℕᵒᵈ` means `j.ofDual ≤ i.ofDual` in `ℕ`
    -- Antitone: `hF : a ≤ b → F b ≤ F a`
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
  · -- `⨆ ≤ F 0` since `F n ≤ F 0` for all `n`
    refine iSup_le (fun i => ?_)
    have : (0 : ℕ) ≤ i.ofDual := Nat.zero_le _
    exact hF this
  · -- and `F 0 ≤ ⨆` since `0` is one of the indices
    have : F 0 ≤ F (OrderDual.ofDual (OrderDual.toDual 0)) := le_rfl
    simpa using (le_iSup_of_le (OrderDual.toDual 0) this)

/-! ## Application to De Finetti

The specific case needed for the martingale proof of de Finetti. -/

/-! ### Helper definitions for reverse martingale convergence -/

/-- Reverse martingale along a decreasing chain: `X n := condExp μ (F n) f`. -/
def revCE (μ : Measure Ω) (F : ℕ → MeasurableSpace Ω) (f : Ω → ℝ) (n : ℕ) : Ω → ℝ :=
  μ[f | F n]

/-- Tower property in the reverse direction: for `m ≥ n`, `E[X_n | F_m] = X_m`. -/
lemma revCE_tower
    [IsProbabilityMeasure μ]
    {F : ℕ → MeasurableSpace Ω} (hF : Antitone F)
    (h_le : ∀ n, F n ≤ (inferInstance : MeasurableSpace Ω))
    (f : Ω → ℝ) {n m : ℕ} (hmn : n ≤ m) :
    μ[revCE μ F f n | F m] =ᵐ[μ] revCE μ F f m := by
  -- `hF hmn` says `F m ≤ F n`. Use the tower property in the `≤` direction.
  -- i.e. `condExp μ (F m) (condExp μ (F n) f) = condExp μ (F m) f`.
  simp only [revCE]
  exact condExp_condExp_of_le (hF hmn) (h_le n)

/-- L¹ boundedness of the reverse martingale. -/
lemma revCE_L1_bdd
    [IsProbabilityMeasure μ]
    {F : ℕ → MeasurableSpace Ω}
    (h_le : ∀ n, F n ≤ (inferInstance : MeasurableSpace Ω))
    (f : Ω → ℝ) (hf : Integrable f μ) :
    ∀ n, eLpNorm (revCE μ F f n) 1 μ ≤ eLpNorm f 1 μ := by
  intro n
  simp only [revCE]
  exact eLpNorm_one_condExp_le_eLpNorm f

/-! ### Uniform integrability via Jensen and de la Vallée-Poussin

The following lemmas establish uniform integrability of the reverse martingale family.
These are standard results but not yet in mathlib. -/

/-- From the de la Vallée-Poussin tail condition `Φ(t)/t → ∞`, extract a threshold `R > 0`
such that `t ≤ Φ t` for all `t ≥ R`. This is used to control the small-values region
when applying the dvP criterion for uniform integrability. -/
lemma deLaValleePoussin_eventually_ge_id
    (Φ : ℝ → ℝ)
    (hΦ_tail : Tendsto (fun t : ℝ => Φ t / t) atTop atTop) :
    ∃ R > 0, ∀ ⦃t⦄, t ≥ R → t ≤ Φ t := by
  -- Take `M = 1`; eventually `Φ t / t ≥ 1`, hence `Φ t ≥ t` for large `t`.
  have h := (tendsto_atTop_atTop.1 hΦ_tail) 1
  rcases h with ⟨R, hR⟩
  refine ⟨max R 1, by positivity, ?_⟩
  intro t ht
  have ht' : t ≥ R := le_trans (le_max_left _ _) ht
  have hΦ_ge : Φ t / t ≥ 1 := hR t ht'
  -- `t > 0` for `t ≥ max R 1`
  have hpos : 0 < t := by linarith [le_max_right R 1]
  -- From `Φ t / t ≥ 1` and `t > 0`, deduce `Φ t ≥ t`
  have : 1 ≤ Φ t / t := hΦ_ge
  calc t = t * 1 := by ring
       _ ≤ t * (Φ t / t) := by exact mul_le_mul_of_nonneg_left this (le_of_lt hpos)
       _ = Φ t := by field_simp

/-- **Jensen inequality for conditional expectation with convex functions of the norm.**

For a convex function Φ on [0,∞) with Φ(0) = 0 and an integrable function f,
the composition Φ(‖E[f | m]‖) is a.e. bounded by E[Φ(‖f‖) | m].

**Proof strategy:**
1. Apply Jensen's inequality to the convex function Φ
2. Use convexity and the defining property of conditional expectation
3. Test against m-measurable bounded functions
4. Standard approximation argument (~20-30 lines)

**Mathlib status:** Not available as of v4.24.0. Needs implementation. -/
axiom condExp_jensen_norm
    {m : MeasurableSpace Ω} {μ : Measure Ω}
    (Φ : ℝ → ℝ) (hΦ_conv : ConvexOn ℝ (Set.Ici (0:ℝ)) Φ) (hΦ0 : Φ 0 = 0)
    (f : Ω → ℝ) (hf : Integrable f μ) :
    (fun x => Φ ‖μ[f | m] x‖) ≤ᵐ[μ] μ[(fun x => Φ ‖f x‖) | m]

/-- **Uniform integrability of conditional expectation family.**

The family {E[f | F n]} is uniformly integrable when f ∈ L¹.

**Proof strategy:**
1. Choose a de la Vallée-Poussin function Φ for ‖f‖:
   - Φ superlinear: Φ(t)/t → ∞ as t → ∞
   - Φ convex on [0,∞), Φ(0) = 0
   - ∫ Φ(‖f‖) dμ < ∞ (exists by integrability of f)
2. Apply Jensen inequality: ∫ Φ(‖E[f | F n]‖) ≤ ∫ E[Φ(‖f‖) | F n] = ∫ Φ(‖f‖)
3. Use de la Vallée-Poussin criterion: sup_n ∫ Φ(‖X_n‖) < ∞ ⇒ UI

**Mathlib status:** de la Vallée-Poussin criterion not in mathlib v4.24.0.
Alternative: prove UI directly by splitting on ‖E[f | F n]‖ ≤ R / > R. -/
axiom uniformIntegrable_condExp
    [IsProbabilityMeasure μ]
    (F : ℕ → MeasurableSpace Ω)
    (h_le : ∀ n, F n ≤ (inferInstance : MeasurableSpace Ω))
    (f : Ω → ℝ) (hf : Integrable f μ) :
    UniformIntegrable (fun n => revCE μ F f n) 1 μ

/-! ### Compactness from uniform integrability

From UI + integrability, we can extract a convergent subsequence. This is the
compactness property of uniformly integrable families. -/

/-- **Existence of de la Vallée-Poussin function.**

For any integrable function f, there exists a convex function Φ : [0,∞) → ℝ satisfying:
- Φ(0) = 0
- Φ is nondecreasing
- Φ is convex on [0,∞)
- Φ(t)/t → ∞ as t → ∞ (superlinearity)
- ∫ Φ(‖f‖) dμ < ∞

This is the de la Vallée-Poussin criterion for uniform integrability.

**Mathlib status:** Not available as of v4.24.0. The existence is standard (construct
via ∑ 2^n · min(1, ‖f‖ / 2^n) or similar). -/
axiom exists_deLaValleePoussin_function
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]
    {f : α → ℝ} (hf : Integrable f μ) :
    ∃ (Φ : ℝ → ℝ),
      Monotone Φ ∧
      ConvexOn ℝ (Set.Ici 0) Φ ∧
      Φ 0 = 0 ∧
      Tendsto (fun t => Φ t / t) atTop atTop ∧
      Integrable (fun x => Φ (‖f x‖)) μ

/-- Banach-valued L¹ contraction for conditional expectation:
`∫ ‖condExp μ m f‖ ≤ ∫ ‖f‖`. -/
lemma integral_norm_condExp_le
  {α β : Type*} [MeasurableSpace α] {μ : Measure α}
  [MeasurableSpace β] [NormedAddCommGroup β] [BorelSpace β] [CompleteSpace β]
  (m : MeasurableSpace α) {f : α → β} (hf : Integrable f μ) :
  ∫ x, ‖condExp μ m f x‖ ∂μ ≤ ∫ x, ‖f x‖ ∂μ := by
  -- TODO: Need Jensen inequality for Banach-valued condExp
  -- Strategy: Use Jensen with Φ = id, then integrate and apply tower property
  sorry

/-- Fatou on `ENNReal.ofReal ∘ ‖·‖` along an a.e. pointwise limit. -/
lemma lintegral_fatou_ofReal_norm
  {α β : Type*} [MeasurableSpace α] {μ : Measure α}
  [MeasurableSpace β] [NormedAddCommGroup β] [BorelSpace β]
  {u : ℕ → α → β} {g : α → β}
  (hae : ∀ᵐ x ∂μ, Tendsto (fun n => u n x) atTop (nhds (g x)))
  (hu_meas : ∀ n, AEMeasurable (fun x => ENNReal.ofReal ‖u n x‖) μ)
  (hg_meas : AEMeasurable (fun x => ENNReal.ofReal ‖g x‖) μ) :
  ∫⁻ x, ENNReal.ofReal ‖g x‖ ∂μ
    ≤ liminf (fun n => ∫⁻ x, ENNReal.ofReal ‖u n x‖ ∂μ) atTop := by
  -- Compose the a.e. convergence with continuity of `ofReal ∘ ‖·‖`.
  have hae_ofReal :
      ∀ᵐ x ∂μ,
        Tendsto (fun n => ENNReal.ofReal ‖u n x‖) atTop
                (nhds (ENNReal.ofReal ‖g x‖)) :=
    hae.mono (fun x hx =>
      ((ENNReal.continuous_ofReal.comp continuous_norm).tendsto _).comp hx)
  -- Apply Fatou in two steps: liminf equality + lintegral_liminf_le'
  calc ∫⁻ x, ENNReal.ofReal ‖g x‖ ∂μ
      = ∫⁻ x, liminf (fun n => ENNReal.ofReal ‖u n x‖) atTop ∂μ :=
          lintegral_congr_ae (hae_ofReal.mono fun x hx => hx.liminf_eq.symm)
    _ ≤ liminf (fun n => ∫⁻ x, ENNReal.ofReal ‖u n x‖ ∂μ) atTop :=
          lintegral_liminf_le' hu_meas

/-- **Integrable limit from a.e. convergence via Fatou + L¹ contraction.**

If `condExp μ (F (φ k)) f → g` a.e. along a subsequence, then `g ∈ L¹`.

Uses Fatou's lemma on `‖·‖` combined with the L¹ contraction property
`‖condExp μ m f‖₁ ≤ ‖f‖₁` to avoid circular dependency with Vitali. -/
lemma integrable_limit_of_ae_tendsto_condExp
    {α β : Type*} [MeasurableSpace α] {μ : Measure α}
    [MeasurableSpace β] [NormedAddCommGroup β] [NormedSpace ℝ β] [CompleteSpace β] [BorelSpace β]
    (F : ℕ → MeasurableSpace α) (f : α → β) (hf : Integrable f μ)
    (φ : ℕ → ℕ) {g : α → β}
    (hae : ∀ᵐ x ∂μ, Tendsto (fun k => (μ[f | F (φ k)]) x) atTop (nhds (g x))) :
    Integrable g μ := by
  classical
  -- Fatou on `ofReal ∘ ‖·‖`
  have hfatou :
      ∫⁻ x, ENNReal.ofReal ‖g x‖ ∂μ
        ≤ liminf (fun k => ∫⁻ x, ENNReal.ofReal ‖μ[f | F (φ k)] x‖ ∂μ) atTop := by
    have hmeas_u : ∀ k,
        AEMeasurable (fun x => ENNReal.ofReal ‖μ[f | F (φ k)] x‖) μ := by
      intro k
      exact integrable_condExp.aestronglyMeasurable.aemeasurable.norm.ennreal_ofReal
    have hmeas_g :
        AEMeasurable (fun x => ENNReal.ofReal ‖g x‖) μ := by
      have : AEStronglyMeasurable g μ :=
        aestronglyMeasurable_of_tendsto_ae atTop
          (fun k => integrable_condExp.aestronglyMeasurable) hae
      exact this.aemeasurable.norm.ennreal_ofReal
    exact lintegral_fatou_ofReal_norm (μ := μ)
      (u := fun k x => μ[f | F (φ k)] x) (g := g)
      hae hmeas_u hmeas_g

  -- Bound each term by L¹ contraction.
  have hbound :
      ∀ k, ∫⁻ x, ENNReal.ofReal ‖μ[f | F (φ k)] x‖ ∂μ
            ≤ ∫⁻ x, ENNReal.ofReal ‖f x‖ ∂μ := by
    intro k
    -- Use integral form of L¹ contraction, then convert to lintegral
    have hL1 : ∫ x, ‖μ[f | F (φ k)] x‖ ∂μ ≤ ∫ x, ‖f x‖ ∂μ :=
      integral_norm_condExp_le (μ := μ) (m := F (φ k)) (hf := hf)
    -- Convert to lintegral form using ofReal_integral_eq_lintegral_ofReal
    have lhs : ∫⁻ x, ENNReal.ofReal ‖μ[f | F (φ k)] x‖ ∂μ
               = ENNReal.ofReal (∫ x, ‖μ[f | F (φ k)] x‖ ∂μ) :=
      (ofReal_integral_eq_lintegral_ofReal integrable_condExp.norm (ae_of_all _ (fun _ => norm_nonneg _))).symm
    have rhs : ∫⁻ x, ENNReal.ofReal ‖f x‖ ∂μ
               = ENNReal.ofReal (∫ x, ‖f x‖ ∂μ) :=
      (ofReal_integral_eq_lintegral_ofReal hf.norm (ae_of_all _ (fun _ => norm_nonneg _))).symm
    rw [lhs, rhs]
    exact ENNReal.ofReal_le_ofReal hL1

  -- Chain: Fatou + uniform bound ⇒ finiteness of `∫⁻ ofReal ‖g‖`.
  have : ∫⁻ x, ENNReal.ofReal ‖g x‖ ∂μ ≤ ∫⁻ x, ENNReal.ofReal ‖f x‖ ∂μ := by
    refine le_trans hfatou ?_
    -- liminf of a sequence bounded above by a constant ≤ that constant
    -- Use liminf of constant = constant, then liminf_le_liminf
    have : liminf (fun k => ∫⁻ x, ENNReal.ofReal ‖μ[f | F (φ k)] x‖ ∂μ) atTop
           ≤ liminf (fun _ : ℕ => ∫⁻ x, ENNReal.ofReal ‖f x‖ ∂μ) atTop :=
      liminf_le_liminf (Eventually.of_forall hbound)
    rw [liminf_const] at this
    exact this
  -- Turn finite `lintegral (ofReal ‖g‖)` into `Integrable g`.
  have hfin : (∫⁻ x, ENNReal.ofReal ‖g x‖ ∂μ) < ⊤ := by
    refine lt_of_le_of_lt this ?_
    have := hasFiniteIntegral_iff_norm f |>.1 hf.hasFiniteIntegral
    simpa using this
  -- Convert: HasFiniteIntegral g + AEStronglyMeasurable g → Integrable g
  have hg_aemeas : AEStronglyMeasurable g μ := by
    -- g is ae strongly measurable as pointwise limit of ae strongly measurable sequence
    refine aestronglyMeasurable_of_tendsto_ae atTop (fun k => ?_) hae
    exact integrable_condExp.aestronglyMeasurable
  have : HasFiniteIntegral g μ := hasFiniteIntegral_iff_norm g |>.2 hfin
  exact ⟨hg_aemeas, this⟩

/-- **Vitali L¹ convergence from a.e. convergence + UI.**

For the reverse martingale E[f | F n] with decreasing filtration F n,
if E[f | F n] → g a.e., then E[f | F n] → g in L¹.

**Proof strategy:**
1. UI from `uniformIntegrable_condExp` (already have)
2. Integrable limit g from `integrable_limit_of_ae_tendsto_condExp`
3. Apply Vitali: `tendsto_Lp_finite_of_tendsto_ae` with p = 1

This is the key to Lévy's downward theorem: a.e. convergence + UI ⇒ L¹ convergence. -/
lemma tendsto_L1_condExp_of_ae
    [IsProbabilityMeasure μ]
    (F : ℕ → MeasurableSpace Ω) (f : Ω → ℝ)
    (h_le : ∀ n, F n ≤ (inferInstance : MeasurableSpace Ω))
    (hf : Integrable f μ)
    {g : Ω → ℝ}
    (hg_meas : AEStronglyMeasurable g μ)
    (hae : ∀ᵐ x ∂μ, Tendsto (fun n => (μ[f | F n]) x) atTop (𝓝 (g x))) :
    Tendsto (fun n => eLpNorm (μ[f | F n] - g) 1 μ) atTop (𝓝 0) := by
  classical
  -- Step 1: UI from uniformIntegrable_condExp
  have hUI : UniformIntegrable (fun n => revCE μ F f n) 1 μ :=
    uniformIntegrable_condExp F h_le f hf

  -- Step 2: Integrable limit g from Part 1 (using full sequence, φ = id)
  have hg : Integrable g μ :=
    integrable_limit_of_ae_tendsto_condExp (μ := μ) F f hf id hae

  -- Step 3: Apply Vitali (p = 1)
  have hgmem : MemLp g 1 μ := by
    rw [memLp_one_iff_integrable]
    exact hg

  -- Extract UnifIntegrable (measure theory version) from UniformIntegrable (probability version)
  have hUnifInt : UnifIntegrable (fun n => μ[f | F n]) 1 μ := by
    -- UniformIntegrable = ae measurable + UnifIntegrable + bounded
    exact hUI.unifIntegrable

  -- Extract ae strong measurability (condExp is always ae strongly measurable)
  have hae_meas : ∀ n, AEStronglyMeasurable (μ[f | F n]) μ := by
    intro n
    exact integrable_condExp.aestronglyMeasurable

  -- Apply Vitali with p = 1
  have hp : (1 : ENNReal) ≤ 1 := le_refl _
  have hp' : (1 : ENNReal) ≠ ⊤ := ENNReal.one_ne_top
  exact tendsto_Lp_finite_of_tendsto_ae hp hp' hae_meas hgmem hUnifInt hae

/-- **Axiom 1.** From uniform integrability and integrability, extract a subsequence
that converges a.e. (and hence, by Vitali, in L¹) to some integrable limit `g`.

**Proof strategy:**
1. UI ⇒ compactness in measure (mathlib: `UniformIntegrable.compactInMeasure`)
2. Compactness ⇒ subsequence converging in measure to some g
3. Convergence in measure ⇒ further subsequence converging a.e.
4. UI + a.e. convergence ⇒ L¹ convergence (Vitali)
5. L¹ convergence ⇒ limit is integrable -/
theorem UniformIntegrable.exists_ae_tendsto_subseq_of_integrable
    [IsProbabilityMeasure μ]
    {u : ℕ → Ω → ℝ}
    (hUI : UniformIntegrable (fun n x => ‖u n x‖) 1 μ)
    (hint : ∀ n, Integrable (u n) μ) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∃ g : Ω → ℝ, Integrable g μ ∧
        (∀ᵐ x ∂μ, Tendsto (fun k => u (φ k) x) atTop (𝓝 (g x)))
        ∧ Tendsto (fun k => eLpNorm (u (φ k) - g) 1 μ) atTop (𝓝 0) := by
  classical
  -- Step 1: Compactness in measure ⇒ a subsequence converges **in measure**
  -- NOTE: This requires UI → compactness in measure, which is NOT in mathlib v4.24.0
  -- We axiomatize this step pending mathlib addition
  obtain ⟨φ, hφ_mono, g, h_in_measure⟩ : ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∃ g : Ω → ℝ, TendstoInMeasure μ (fun k => u (φ k)) atTop g := by
    sorry -- TODO: UI → compactness in measure (not yet in mathlib)

  -- Step 2: From convergence in measure, extract a further subsequence with a.e. convergence
  -- mathlib: `TendstoInMeasure.exists_seq_tendsto_ae`
  obtain ⟨ψ, hψ_mono, hae⟩ : ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
      ∀ᵐ x ∂μ, Tendsto (fun k => u (φ (ψ k)) x) atTop (𝓝 (g x)) := by
    exact h_in_measure.exists_seq_tendsto_ae

  -- Step 3: Vitali upgrades a.e. → L¹ using uniform integrability
  -- UI is stable under subsequences (mathematical fact, but no direct lemma in mathlib)
  have hUI' : UniformIntegrable (fun k x => ‖u (φ (ψ k)) x‖) 1 μ := by
    sorry -- TODO: UI.comp_strictMono (not yet in mathlib)

  have hint' : ∀ k, Integrable (u (φ (ψ k))) μ := by
    intro k
    exact hint _

  -- Step 4: Extract integrability of g using a.e. convergence + UI
  -- First, we need g to be ae strongly measurable
  have hg_meas : AEStronglyMeasurable g μ := by
    refine aestronglyMeasurable_of_tendsto_ae atTop (fun k => ?_) hae
    exact (hint' k).1

  -- Step 5: Extract g ∈ L¹ from the facts that u (φ (ψ k)) → g a.e. and uniformly bounded in L¹
  have hg : Integrable g μ := by
    sorry -- Will use UI + a.e. convergence → Fatou → g ∈ L¹

  -- Vitali: a.e. + UI + g ∈ L¹ ⇒ L¹ convergence
  have hL1 : Tendsto (fun k => eLpNorm (u (φ (ψ k)) - g) 1 μ) atTop (𝓝 0) := by
    sorry -- TODO: Apply tendsto_Lp_finite_of_tendsto_ae

  -- Package the chosen subsequence
  refine ⟨(fun k => φ (ψ k)), (hφ_mono.comp hψ_mono), g, hg, ?_, ?_⟩
  · -- a.e. convergence along the composed subsequence
    exact hae
  · -- L¹ convergence along the composed subsequence
    exact hL1

/-- **Conditional expectation converges along decreasing filtration (Lévy's downward theorem).**

For a decreasing filtration 𝔽ₙ and integrable f, the sequence
  Mₙ := E[f | 𝔽ₙ]
converges a.s. to E[f | ⨅ₙ 𝔽ₙ].

**Proof strategy:** This is a reverse martingale convergence theorem. We prove it directly using:
1. **L¹ contraction:** ‖E[f | 𝔽ₙ]‖₁ ≤ ‖f‖₁ uniformly in n (mathlib)
2. **Tower property:** For m ≥ n, E[E[f | 𝔽ₙ] | 𝔽ₘ] = E[f | 𝔽ₘ] (reverse martingale)
3. **Uniform integrability:** Via de la Vallée-Poussin (Jensen inequality for condexp)
4. **Vitali:** UI + subsequence a.e. convergence ⇒ full a.e. convergence
5. **Limit identification:** Test on A ∈ ⨅ 𝔽ₙ to show limit = E[f | ⨅ 𝔽ₙ]

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
  -- **The missing piece:** Reverse martingale a.e. convergence to the tail σ-algebra
  -- This is the core of Lévy's downward theorem, requiring the upcrossing inequality.
  --
  -- **Standard proof (~100-150 lines):**
  -- 1. Define reverse upcrossings: for interval [a,b], count how many times
  --    the sequence crosses from below a to above b as n increases
  -- 2. Prove reverse upcrossing inequality: E[# upcrossings] ≤ E[|X₀ - a|] / (b - a)
  -- 3. Show: finitely many upcrossings a.e. for all rational [a,b]
  -- 4. Deduce: the sequence {E[f | 𝔽 n]} converges a.e.
  -- 5. Identify the limit as E[f | ⨅ 𝔽 n] using tower property
  --
  -- **Why this is hard:** Requires careful analysis of stopped sequences and
  -- optional stopping theorem for reverse martingales.
  sorry

/-- **Conditional expectation converges along increasing filtration (Doob/Levy upward).**

For an increasing filtration 𝔽ₙ and integrable f, the sequence
  Mₙ := E[f | 𝔽ₙ]
converges a.s. to E[f | ⨆ₙ 𝔽ₙ].

**Mathematical statement:**
Let 𝔽ₙ ↗ be an increasing filtration (𝔽ₙ ⊆ 𝔽ₙ₊₁) and f ∈ L¹(μ). Then:
  E[f | 𝔽ₙ] → E[f | ⨆ₙ 𝔽ₙ]  a.s.

**Why needed for de Finetti:**
The finite future σ-algebras finFutureSigma X m k form an increasing sequence in k,
converging to the infinite future σ-algebra futureFiltration X m.
We use this to pass from finite approximations to the infinite case.

**This is the dual of Lévy's downward theorem** - same proof technique applies.

**Implementation:** This is now a direct wrapper around mathlib's `MeasureTheory.tendsto_ae_condExp`
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

### Fully Implemented (No Axioms)
- **`condExp_tendsto_iSup` (Lévy upward)**: ✅ Direct wrapper around mathlib's
  `MeasureTheory.tendsto_ae_condExp` from `Mathlib.Probability.Martingale.Convergence`.
  Clean 3-line proof packaging the filtration and forwarding to mathlib.

### Partially Implemented (1 Sorry)
- **`condExp_tendsto_iInf` (Lévy downward)**: ⚠️ Structure complete, awaiting proof of
  convergence. Current implementation explores transformation strategy but hits fundamental
  limitation (see detailed comments in proof at line ~233).

### Mathlib Gap Identified
Investigation of `Mathlib.Probability.Martingale.Convergence` (v4.24.0) reveals:
- ✅ Submartingale convergence for **increasing** filtrations (`tendsto_ae_condExp`)
- ❌ No supermartingale convergence for **decreasing** filtrations
- ❌ No reverse martingale convergence theorems

The attempted transformation `G k := ⨆_{n ≤ k} 𝔽 n` for antitone `𝔽` yields a constant
sequence `G k = 𝔽 0` (proved in `iSup_of_antitone_eq`), which cannot provide convergence
to `⨅ k, 𝔽 k`.

### Still Axiomatized (Intentionally)
- `reverseMartingaleLimit*` family: More general witness functions for reverse martingale limits
- Used in `ViaMartingale.lean`; await mathlib development or future implementation

### Path Forward for `condExp_tendsto_iInf`
**Option 1**: Direct proof from upcrossings (500-1000 lines estimated)
  - Define reverse upcrossings for decreasing processes
  - Prove reverse upcrossing inequality
  - Show bounded reverse upcrossings ⇒ convergence
  - Identify limit via uniform integrability

**Option 2**: Wait for mathlib to add reverse martingale convergence
  - Active area of probability theory development
  - Natural next step after current submartingale theory

**Option 3**: Keep as well-documented sorry/axiom
  - Only affects `ViaMartingale.lean` (one of three de Finetti proofs)
  - `ViaL2.lean` and `ViaKoopman.lean` are independent
  - Standard result with multiple textbook proofs

### Dependencies from Mathlib
- ✅ `MeasureTheory.tendsto_ae_condExp`: Lévy upward (used)
- ✅ `Filtration`: Filtration structure (used)
- ✅ `condExp_condExp_of_le`: Tower property (available, not yet used)
- ❌ Reverse martingale convergence: Not available -/

end Exchangeability.Probability
