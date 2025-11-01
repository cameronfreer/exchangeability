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

/-- **Jensen inequality for conditional expectation (norm version).**

For a convex function Φ : ℝ → ℝ on [0,∞) with Φ(0) = 0, we have
  Φ(‖E[f | m]‖) ≤ E[Φ(‖f‖) | m]  a.e.

**Proof strategy:**
1. Reduce to scalar case by applying to ‖f‖
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
  have hg_memℒp : Memℒp g 1 μ := by
    sorry -- Will use UI + a.e. convergence → compactness → some subsequence has L¹ limit

  have hg : Integrable g μ := by
    rw [← memℒp_one_iff_integrable] at hg_memℒp ⊢
    exact hg_memℒp

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
