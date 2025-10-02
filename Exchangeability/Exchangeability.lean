/-- Exchangeability for infinite sequences.

This file reuses the basic definitions from `Exchangeability/Contractability.lean`
and focuses on the Kolmogorov-style equivalence between exchangeability and full
exchangeability.
-/
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Probability.Kernel.IonescuTulcea.Traj
import Exchangeability.Contractability

noncomputable section
open scoped BigOperators MeasureTheory Topology Classical

namespace Exchangeability

open MeasureTheory Filter

variable {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]

/-- Exchangeability implies full exchangeability (Kolmogorov extension theorem).

For an exchangeable family `X`, the finite-dimensional distributions satisfy the
consistency conditions required by Kolmogorov's extension theorem. This allows us
to construct a unique probability measure on the infinite product space such that
the process is fully exchangeable.

**Proof strategy**: Use mathlib's Ionescu-Tulcea theorem (`ProbabilityTheory.Kernel.traj`),
which constructs infinite products of probability kernels. For the constant kernel
case (which suffices here), the finite-dimensional distributions of an exchangeable
process satisfy the required consistency conditions, and the Ionescu-Tulcea
construction yields a unique measure on the infinite product that is invariant
under all permutations.
-/
theorem exchangeable_iff_fullyExchangeable {μ : Measure Ω} {X : ℕ → Ω → α}
    [IsProbabilityMeasure μ] (hX_meas : ∀ i, Measurable (X i)) :
    Exchangeable μ X ↔ FullyExchangeable μ X := by
  constructor
  · intro hexch π
    -- Strategy: Use uniqueness from Ionescu-Tulcea/Kolmogorov extension
    
    -- Step 1: Define the pushforward measures for X and X ∘ π
    let μ_X := Measure.map (fun ω => fun n : ℕ => X n ω) μ
    let μ_Xπ := Measure.map (fun ω => fun n : ℕ => X (π n) ω) μ
    
    -- Step 2: Both are probability measures on ℕ → α
    -- These instances are needed for the finite measure uniqueness arguments in h_unique.
    have hμ_X : IsProbabilityMeasure μ_X := by
      -- Pushforward of probability measure is probability measure
      constructor
      show μ_X Set.univ = 1
      simp only [μ_X, Measure.map_apply (measurable_pi_lambda _ (fun i => hX_meas i)) MeasurableSet.univ]
      simp
    have hμ_Xπ : IsProbabilityMeasure μ_Xπ := by
      -- Pushforward of probability measure is probability measure
      constructor
      show μ_Xπ Set.univ = 1
      simp only [μ_Xπ, Measure.map_apply (measurable_pi_lambda _ (fun i => hX_meas (π i))) MeasurableSet.univ]
      simp
    
    -- Step 3: Show finite-dimensional marginals agree
    have h_marginals : ∀ (n : ℕ) (S : Set (Fin n → α)) (hS : MeasurableSet S),
        μ_X.map (fun f : ℕ → α => fun i : Fin n => f i) S =
        μ_Xπ.map (fun f : ℕ → α => fun i : Fin n => f i) S := by
      intro n S hS
      -- TODO: reuse contractability lemmas to avoid combinatorial explosion.
      sorry
    
    -- Step 4: Kolmogorov uniqueness via π-λ theorem
    have h_unique : μ_X = μ_Xπ := by
      -- Show equality on cylinder sets and extend by Dynkin π-λ theorem
      sorry
    
    -- Step 5: Conclude equal laws
    calc
      Measure.map (fun ω => fun i : ℕ => X (π i) ω) μ
          = μ_Xπ := rfl
      _ = μ_X := h_unique.symm
      _ = Measure.map (fun ω => fun i : ℕ => X i ω) μ := rfl
  · intro hfull
    exact FullyExchangeable.exchangeable hX_meas hfull

end Exchangeability
