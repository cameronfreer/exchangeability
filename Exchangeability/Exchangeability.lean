import Exchangeability.Contractability

/-- Exchangeability for infinite sequences (axiomatic stub).

To keep other parts of the project compiling while the full development is in
progress, we record the main results here as axioms. -/

noncomputable section

namespace Exchangeability

variable {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]

/-- **Axiom**: measures on path space are determined by their finite-dimensional marginals. -/
axiom measure_eq_of_fin_marginals_eq {μ ν : Measure (ℕ → α)}
    (h : ∀ n (S : Set (Fin n → α)) (hS : MeasurableSet S),
        Measure.map (fun f : ℕ → α => fun i : Fin n => f i) μ S =
        Measure.map (fun f : ℕ → α => fun i : Fin n => f i) ν S) : μ = ν

/-- **Axiom**: exchangeability is equivalent to full exchangeability. -/
axiom exchangeable_iff_fullyExchangeable {μ : Measure Ω} {X : ℕ → Ω → α}
    (hX_meas : ∀ i, Measurable (X i)) : Exchangeable μ X ↔ FullyExchangeable μ X

end Exchangeability
