import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Exchangeability.Contractability

/-- Exchangeability for infinite sequences (axiomatic stub).

To keep other parts of the project compiling while the full development is in
progress, we record the main results here as axioms. -/

noncomputable section

namespace Exchangeability

open MeasureTheory

variable {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]

/-- **Axiom**: measures on path space are determined by their finite-dimensional marginals.

Sketch (to be formalised later): choose the cylinder σ-algebra and use the
π-λ/Dynkin theorem (`MeasurableSpace.induction_on_inter`) to reduce the problem
to cylinder sets. Then revisit the measurability gymnastics from the previous
implementation to compare the push-forwards `Measure.map` along the restriction
maps to finite coordinates, carefully tracking the finite index embeddings.
Finally, invoke uniqueness for the kernels produced by the Ionescu–Tulcea
construction (`ProbabilityTheory.Kernel.traj`) to conclude that the induced
measures on path space agree. Along the way, FMP 10.3 and 10.4 (relating
invariant and almost invariant σ-fields, ergodicity) are expected to control the
tail σ-field appearing in the extension argument. -/
axiom measure_eq_of_fin_marginals_eq {μ ν : Measure (ℕ → α)}
    (h : ∀ n (S : Set (Fin n → α)) (hS : MeasurableSet S),
        Measure.map (fun f : ℕ → α => fun i : Fin n => f i) μ S =


/-- **Axiom**: exchangeability is equivalent to full exchangeability.

Sketch (to mirror Kallenberg's second proof): define the path-space measures
`μ_X` and `μ_Xπ` as push-forwards of the base measure by `ω ↦ (X n ω)` and
`ω ↦ (X (π n) ω)`. Using exchangeability (and the invariant σ-field facts from
FMP 10.3/10.4) show that their finite-dimensional marginals agree; then apply
`measure_eq_of_fin_marginals_eq` to deduce `μ_X = μ_Xπ`. Finally evaluate back
along the coordinate map to obtain
`Measure.map (ω ↦ X (π i) ω) μ = Measure.map (ω ↦ X i ω) μ`, i.e. full
exchangeability. -/
axiom exchangeable_iff_fullyExchangeable {μ : Measure Ω} {X : ℕ → Ω → α}
    (hX_meas : ∀ i, Measurable (X i)) : Exchangeable μ X ↔ FullyExchangeable μ X

end Exchangeability
