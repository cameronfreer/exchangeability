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

Sketch of proof (to be filled in later): first choose the cylinder σ-algebra
and use the π-λ (Dynkin) theorem to reduce the problem to cylinder sets (cf.
mathlib's `MeasurableSpace.induction_on_inter`). Next, expand the measurability
gymnastics from the previous (now deleted) script to compare the push-forwards
`Measure.map` along the restriction maps to finite coordinates, keeping track of
the finite index embeddings explicitly. Finally, invoke uniqueness for the
kernels produced by the Ionescu–Tulcea construction
(`ProbabilityTheory.Kernel.traj`) to conclude that the induced measures on path
space agree.

At the invariant σ-algebra level, we expect to appeal to the results in FMP 10.3
and 10.4 (measurable invariants vs almost invariants, ergodicity) to relate the
shift actions on path space to the fixed-point σ-field appearing in the
Kolmogorov extension.

The present statement is kept as an axiom so that downstream files do not rely on
the unfinished technical proof. -/
axiom measure_eq_of_fin_marginals_eq {μ ν : Measure (ℕ → α)}
    (h : ∀ n (S : Set (Fin n → α)) (hS : MeasurableSet S),
        Measure.map (fun f : ℕ → α => fun i : Fin n => f i) μ S =

/-- **Axiom**: exchangeability is equivalent to full exchangeability.

The intended proof sketch is the following, based on Kallenberg's second proof
and the Ionescu–Tulcea theorem. First define the path-space measures `μ_X` and
`μ_Xπ` as push-forwards of the base measure by `ω ↦ (X n ω)` and `ω ↦ (X (π n)
ω)`; next check, using exchangeability of `X`, that their finite-dimensional
marginals agree (combining the permutation arguments with FMP 10.3/10.4 to
control the invariant σ-fields). Then apply `measure_eq_of_fin_marginals_eq`
above to deduce `μ_X = μ_Xπ`, and finally map back along the evaluation map to
conclude `Measure.map (ω ↦ X (π i) ω) μ = Measure.map (ω ↦ X i ω) μ`, i.e. full
exchangeability.

Steps (2)–(4) will eventually be formalised using the previous implementation of
the permutation/shifting arguments together with the axiom above; they are left
as comments for now so that the rest of the project can continue to evolve. -/
axiom exchangeable_iff_fullyExchangeable {μ : Measure Ω} {X : ℕ → Ω → α}
    (hX_meas : ∀ i, Measurable (X i)) : Exchangeable μ X ↔ FullyExchangeable μ X

end Exchangeability
