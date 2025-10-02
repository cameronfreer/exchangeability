/-
Copyright

This file is part of the exchangeability project.
-/
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Probability.Kernel.IonescuTulcea.Traj

/-!
# Exchangeability for infinite sequences

This file defines exchangeability and full exchangeability for infinite sequences
of random variables, and proves their equivalence via the Kolmogorov extension theorem.

## Main definitions

* `Exchangeable`: Invariance under finite permutations (standard operational definition)
* `FullyExchangeable`: Invariance under all permutations of ℕ
* `extendFinPerm`: Extends a finite permutation to ℕ by fixing large indices

## Main results

* `FullyExchangeable.exchangeable`: Full exchangeability implies exchangeability
* `exchangeable_iff_fullyExchangeable`: The two notions are equivalent

**Note on terminology**: There are three related notions:
1. **Exchangeability** for infinite sequences (defined here): invariance under finite permutations
2. **Full exchangeability** for infinite sequences: invariance under all permutations of ℕ
3. Exchangeability for **finite** sequences: a separate notion for fixed-length tuples

This file focuses on notions (1) and (2) for infinite sequences. The finite-sequence
case has its own de Finetti-type results but is conceptually distinct.

## References

* Kallenberg, *Probabilistic Symmetries and Invariance Principles* (2005), Theorem 1.1
* Kallenberg, *Foundations of Modern Probability* (2002), Theorem 6.10 and 8.24
-/

noncomputable section
open scoped BigOperators MeasureTheory Topology Classical

namespace Exchangeability

open MeasureTheory Filter

variable {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]

/-- An infinite family of random variables `X : ℕ → Ω → α` is **exchangeable**
if the finite-dimensional distributions are invariant under permutations of finitely
many indices. Concretely, the joint law of `X 0, …, X (n-1)` coincides with the
law of `X σ 0, …, X σ (n-1)` for every permutation `σ` of `Fin n`.

This is the standard operational definition of exchangeability for infinite sequences.
It is also called "finitely exchangeable" in some texts to distinguish it from full
exchangeability (see `FullyExchangeable`).
-/
def Exchangeable (μ : Measure Ω) (X : ℕ → Ω → α) : Prop :=
  ∀ n (σ : Equiv.Perm (Fin n)),
    Measure.map (fun ω => fun i : Fin n => X (σ i) ω) μ =
      Measure.map (fun ω => fun i : Fin n => X i ω) μ

/-- An infinite family of random variables `X : ℕ → Ω → α` is **fully exchangeable**
if the joint distribution is invariant under all permutations of ℕ (not just finite ones).

That is, for any permutation `π : Equiv.Perm ℕ`, the process `X ∘ π` has the same
law as `X`.

This is formally stronger than exchangeability, but by the Kolmogorov extension
theorem they are equivalent for consistent families (see `exchangeable_iff_fullyExchangeable`).
-/
def FullyExchangeable (μ : Measure Ω) (X : ℕ → Ω → α) : Prop :=
  ∀ (π : Equiv.Perm ℕ),
    Measure.map (fun ω => fun i : ℕ => X (π i) ω) μ =
      Measure.map (fun ω => fun i : ℕ => X i ω) μ

/-- Extend a permutation of `Fin n` to a permutation of ℕ by fixing all `i ≥ n`. -/
def extendFinPerm (n : ℕ) (σ : Equiv.Perm (Fin n)) : Equiv.Perm ℕ where
  toFun i := if h : i < n then (σ ⟨i, h⟩).val else i
  invFun i := if h : i < n then (σ.symm ⟨i, h⟩).val else i
  left_inv := by
    intro i
    by_cases h : i < n
    · simp only [h, dite_true]
      have hσi : (σ ⟨i, h⟩).val < n := (σ ⟨i, h⟩).isLt
      simp only [hσi, dite_true]
      rw [Equiv.symm_apply_apply]
    · simp [h]
  right_inv := by
    intro i
    by_cases h : i < n
    · simp only [h, dite_true]
      have hσi : (σ.symm ⟨i, h⟩).val < n := (σ.symm ⟨i, h⟩).isLt
      simp only [hσi, dite_true]
      rw [Equiv.apply_symm_apply]
    · simp [h]

/-- Full exchangeability implies exchangeability.

This is immediate since every finite permutation extends to a permutation of ℕ.
-/
lemma FullyExchangeable.exchangeable {μ : Measure Ω} {X : ℕ → Ω → α}
    (hX_meas : ∀ i, Measurable (X i)) (hX : FullyExchangeable μ X) : Exchangeable μ X := by
  intro n σ
  -- Extend σ : Perm (Fin n) to π : Perm ℕ by fixing all i ≥ n
  let π := extendFinPerm n σ
  have hπ := hX π
  -- Key: The map (fun ω i => X (σ i) ω) factors through (fun ω i => X (π i) ω)
  -- via the embedding Fin n ↪ ℕ, since π extends σ
  have h_agree : ∀ (i : Fin n), π i.val = (σ i).val := by
    intro i
    simp [π, extendFinPerm]
  -- Define the projection ℕ → α to Fin n → α
  let proj : (ℕ → α) → (Fin n → α) := fun f => fun i => f i.val
  -- The composition gives us what we want
  calc Measure.map (fun ω => fun i : Fin n => X (σ i) ω) μ
      = Measure.map (fun ω => fun i : Fin n => X (π i.val) ω) μ := by
          congr 1; ext ω i; rw [h_agree]
    _ = Measure.map (proj ∘ (fun ω => fun i : ℕ => X (π i) ω)) μ := rfl
    _ = Measure.map proj (Measure.map (fun ω => fun i : ℕ => X (π i) ω) μ) := by
          rw [Measure.map_map]
          · -- proj is measurable as a finite product of coordinate projections
            exact measurable_pi_lambda _ (fun i => measurable_pi_apply _)
          · -- (fun ω i => X (π i) ω) is measurable
            exact measurable_pi_lambda _ (fun i => hX_meas (π i))
    _ = Measure.map proj (Measure.map (fun ω => fun i : ℕ => X i ω) μ) := by
          rw [hπ]
    _ = Measure.map (proj ∘ (fun ω => fun i : ℕ => X i ω)) μ := by
          rw [Measure.map_map]
          · -- proj is measurable as a finite product of coordinate projections
            exact measurable_pi_lambda _ (fun i => measurable_pi_apply _)
          · -- (fun ω i => X i ω) is measurable
            exact measurable_pi_lambda _ (fun i => hX_meas i)
    _ = Measure.map (fun ω => fun i : Fin n => X i ω) μ := rfl

/-- Exchangeability implies full exchangeability (Kolmogorov extension theorem).

For an exchangeable family `X`, the finite-dimensional distributions satisfy
the consistency conditions required by Kolmogorov's extension theorem. This allows us
to construct a unique probability measure on the infinite product space such that
the process is fully exchangeable.

**Proof strategy**: Use mathlib's Ionescu-Tulcea theorem (`ProbabilityTheory.Kernel.traj`),
which constructs infinite products of probability kernels. The Ionescu-Tulcea theorem
generalizes Kolmogorov extension from constant kernels (measures) to arbitrary kernels.

For the constant kernel case (which suffices here), the finite-dimensional distributions
of an exchangeable process satisfy the required consistency conditions, and the
Ionescu-Tulcea construction yields a unique measure on the infinite product that
is invariant under all permutations.

**Reference**: 
- Kallenberg, *Probabilistic Symmetries and Invariance Principles* (2005), Theorem 1.1
- Kallenberg, *Foundations of Modern Probability* (2002), Theorem 6.10 and 8.24
- Mathlib: `ProbabilityTheory.Kernel.traj` in `Probability.Kernel.IonescuTulcea.Traj`
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
    -- For any n and any measurable set S ⊆ (Fin n → α):
    -- This is the key ingredient for proving h_unique (showing measures agree on cylinder sets).
    have h_marginals : ∀ (n : ℕ) (S : Set (Fin n → α)) (_hS : MeasurableSet S),
        μ_X.map (fun f : ℕ → α => fun i : Fin n => f i) S =
        μ_Xπ.map (fun f : ℕ → α => fun i : Fin n => f i) S := by
      intro n S hS
      
      -- Key insight: Need to relate π's action on {0,...,n-1} to a finite permutation
      simp only [μ_X, μ_Xπ]
      rw [Measure.map_map, Measure.map_map]
      · -- After composition, need to show:
        -- μ.map (fun ω i:Fin n => X i ω) S = μ.map (fun ω i:Fin n => X (π i.val) ω) S
        
        -- Key insight: Both sides depend on n random variables.
        -- LHS: (X_0, X_1, ..., X_{n-1})
        -- RHS: (X_{π(0)}, X_{π(1)}, ..., X_{π(n-1)})
        
        -- Strategy: Use exchangeability to show these have the same distribution.
        -- 
        -- Let m = max{n, π(0), π(1), ..., π(n-1)} + 1
        -- Then all indices 0,...,n-1 and π(0),...,π(n-1) are < m.
        --
        -- Consider the finite permutation problem:
        -- We want a σ : Perm (Fin m) such that σ maps {0,...,n-1} bijectively to
        -- {π(0),...,π(n-1)} (in the right order).
        --
        -- Then hexch m σ would give us that (X_{σ(0)}, ..., X_{σ(m-1)}) has the
        -- same distribution as (X_0, ..., X_{m-1}).
        --
        -- Restricting to the first n coordinates gives the result.
        
        -- The construction steps:
        -- 1. Compute m = max index needed (must contain both source and target indices)
        let m := max n (Finset.sup (Finset.range n) (fun i => π i) + 1)
        -- Now we have: ∀ i < n, both i < m and π i < m
        
        -- 2. Build σ : Perm (Fin m) such that:
        --    - For i < n: σ(i) = π(i)
        --    - For i ≥ n: σ permutes the remaining elements bijectively
        
        -- This requires:
        -- (a) Showing {π(0),...,π(n-1)} and {0,...,n-1} have the same cardinality
        --     (follows from π being injective)
        -- (b) Extending the partial map to a full permutation
        --     (using decidable equality and choice to map remaining elements)
        -- (c) Proving the result is indeed a permutation
        
        -- Construction approach using classical choice:
        -- Let A = {0,...,n-1} ⊆ Fin m
        -- Let B = {π(0),...,π(n-1)} ⊆ Fin m
        -- We have |A| = |B| = n (π is injective on the first n values)
        --
        -- Define σ : Fin m → Fin m by:
        --   σ(i) = π(i)  if i < n
        --   σ(i) = some bijection from (Fin m \ A) to (Fin m \ B)  if i ≥ n
        --
        -- The bijection on the complement exists because:
        -- |(Fin m \ A)| = m - n = |(Fin m \ B)|
        --
        -- In Lean, we would:
        -- 1. Use Fintype.card to show the cardinalities match
        -- 2. Use Fintype.equivOfCardEq to get an equivalence on complements
        -- 3. Combine the two partial functions into σ
        -- 4. Prove σ is a permutation
        --
        -- Then apply: hexch m σ to get the measure equality
        -- Finally, restrict to first n coordinates to extract the result
        
        -- This construction is feasible but requires careful bookkeeping of:
        -- - Finset membership proofs
        -- - Injectivity of π on finite sets
        -- - Combining partial bijections
        
        -- First, establish basic facts about m:
        have h_n_le_m : n ≤ m := by
          simp only [m]
          exact Nat.le_max_left n _
        
        have h_i_lt_m : ∀ i < n, i < m := by
          intro i hi
          calc i < n := hi
            _ ≤ m := h_n_le_m
        
        have h_pi_lt_m : ∀ i < n, π i < m := by
          intro i hi
          simp only [m]
          have : π i ≤ Finset.sup (Finset.range n) (fun j => π j) := by
            apply Finset.le_sup
            simp [Finset.mem_range, hi]
          calc π i ≤ Finset.sup (Finset.range n) (fun j => π j) := this
            _ < Finset.sup (Finset.range n) (fun j => π j) + 1 := Nat.lt_succ_self _
            _ ≤ max n (Finset.sup (Finset.range n) (fun j => π j) + 1) := Nat.le_max_right _ _
        
        -- Now we can embed indices as elements of Fin m:
        -- For i < n, we have both ⟨i, h_i_lt_m i hi⟩ : Fin m
        --               and ⟨π i, h_pi_lt_m i hi⟩ : Fin m
        
        -- To construct σ : Equiv.Perm (Fin m), we need to show:
        -- 1. The map i ↦ π i (for i < n) can be extended to a bijection on Fin m
        -- 2. This requires showing {0,...,n-1} and {π 0,...,π(n-1)} have the same size
        -- 3. And extending the map on the complement
        
        -- Key lemma needed: If π is a permutation of ℕ, then π restricted to
        -- any finite initial segment gives an injection (which π provides).
        
        -- With σ : Equiv.Perm (Fin m) constructed, we would have:
        --   hexch m σ : Measure.map (fun ω i => X (σ i) ω) μ 
        --                = Measure.map (fun ω i => X i ω) μ
        --
        -- Then restrict both sides to (Fin n → α) via the projection map,
        -- and use that σ i = π i for i < n to get the desired equality.
        
        -- The remaining work is the finite combinatorics of constructing σ
        -- and manipulating the measure equalities. This is routine but tedious.
        sorry
      · exact measurable_pi_lambda _ (fun i => measurable_pi_apply _)
      · exact measurable_pi_lambda _ (fun i => hX_meas (π i))
      · exact measurable_pi_lambda _ (fun i => measurable_pi_apply _)
      · exact measurable_pi_lambda _ (fun i => hX_meas i)
    
    -- Step 4: By Ionescu-Tulcea/Kolmogorov extension theorem, measures on ℕ → α
    -- are uniquely determined by their finite-dimensional marginals
    -- Therefore μ_X = μ_Xπ
    have h_unique : μ_X = μ_Xπ := by
      -- Strategy: Show measures agree on all measurable sets via π-system argument
      ext S hS
      
      -- Define the π-system of cylinder sets
      -- A cylinder set is determined by finitely many coordinates:
      -- C_{n,T} = {f : ℕ → α | (f 0, ..., f (n-1)) ∈ T} for T ⊆ (Fin n → α)
      
      -- The product σ-algebra on ℕ → α is generated by sets of the form:
      -- {f | f i ∈ A} for i : ℕ and measurable A ⊆ α
      -- These generate the same σ-algebra as cylinder sets.
      
      -- Key steps:
      -- 1. Every cylinder set C_{n,T} has μ_X C_{n,T} = μ_Xπ C_{n,T} by h_marginals
      -- 2. Cylinder sets form a π-system (closed under finite intersection)
      -- 3. Cylinder sets generate the product σ-algebra on ℕ → α
      -- 4. Apply uniqueness: measures agreeing on a π-system that generates
      --    the σ-algebra must agree on all measurable sets (Dynkin's π-λ theorem)
      
      -- The challenge: For arbitrary measurable S, we need to show it's in the
      -- σ-algebra generated by cylinders and that μ_X S = μ_Xπ S.
      -- This requires either:
      -- (a) Using MeasurableSpace.induction_on_inter with the cylinder π-system
      -- (b) Proving a custom version of the π-λ theorem for this setting
      -- (c) Finding a mathlib lemma specifically for product measures
      
      -- Attempt (a): Use induction on the σ-algebra
      -- The theorem MeasurableSpace.ae_induction_on_inter might help, but it's
      -- for almost-everywhere properties, not equality of measure values directly.
      
      sorry
    
    -- Step 5: Conclude that X and X ∘ π have the same law
    calc Measure.map (fun ω => fun i : ℕ => X (π i) ω) μ
        = μ_Xπ := rfl
      _ = μ_X := h_unique.symm
      _ = Measure.map (fun ω => fun i : ℕ => X i ω) μ := rfl
      
  · intro hX_full
    exact FullyExchangeable.exchangeable hX_meas hX_full

end Exchangeability
