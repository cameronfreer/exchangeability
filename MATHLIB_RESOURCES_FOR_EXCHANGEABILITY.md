# Mathlib Resources for Proving Exchangeability Axioms

This document outlines the mathlib theorems and constructions that can be used to eliminate the axioms in `Exchangeability.lean`.

## Axiom 1: `measure_eq_of_fin_marginals_eq`

**Goal**: Prove that measures on path space are determined by their finite-dimensional marginals.

### Key Mathlib Theorems

1. **`MeasureTheory.Measure.ext_of_generate_finite`** (`Mathlib/MeasureTheory/Measure/Typeclasses/Finite.lean:445`)
   ```lean
   theorem ext_of_generate_finite (C : Set (Set α)) (hA : m0 = generateFrom C) 
       (hC : IsPiSystem C) [IsFiniteMeasure μ] 
       (hμν : ∀ s ∈ C, μ s = ν s) (h_univ : μ univ = ν univ) : μ = ν
   ```
   - This is the π-λ theorem for finite measures
   - If two finite measures agree on a π-system generating the σ-algebra, they are equal

2. **`MeasureTheory.Constructions.generateFrom_measurableCylinders`** (`Mathlib/MeasureTheory/Constructions/Cylinders.lean:347`)
   ```lean
   theorem generateFrom_measurableCylinders :
       MeasurableSpace.generateFrom (measurableCylinders α) = MeasurableSpace.pi
   ```
   - Cylinder sets generate the product σ-algebra on `∀ i, α i`

3. **`MeasureTheory.Constructions.isPiSystem_measurableCylinders`** (`Mathlib/MeasureTheory/Constructions/Cylinders.lean`)
   - Measurable cylinders form a π-system

4. **`MeasurableSpace.induction_on_inter`** (`Mathlib/MeasureTheory/Measure/PiSystem.lean:674`)
   ```lean
   theorem induction_on_inter {m : MeasurableSpace α} 
       {C : ∀ s : Set α, MeasurableSet s → Prop}
       {s : Set (Set α)} (h_eq : m = generateFrom s) (h_inter : IsPiSystem s)
       ...
   ```
   - Dynkin's π-λ theorem as an induction principle

5. **Ionescu-Tulcea Theorem** (`Mathlib/Probability/Kernel/IonescuTulcea/Traj.lean`)
   - `ProbabilityTheory.Kernel.traj`: constructs infinite product measures from kernels
   - Provides the machinery for defining measures on path space

6. **`MeasureTheory.Measure.infinitePiNat`** (`Mathlib/Probability/ProductMeasure.lean:108`)
   ```lean
   noncomputable def infinitePiNat : Measure (Π n, X n)
   ```
   - Constructs infinite product measures indexed by `ℕ`
   
7. **`MeasureTheory.Measure.isProjectiveLimit_infinitePiNat`** (`Mathlib/Probability/ProductMeasure.lean:204`)
   - Shows that `infinitePiNat` is a projective limit
   - Key for relating infinite products to finite-dimensional marginals

### Proof Strategy

```lean
theorem measure_eq_of_fin_marginals_eq {μ ν : Measure (ℕ → α)}
    (h : ∀ n (S : Set (Fin n → α)) (_hS : MeasurableSet S),
        Measure.map (fun f : ℕ → α => fun i : Fin n => f i) μ S =
        Measure.map (fun f : ℕ → α => fun i : Fin n => f i) ν S) : μ = ν := by
  -- Step 1: Assume μ and ν are finite (or work with probability measures)
  -- This should follow from the structure of the problem
  
  -- Step 2: Use ext_of_generate_finite with C = measurableCylinders
  apply ext_of_generate_finite (measurableCylinders α) 
    generateFrom_measurableCylinders.symm isPiSystem_measurableCylinders
  
  -- Step 3: For each cylinder set s ∈ measurableCylinders:
  -- A cylinder is determined by finitely many coordinates
  intro s hs
  obtain ⟨I, S, hS, rfl⟩ := (mem_measurableCylinders _).mp hs
  
  -- Step 4: Use the hypothesis h to show μ and ν agree on this cylinder
  -- This follows because cylinders are preimages under finite projections
  rw [cylinder_eq_map_preimage, ← h I S hS]
  
  -- Step 5: Check μ univ = ν univ (probability measures have this automatically)
  sorry
```

## Axiom 2: `exchangeable_iff_fullyExchangeable`

**Goal**: Prove that exchangeability is equivalent to full exchangeability.

### Key Mathlib Theorems

1. **`MeasureTheory.Measure.map_apply`** 
   - For measurable functions, `(μ.map f) S = μ (f ⁻¹' S)`
   - Essential for relating push-forward measures

2. **`MeasureTheory.Measure.ext`**
   - Extensionality for measures

3. The proof of `measure_eq_of_fin_marginals_eq` above
   - Once proven, this can be applied to show `μ_X = μ_Xπ`

### Proof Strategy

```lean
theorem exchangeable_iff_fullyExchangeable {μ : Measure Ω} {X : ℕ → Ω → α}
    (hX_meas : ∀ i, Measurable (X i)) : 
    Exchangeable μ X ↔ FullyExchangeable μ X := by
  constructor
  · intro h_exch π
    -- Define path-space measures
    let μ_X : Measure (ℕ → α) := μ.map (fun ω n => X n ω)
    let μ_Xπ : Measure (ℕ → α) := μ.map (fun ω n => X (π n) ω)
    
    -- Step 1: Show finite-dimensional marginals of μ_X and μ_Xπ agree
    -- This uses the exchangeability assumption
    have h_marginals : ∀ n (S : Set (Fin n → α)) (hS : MeasurableSet S),
        Measure.map (fun f : ℕ → α => fun i : Fin n => f i) μ_X S =
        Measure.map (fun f : ℕ → α => fun i : Fin n => f i) μ_Xπ S := by
      intro n S hS
      -- Use exchangeability: the law of (X 0, ..., X (n-1)) equals 
      -- the law of (X (π 0), ..., X (π (n-1)))
      sorry
    
    -- Step 2: Apply measure_eq_of_fin_marginals_eq
    have : μ_X = μ_Xπ := measure_eq_of_fin_marginals_eq h_marginals
    
    -- Step 3: Evaluate at coordinate sets to conclude
    intro i S hS
    calc μ (X i ⁻¹' S)
        = μ_X ((eval i) ⁻¹' S) := by rw [Measure.map_apply]
      _ = μ_Xπ ((eval i) ⁻¹' S) := by rw [this]
      _ = μ (X (π i) ⁻¹' S) := by rw [Measure.map_apply]
  
  · intro h_full
    -- Reverse direction: full exchangeability trivially implies exchangeability
    sorry
```

## Additional Useful Theorems

### Permutations and Equivalences

1. **`Equiv.Perm`** (`Mathlib/Logic/Equiv/Defs.lean:92`)
   ```lean
   abbrev Equiv.Perm (α : Sort*) := Equiv α α
   ```
   - Type of bijections from `α` to itself (permutations)

2. **`Equiv.piCongrLeft`** (`Mathlib/Data/Set/Prod.lean` and many other files)
   ```lean
   def piCongrLeft {ι ι' : Type*} (α : ι' → Type*) (e : ι' ≃ ι) :
       (Π i, α (e i)) ≃ Π i, α i
   ```
   - Transport dependent functions through an equivalence of the base space
   - Essential for reindexing products under permutations

3. **`Equiv.piCongrLeft_preimage_pi`** (`Mathlib/Data/Set/Prod.lean:885`)
   ```lean
   theorem piCongrLeft_preimage_pi (f : ι' ≃ ι) (s : Set ι') (t : ∀ i, Set (α i)) :
       f.piCongrLeft α ⁻¹' (f '' s).pi t = s.pi fun i => t (f i)
   ```
   - Key for relating preimages under reindexing

4. **`MeasureTheory.MeasurableEquiv`** 
   - Measurable equivalences preserve measure-theoretic properties
   - Many versions: `integral_map_equiv`, `lintegral_map_equiv`, `integrableOn_map_equiv`

5. **`MeasureTheory.Measure.map`** with equivalences
   - `integral_map_equiv`: `∫ y, f y ∂Measure.map e μ = ∫ x, f (e x) ∂μ`
   - `lintegral_map_equiv`: The same for Lebesgue integrals
   - Essential for push-forward measures under permutations

### Projective Limits

- **`MeasureTheory.Constructions.Projective.unique`** (`Mathlib/MeasureTheory/Constructions/Projective.lean:153`)
  ```lean
  theorem unique [Nonempty (∀ i, α i)] (hμ : IsProjectiveLimit μ P) 
      (hν : IsProjectiveLimit ν P) : μ = ν
  ```
  - Uniqueness of projective limits
  - Shows that a measure is uniquely determined by its projective system

### Cylinder Sets

- **`MeasureTheory.Constructions.cylinder`** (`Mathlib/MeasureTheory/Constructions/Cylinders.lean:151`)
  - Definition of cylinder sets
  - Preimages under finite projections

- **`MeasureTheory.Constructions.mem_cylinder`** 
  - Characterization of membership in cylinders

### π-systems and Dynkin Systems

- **`MeasurableSpace.generateFrom_le_iff`**
  - For checking inclusions of generated σ-algebras

- **`MeasureTheory.induction_on_inter`**
  - The main induction principle from Dynkin's theorem

## Implementation Notes

1. **Probability vs. Finite Measures**: Most theorems work for finite measures. For probability measures, conditions like `μ univ = ν univ` are automatic.

2. **Measurability**: Careful tracking of measurability is crucial. The compositions of projections and the functions `X` must all be measurable.

3. **Classical Logic**: Some constructions (like Ionescu-Tulcea) may use classical logic and choice principles.

4. **Type Theory Considerations**: Lean's dependent type theory requires careful handling of the index types (e.g., `Fin n` vs `ℕ` vs general `ι`).

## Next Steps

1. Start with `measure_eq_of_fin_marginals_eq` as it's more self-contained
2. The key challenge is properly connecting cylinders to finite-dimensional marginals
3. Once the first axiom is proven, the second should follow relatively quickly
4. Consider creating intermediate lemmas about:
   - Relating `Measure.map` with projections
   - Properties of cylinder sets and their measures
   - Finite permutations and their action on measures
