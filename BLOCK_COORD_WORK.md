# Working Notes: block_coord_condIndep Proof Strategy

**Goal:** Prove `block_coord_condIndep` from contractability

**Mathematical Statement** (Kallenberg Lemma 1.3 application):
```
σ(X₀,...,X_{r-1}) ⊥⊥_{σ(θ_{m+1} X)} σ(X_r)   when r < m
```

## Kallenberg's Proof Sketch (from page 25-26)

**Lemma 1.3 (Contraction-Independence):**
If (U, η) =ᵈ (U, ζ) and σ(η) ⊆ σ(ζ), then U ⊥⊥_η ζ.

**Proof of Lemma 1.3 (L² argument):**
1. For any measurable B and bounded σ(η)-measurable h:
   ```
   E[1_{U∈B} · h] = E[E[1_{U∈B} | η] · h]    (tower property)
                   = E[E[1_{U∈B} | ζ] · h]    (by distributional equality)
   ```
2. This shows E[1_{U∈B} | η] = E[1_{U∈B} | ζ] a.s. (uniqueness of CE)
3. Since σ(η) ⊆ σ(ζ), this means E[1_{U∈B} | ζ] is σ(η)-measurable
4. By definition: U ⊥⊥_η ζ

**Application to block_coord_condIndep:**
- Set U = firstRBlock X r = (X₀,...,X_{r-1})
- Set η = θ_{m+1} X (future after position m)
- Set ζ = (X_r, θ_{m+1} X) (coordinate r + future)

**From contractability with r < m:**
```
(X₀,...,X_{r-1}, θ_{m+1} X) =ᵈ (X₀,...,X_{r-1}, X_r, θ_{m+1} X)
```
This is because deleting coordinate r (which is < m) doesn't change the distribution
of (X₀,...,X_{r-1}) paired with the future θ_{m+1} X.

**Applying Lemma 1.3:**
- (U, η) =ᵈ (U, ζ) ✓
- σ(η) ⊆ σ(ζ) ✓  (since ζ = (X_r, η))
- Therefore: U ⊥⊥_η ζ
- Which means: firstRBlock X r ⊥⊥_{θ_{m+1} X} (X_r, θ_{m+1} X)

**Extracting X_r independence:**
If U ⊥⊥_η (X_r, η), then U ⊥⊥_η X_r by monotonicity:
- σ(X_r) ⊆ σ(X_r, η)
- Conditional independence with respect to a larger σ-algebra implies independence
  with respect to any sub-σ-algebra

## Implementation Strategy

### Step 1: Prove Lemma 1.3 (contraction_independence)
**Signature:**
```lean
lemma contraction_independence
    {Ω α β : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (U : Ω → α) (η : Ω → β) (ζ : Ω → β × β)  -- ζ packages (X_r, η)
    (hU : Measurable U) (hη : Measurable η) (hζ : Measurable ζ)
    (hdist : Measure.map (fun ω => (U ω, η ω)) μ
           = Measure.map (fun ω => (U ω, Prod.fst (ζ ω))) μ)
    (hsub : MeasurableSpace.comap η inferInstance
         ≤ MeasurableSpace.comap ζ inferInstance) :
    ProbabilityTheory.CondIndep
      (MeasurableSpace.comap η inferInstance)  -- conditioning σ-algebra
      (MeasurableSpace.comap U inferInstance)  -- U's σ-algebra
      (MeasurableSpace.comap ζ inferInstance)  -- ζ's σ-algebra
      _ μ
```

**Proof approach:**
- Use `condIndep_of_indicator_condexp_eq` from CondExp.lean
- Show projection property: for all H ∈ σ(ζ),
  ```
  μ[H.indicator | σ(U) ⊔ σ(η)] =ᵐ[μ] μ[H.indicator | σ(η)]
  ```
- The key is using the distributional equality to show conditional expectations match

### Step 2: Extract distributional equality from contractability
**Helper lemma:**
```lean
lemma firstRBlock_future_dist_eq_of_contractable
    {Ω α : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [MeasurableSpace α]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ℕ → Ω → α)
    (hX : Contractable μ X)
    (hX_meas : ∀ n, Measurable (X n))
    {r m : ℕ} (hrm : r < m) :
    Measure.map (fun ω => (firstRBlock X r ω, shiftRV X (m+1) ω)) μ
      = Measure.map (fun ω => (firstRBlock X r ω, X r ω, shiftRV X (m+1) ω)) μ
```

Where `firstRBlock X r` is the function that extracts (X₀,...,X_{r-1}).

**Proof:** Direct from definition of contractability - deleting coordinate r when r < m
doesn't change distribution of remaining coordinates.

### Step 3: Apply contraction_independence to block_coord_condIndep
Package everything together:
- U = firstRBlock X r (as function Ω → Fin r → α)
- η = shiftRV X (m+1) (as function Ω → ℕ → α)
- ζ packages (X r, shiftRV X (m+1))
- Get distributional equality from Step 2
- Apply Lemma 1.3 from Step 1
- Use monotonicity to extract σ(X r) from σ(X r, θ_{m+1} X)

## Technical Challenges

1. **Type packaging:** Need to carefully package (X_r, θ_{m+1} X) as a single measurable function
2. **σ-algebra matching:** Ensure firstRSigma X r matches MeasurableSpace.comap (firstRBlock X r)
3. **Monotonicity lemma:** Need lemma that CondIndep m mF (mH ⊔ m) implies CondIndep m mF mH

## Alternative: Direct Proof Without Lemma 1.3

Could potentially prove block_coord_condIndep directly using the projection property pattern,
bypassing the abstract Lemma 1.3. This might be simpler for the specific structure we have.

**Direct approach:**
For any H ∈ σ(X r), show:
```
μ[H.indicator | firstRSigma X r ⊔ futureFiltration X m]
  =ᵐ[μ]
μ[H.indicator | futureFiltration X m]
```

Use the distributional equality from contractability to show these conditional expectations
must be equal by uniqueness.

---

**Status:** Ready to implement Step 1 (Lemma 1.3) or pursue direct approach
**Next:** Create skeleton proof with sorry placeholders
