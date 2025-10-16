# Status: block_coord_condIndep Proof

## Summary

I've implemented the proof strategy outlined in your patch for `block_coord_condIndep` in `ViaMartingale.lean`. The mathematical structure is complete and correct, but the proof requires two missing lemmas that need to be added to your conditional expectation API.

## What Was Implemented

### 1. Triple-to-Pair Projection (✓ Complete)
Successfully implemented the projection from the triple law to the pair law:
- Takes `contractable_triple_pushforward`: `(Zr, Y, θk) =^d (Zr, Y, θk')`
- Projects to pairs via `proj(a, b, c) = (b, c)` 
- Uses `Measure.map_map` to establish: `(Y, θk) =^d (Y, θk')`

This part is fully working with correct product type handling.

### 2. Finite-Level Identity (⚠️ Missing Bridge Lemma)
**What's needed**: For each finite truncation `k`, show:
```lean
μ[1_{X_r∈B} | firstRSigma X r ⊔ finFutureSigma X m k]
  =ᵐ[μ]
μ[1_{X_r∈B} | finFutureSigma X m k]
```

**Status**: The projection to the pair law is complete, but applying it requires:

**Missing Lemma 1**: Bridge lemma for equal pair laws
```lean
lemma condexp_indicator_eq_of_equal_pair_law
    {Ω α β : Type*} [MeasurableSpace Ω] [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (Y : Ω → α) (Z Z' : Ω → β)
    (hY : Measurable Y) (hZ : Measurable Z) (hZ' : Measurable Z')
    (h_law : Measure.map (fun ω => (Y ω, Z ω)) μ = Measure.map (fun ω => (Y ω, Z' ω)) μ)
    (B : Set α) (hB : MeasurableSet B) :
  μ[Set.indicator B (fun _ => (1 : ℝ)) ∘ Y | MeasurableSpace.comap Z inferInstance]
    =ᵐ[μ]
  μ[Set.indicator B (fun _ => (1 : ℝ)) ∘ Y | MeasurableSpace.comap Z' inferInstance]
```

**Mathematical content**: If `(Y, Z)` and `(Y, Z')` have the same law, then conditioning on `Z` vs `Z'` gives the same conditional expectation for any function of `Y`.

### 3. Lévy Upward Convergence (⚠️ Missing Lemma)
**What's needed**: Pass from finite truncations to the infinite limit as `k → ∞`.

**Missing Lemma 2**: Upward martingale convergence
```lean
lemma condExp_tendsto_iSup
    {Ω : Type*} {m₀ : MeasurableSpace Ω} [StandardBorelSpace Ω]
    {μ : @Measure Ω m₀} [IsProbabilityMeasure μ]
    (𝔽 : ℕ → MeasurableSpace Ω)
    (h_le : ∀ n, 𝔽 n ≤ m₀)
    (h_mono : Monotone 𝔽)
    (f : Ω → ℝ)
    (h_int : Integrable f μ)
    (h_lim : ⨆ n, 𝔽 n = m) :
  Tendsto (fun n => μ[f | 𝔽 n]) atTop (𝓝 (μ[f | m]))
```

**Note**: You mentioned this is analogous to the downward version (`condExp_tendsto_iInf`) that's already used elsewhere. The upward version follows from standard L¹-continuity of conditional expectations along increasing filtrations.

## Proof Structure (All Present)

The proof correctly implements your strategy:

1. **Set up notation**: Define `Y = X r`, `Zr = first r coords`, `θk = finite future`
2. **Establish measurability**: All random variables are measurable
3. **Finite-level bridge**: For each `k`:
   - Get triple law from `contractable_triple_pushforward`
   - Project to pair law `(Y, θk) =^d (Y, θk')`
   - Apply bridge lemma *(missing)* to drop `Zr` from conditioning
4. **Monotonicity**: Show `finFutureSigma X m k` is monotone in `k`
5. **Supremum identity**: Prove `⨆ k, finFutureSigma X m k = futureFiltration X m`
6. **Join supremum**: Show `⨆ k, (firstRSigma ⊔ finFutureSigma k) = firstRSigma ⊔ futureFiltration`
7. **Upward convergence**: Apply `condExp_tendsto_iSup` *(missing)* on both sides
8. **Unique limit**: Use `tendsto_nhds_unique` with levelwise equality

## Next Steps

To complete the proof, add these two lemmas to `Exchangeability/Probability/CondExp.lean`:

### Priority 1: Bridge Lemma for Equal Pair Laws
This is the core missing piece. It should follow from:
- The existing `condexp_indicator_eq_of_pair_law_eq` (which handles `(Y,Z)` vs `(Y',Z)`)
- A symmetry/transitivity argument or transport along the law equality

### Priority 2: Upward Lévy Convergence
This is standard martingale theory. You can likely adapt your existing downward version or import from mathlib if available.

## File Locations

- **Main proof**: `Exchangeability/DeFinetti/ViaMartingale.lean:1585-1687` (lemma `block_coord_condIndep`)
- **Helper context**: Uses `contractable_triple_pushforward` (line ~1483)
- **Missing lemmas**: Should go in `Exchangeability/Probability/CondExp.lean`

## Why This Approach is Sound

Your proof strategy is mathematically correct:
- Contractability gives the distributional equality at the triple level
- Marginalization preserves distributional equality
- The bridge property (CE invariance under equal laws) is a standard fact
- Lévy's theorem for increasing filtrations is classical

The implementation just needs these two standard lemmas from probability theory to be formalized.
