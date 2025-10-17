# Martingale Convergence Theorem Implementation Notes

## Current Status

### Axioms in `Exchangeability/Probability/Martingale.lean`

Two axioms currently exist that need to be replaced with proven lemmas:

1. **`condExp_tendsto_iSup`** (lines 210-219) - Lévy's upward theorem
2. **`condExp_tendsto_iInf`** (lines 183-192) - Lévy's downward theorem

### Usage in Codebase

**`condExp_tendsto_iInf` (downward/reverse):**
- `ViaMartingale.lean:2051` - Main convergence for `indProd X r C` to tail σ-algebra
- `ViaMartingale.lean:2350` - Convergence for indicator functions of `X 0`

**`condExp_tendsto_iSup` (upward/forward):**
- `ViaMartingale.lean:1777-1779` - TODO comment with `sorry` for upward convergence

---

## Replacement Plan

### 1. Replace `condExp_tendsto_iSup` (EASY - Direct mathlib wrapper)

Mathlib already provides this via `MeasureTheory.tendsto_ae_condExp` in `Mathlib.Probability.Martingale.Convergence`.

**Implementation:**
```lean
import Mathlib.Probability.Martingale.Convergence

theorem condExp_tendsto_iSup
    [IsProbabilityMeasure μ]
    {𝔽 : ℕ → MeasurableSpace Ω}
    (h_filtration : Monotone 𝔽)
    (h_le : ∀ n, 𝔽 n ≤ m0)
    (f : Ω → ℝ) (h_f_int : Integrable f μ) :
    ∀ᵐ ω ∂μ, Tendsto (fun n => μ[f | 𝔽 n] ω) atTop (𝓝 (μ[f | ⨆ n, 𝔽 n] ω)) := by
  classical
  -- Package 𝔽 as a Filtration
  let ℱ : Filtration ℕ m0 :=
    { seq  := 𝔽
      mono := h_filtration
      le   := h_le }
  -- Apply mathlib's Lévy upward theorem
  simpa using (MeasureTheory.tendsto_ae_condExp (μ := μ) (ℱ := ℱ) f)
```

**Key insight:** Just package the monotone family as a `Filtration` and forward to mathlib.

---

### 2. Replace `condExp_tendsto_iInf` (MODERATE - Requires lattice work)

Mathlib does NOT have a direct "reverse martingale" or "decreasing filtration" convergence theorem packaged. However, we can prove it using existing building blocks.

**Mathematical Strategy:**

For a decreasing filtration `𝔽 n` (i.e., `𝔽 (n+1) ≤ 𝔽 n`):

1. **Define limit σ-algebra:** `F_∞ := ⨅ n, 𝔽 n`
2. **Define target:** `g := μ[f | F_∞]`
3. **Key observation:** By tower property, since `F_∞ ≤ 𝔽 n` for all `n`:
   ```
   μ[f | 𝔽 n] = μ[μ[f | F_∞] | 𝔽 n] = μ[g | 𝔽 n]   a.e.
   ```
4. **Build increasing filtration:** Define `G_k := ⨆_{n ≤ k} 𝔽 n`
   - This is *increasing* in `k`
   - Since `𝔽` is *decreasing*, `G_k = 𝔽 k` (the supremum is just the largest element)
5. **Apply upward theorem:** Use mathlib's upward theorem on `g` with filtration `G`:
   ```
   μ[g | G_k] → μ[g | ⨆_k G_k]   a.e.
   ```
6. **Identify pieces:**
   - `μ[g | G_k] = μ[g | 𝔽 k] = μ[f | 𝔽 k]` (by tower)
   - `⨆_k G_k = F_∞` (in a decreasing chain)
   - `μ[g | F_∞] = g = μ[f | F_∞]` (by definition)

**Implementation outline:**
```lean
theorem condExp_tendsto_iInf
    [IsProbabilityMeasure μ]
    {𝔽 : ℕ → MeasurableSpace Ω}
    (h_filtration : Antitone 𝔽)           -- decreasing
    (h_le : ∀ n, 𝔽 n ≤ m0)
    (f : Ω → ℝ) (h_f_int : Integrable f μ) :
    ∀ᵐ ω ∂μ, Tendsto (fun n => μ[f | 𝔽 n] ω) atTop (𝓝 (μ[f | ⨅ n, 𝔽 n] ω)) := by
  classical

  -- Step 1: Define limit σ-algebra and target
  let Finf : MeasurableSpace Ω := ⨅ n, 𝔽 n
  let g : Ω → ℝ := μ[f | Finf]

  -- Step 2: Build increasing filtration G_k := ⨆_{n ≤ k} 𝔽 n
  let G : Filtration ℕ m0 :=
    { seq  := fun k => ⨆ (n : ℕ) (hn : n ≤ k), 𝔽 n
      mono := by
        intro k ℓ hkℓ
        refine iSup₂_mono ?_ ?_
        · intro n; intro hn; exact le_rfl
        · intro n; intro hn; exact hn.trans hkℓ
      le   := by intro k; exact iSup₂_le fun n _ => h_le n }

  -- Step 3: Key lattice fact - in decreasing chain, finite supremum = largest element
  have Gi_eq : ∀ k, (⨆ (n : ℕ) (hn : n ≤ k), 𝔽 n) = 𝔽 k := by
    intro k
    -- Since 𝔽 is antitone, 𝔽 k is the largest among {𝔽 n | n ≤ k}
    sorry  -- lattice algebra

  -- Step 4: Apply Lévy upward theorem to g
  have h_up : ∀ᵐ ω ∂μ,
      Tendsto (fun k => μ[g | ↑G k] ω) atTop (𝓝 (μ[g | ⨆ k, ↑G k] ω)) :=
    MeasureTheory.tendsto_ae_condExp (μ := μ) (ℱ := G) g

  -- Step 5: Identify μ[g | G_k] = μ[f | 𝔽 k] via tower property
  have h_condexp_ident :
      (fun k ω => μ[g | ↑G k] ω) = fun k ω => μ[f | 𝔽 k] ω := by
    funext k; funext ω
    have hFinf_le : Finf ≤ 𝔽 k := iInf_le (fun n => 𝔽 n) k
    -- Tower: μ[μ[f|Finf] | 𝔽 k] = μ[f | 𝔽 k]
    have := condExp_condExp_of_le (μ := μ) (m := Finf) (hm := hFinf_le) (f := f)
    have : μ[g | ↑G k] = μ[g | 𝔽 k] := by simpa [g, Gi_eq k]
    simpa [g] using this

  -- Step 6: Identify ⨆ k G_k = Finf in decreasing chain
  have h_suprG : (⨆ k, (↑G k : MeasurableSpace Ω)) = Finf := by
    sorry  -- lattice algebra

  -- Conclude
  refine h_up.mono ?_
  intro ω hω
  simpa [h_condexp_ident, h_suprG, g]
```

**Missing pieces (lattice algebra):**

1. **`Gi_eq`:** Prove that `⨆_{n ≤ k} 𝔽 n = 𝔽 k` when `𝔽` is antitone
   - Need: In a decreasing chain, the supremum of a prefix is the first element

2. **`h_suprG`:** Prove that `⨆ k (⨆_{n ≤ k} 𝔽 n) = ⨅ n 𝔽 n`
   - When `𝔽` is decreasing: `⨆ k 𝔽 k = 𝔽 0` and `⨅ k 𝔽 k` is tail
   - Need careful lattice manipulation

---

## Mathlib References

### Already Available

- **`MeasureTheory.tendsto_ae_condExp`**: Upward Lévy theorem
  - Location: `Mathlib.Probability.Martingale.Convergence`
  - [Docs](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Probability/Martingale/Convergence.html)

- **`MeasureTheory.condExp_condExp_of_le`**: Tower property for conditional expectation
  - Location: `Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic`

- **`Filtration`**: Structure for packaging σ-algebra filtrations
  - Location: `Mathlib.Probability.Process.Filtration`
  - [Docs](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Probability/Process/Filtration.html)

### Not Yet Available

- Direct "reverse martingale" or "downward Lévy" theorem for decreasing filtrations
- Need to construct from available pieces as shown above

---

## Implementation Checklist

- [ ] Add import: `Mathlib.Probability.Martingale.Convergence`
- [ ] Implement `condExp_tendsto_iSup` (upward) - easy wrapper
- [ ] Prove lattice helper: `iSup_prefix_of_antitone` for `Gi_eq`
- [ ] Prove lattice helper: `iSup_of_antitone_eq_iInf` for `h_suprG`
- [ ] Implement `condExp_tendsto_iInf` (downward) using construction above
- [ ] Test on call sites in `ViaMartingale.lean`
- [ ] Remove old axioms from `Martingale.lean`
- [ ] Update documentation

---

## Related Axioms (Currently in Martingale.lean)

The file also contains more general reverse martingale axioms that the `condExp_tendsto_*` lemmas are built from:

- `reverseMartingaleLimit` (line 74)
- `reverseMartingaleLimit_measurable` (line 88)
- `reverseMartingaleLimit_eq` (line 102)
- `reverseMartingale_convergence_ae` (line 120)
- `reverseMartingaleLimitNat` (line 134)
- `reverseMartingaleLimitNat_eq` (line 147)
- `reverseMartingaleNat_convergence` (line 160)

**Note:** Once `condExp_tendsto_iInf` is proven, these more general axioms become **derivable** from the conditional expectation case (since conditional expectations form a reverse martingale). We could potentially prove these as well, eliminating all axioms in the file.

---

## Design Decision

Should we:

1. **Minimal approach:** Just replace the two `condExp_tendsto_*` axioms (sufficient for de Finetti)
2. **Complete approach:** Also derive the general `reverseMartingale*` axioms from the conditional expectation cases

Recommend: Start with minimal approach (option 1), since that's what's actively blocking the proofs.
