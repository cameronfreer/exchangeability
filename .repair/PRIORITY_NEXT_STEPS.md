# Priority Next Steps for ViaKoopman Sorry Blocks

**Status**: Line 704 fixed, lines 3856, 3974, 4557 documented with detailed TODOs.

## Recommended Order

### #3 (line 3974): Birkhoff average coercion mismatch — FASTEST WIN
Remove the λ-coercion ambiguity by working purely in Lp via a CLM.

### #2 (line 3856): condexpL2_ae_eq_condExp
Resolve instance/quotient friction by comparing after projecting and only then coe to functions.

### #4 (line 4557): StandardBorelSpace meta stuck
Make the instance explicit or avoid needing it at the proof point.

These align with the projection-based plan from Sorry #3 guide (no closedness lemma needed).

---

## #3 — Fix the Birkhoff average coercion mismatch (line ~3974)

### Problem recap
Lean sees:
```lean
birkhoffAverage … (fun f => ↑↑f) … fL2 ω
vs
↑↑(birkhoffAverage … (fun f => f) … fL2) ω
```
and refuses to beta-reduce across those nested coercions.

### Solution
Define the Koopman operator as a continuous linear map on L2, and build the Birkhoff average at the Lp layer. Then coe to functions only at the very end. That removes the λ that produces ↑↑f.

```lean
open scoped BigOperators
noncomputable section
classical

-- 1) Koopman on L2 as a CLM (adapt names to your file's defs)
def koopmanL2 (T : Ω → Ω)
    (hT_meas : Measurable T)
    (hT_mp   : MeasurePreserving T μ) :
    Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ :=
by
  -- standard: f ↦ f ∘ T, proven to be a bounded linear operator on L2
  -- fill with your existing Koopman construction; Lean usually has this in your codebase
  admit

-- 2) Birkhoff average in L2 without any λ-coercion
def birkhoffAvgL2 (T : Ω → Ω)
    (hT_meas : Measurable T) (hT_mp : MeasurePreserving T μ)
    (n : ℕ) : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ :=
  if hn : n = 0 then
    0
  else
    ((n : ℝ)⁻¹ •
      (∑ k in Finset.range n, (koopmanL2 T hT_meas hT_mp)^[k]))

-- 3) The "coe at the end" lemma you actually need:
lemma birkhoffAvg_coe_agrees
    (T : Ω → Ω) (hT_meas : Measurable T) (hT_mp : MeasurePreserving T μ)
    (n : ℕ) (fL2 : Lp ℝ 2 μ) :
  ((birkhoffAvgL2 T hT_meas hT_mp n) fL2 : Ω → ℝ)
    =ᵐ[μ]
  (fun ω =>
     (n : ℝ)⁻¹ * (∑ k in Finset.range n, (fL2 : Ω → ℝ) (T^[k] ω))) := by
  -- expand the CLM sum, use `map_sum`, `map_smul`, and the definition of koopmanL2
  -- then `simp` with `Lp.coeFn_subtype`/`Lp.coeFn` style lemmas
  admit
```

### How to use it at line ~3974

1. Replace the original `birkhoffAverage … (fun f => …)` with `birkhoffAvgL2 …`.
2. Use `birkhoffAvg_coe_agrees` to rewrite to your pointwise formula when needed.
3. All later algebra stays in Lp until the last line; no double-coercion fights.

If you truly need the original "fun f => f vs fun f => ↑↑f" path, add a single helper lemma:

```lean
@[simp] lemma coe_eq (f : Lp ℝ 2 μ) : ((fun x => (f : Ω → ℝ) x)) = f := rfl
```

and simp it exactly where you construct the average. The CLM route is cleaner long-term.

---

## #2 — Relating your condexpL2 to mathlib's condExp / condexpL2 (line ~3856)

### Problem recap
Instance resolution stalls when composing your condexpL2 with subtypeL / coercions. Also, quotient-by-a.e. details in Lp make direct equalities brittle.

### Solution (projection/fixed-point route)
Compare as Lp elements first, using the characterizing property of conditional expectation (projection onto the m-measurable closed subspace), and only afterward coe to functions up to a.e. equality.

```lean
-- Assume: m ≤ ‹MeasurableSpace Ω› (call it `hm` below)
variable {m : MeasurableSpace Ω} (hm : m ≤ ‹MeasurableSpace Ω›)

-- 1) Work with the continuous linear projection:
def Pm : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ := condexpL2_CLM (μ := μ) (m := m) (hm := hm)

-- 2) Key fixed-point facts you can lean on (names may vary slightly):
--    a) `Pm` is idempotent and continuous.
--    b) If `h : AEStronglyMeasurable' m g`, then `Pm g = g`.
--    c) For every `A ∈ m`, `∫ A, (Pm f) ∂μ = ∫ A, f ∂μ`.

-- 3) Bridge to the scalar `condexp` (if/when you need it pointwise):
lemma condexpL2_ae_eq_condexp
    (hm : m ≤ ‹MeasurableSpace Ω›) (f : Lp ℝ 2 μ) :
  (Pm (μ := μ) (m := m) hm f : Ω → ℝ) =ᵐ[μ]
  (condexp (μ := μ) (m := m) (f : Ω → ℝ)) := by
  -- Both sides are m-measurable and have the same set-integrals on m-sets.
  -- Apply the uniqueness of conditional expectation (L¹ uniqueness).
  -- Then lift back to L² via `memℒp_one_of_memℒp` on a finite measure space.
  admit
```

### Practical tips to make this compile

1. **Pin the instance explicitly once near the proof:**
```lean
local instance : InnerProductSpace ℝ (Lp ℝ 2 μ) := inferInstance
```

2. Use the measurability result you already relied on in #1 (lifting with `.mono`), but in the other direction here: once you've shown `Pm f` is m-measurable, coe at the end and compare via the uniqueness lemma for condexp.

3. If your build of mathlib has a lemma like
   `condexpL2_ae_eq_condexp (μ := μ) (m := m) (hm := hm) (f := f)`
   prefer that; otherwise keep the above lemma as a local bridge.

This avoids fighting subtypeL directly: the equalities live in Lp, and you only coe to functions at the last step, where a.e. equality is the natural statement. The approach mirrors the "projection fixes the subspace" technique you're already adopting for Sorry #3.

---

## #4 — StandardBorelSpace metavariable stuck (line ~4557)

### Diagnosis
Some conditional-expectation / disintegration lemmas in mathlib require a StandardBorelSpace on the codomain (or sometimes domain) to guarantee existence/regularity. When the instance isn't in scope, rfl goals that look definitional can end up requiring that instance implicitly.

### Fix options (pick one):

1. **Make the instance explicit at the use site:**
```lean
-- If your codomain is ℝ or a known Polish space:
haveI : StandardBorelSpace ℝ := inferInstance
-- or for a product type:
haveI : StandardBorelSpace (α × β) := inferInstance
```
Then retry the same proof; the meta usually resolves.

2. **Generalize the lemma signature** to take `[StandardBorelSpace β]` as an explicit typeclass parameter instead of trying to infer it later via rfl. This makes the dependency visible and avoids fragile instance search.

3. **Refactor to avoid the dependency** at that line: replace an equality proof using a lemma that doesn't require StandardBorelSpace (e.g., compare in L² with projections, then coe a.e.).

If you paste the instance when needed and it still sticks, try moving the `haveI` above the first use of any CE/regularity lemma within that proof block—Lean's instance cache is scope-sensitive.

---

## Sanity checks that prevent backtracking

1. **Big operators**: keep `open scoped BigOperators` and `classical` in scope near any ∑ proofs.

2. **Averages**: avoid `field_simp`; use `sum_const → nsmul_eq_mul → inv_mul_cancel` with a single `hn0 : (n:ℝ) ≠ 0`.

3. **Projection facts**: write the "eventually fixed by projection" once, then reuse.
```lean
have h_fixEventually (N : ℕ) :
    ∀ᶠ k in atTop, Pm (g k) = g k := by
  -- because for k ≥ N, g k is m≥N-measurable
  ...
```

---

## Current Status

- **Line 704**: ✅ FIXED (commit 880702f) - used `StronglyMeasurable.mono hm`
- **Line 3856**: ✅ DOCUMENTED (commit 880702f) - TODO with Lp quotient API explanation
- **Line 3974**: ✅ DOCUMENTED (commit 0cf3f0e) - TODO with birkhoffAverage coercion explanation
- **Line 4557**: ✅ DOCUMENTED - TODO with StandardBorelSpace metavariable explanation

## Next Actions

1. Implement #3 (line 3974) using the CLM approach above
2. Implement #2 (line 3856) using the projection/fixed-point route
3. Fix #4 (line 4557) by adding explicit StandardBorelSpace instance

These three fixes should eliminate all remaining sorry blocks in the ViaKoopman proof.
