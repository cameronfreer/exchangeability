/-
Copyright (c) 2025 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.Logic.Equiv.Fintype
import Mathlib.GroupTheory.Perm.Basic

/-!
# Permutation Extension for Strictly Monotone Functions

This file proves that any strictly increasing function `k : Fin m → ℕ` with bounded range
can be extended to a permutation of `Fin n`.

## Main Results

* `exists_perm_extending_strictMono`: Given a strictly increasing `k : Fin m → ℕ` with all
  values `< n` and `m ≤ n`, there exists a permutation `σ : Perm (Fin n)` such that
  `σ(i) = k(i)` for all `i < m`.

## Mathematical Context

This is a key combinatorial lemma in the proof that **exchangeability implies contractability**
for infinite sequences of random variables. The construction allows any strictly increasing
subsequence to be realized as the image of the first m coordinates under some permutation.

**Intuition:** We partition both domain and codomain:
- Domain: `{0,...,m-1}` ∪ `{m,...,n-1}` = `Fin n`
- Codomain: `{k(0),...,k(m-1)}` ∪ complement = `Fin n`

Map first `m` positions to `k`-values, then extend arbitrarily to remaining positions
using `Equiv.extendSubtype`.

## Suggested Mathlib Location

`Mathlib.GroupTheory.Perm.Fintype` or `Mathlib.Combinatorics.Subseq`

## References

* Kallenberg (2005), *Probabilistic Symmetries and Invariance Principles*, Theorem 1.1
-/

namespace Combinatorics

variable {m n : ℕ}

/-- For strictly monotone `k : Fin m → ℕ`, values dominate indices: `i ≤ k(i)` for all `i`. -/
lemma strictMono_Fin_ge_id {k : Fin m → ℕ} (hk : StrictMono k) (i : Fin m) :
    i.val ≤ k i := by
  -- Proof by strong induction on i.val
  have : ∀ n (hn : n < m), n ≤ k ⟨n, hn⟩ := by
    intro n
    induction n with
    | zero => intro _; exact Nat.zero_le _
    | succ n ih =>
        intro hn
        have hn' : n < m := Nat.lt_of_succ_lt hn
        let j : Fin m := ⟨n, hn'⟩
        let j_succ : Fin m := ⟨n.succ, hn⟩
        have hlt : j < j_succ := by simp [Fin.lt_def, j, j_succ]
        have hk_lt : k j < k j_succ := hk hlt
        have ih' : n ≤ k j := ih hn'
        calc n.succ
            = n + 1 := rfl
          _ ≤ k j + 1 := Nat.add_le_add_right ih' 1
          _ ≤ k j_succ := Nat.succ_le_of_lt hk_lt
  exact this i.val i.isLt

/--
Any strictly increasing function can be extended to a permutation.

**Statement:** Given a strictly increasing `k : Fin m → ℕ` with all values `< n`
and `m ≤ n`, there exists a permutation `σ : Perm (Fin n)` such that
`σ(i) = k(i)` for all `i < m`.

**Construction outline:**
1. **Domain partition:** `{0,...,m-1}` ∪ `{m,...,n-1}` = `Fin n`
2. **Codomain partition:** `{k(0),...,k(m-1)}` ∪ `complement` = `Fin n`
3. Map first `m` positions to `k`-values: `σ(i) = k(i)` for `i < m`
4. Extend arbitrarily to remaining positions using `Equiv.extendSubtype`

This is the key combinatorial lemma enabling the implication
**exchangeable → contractable**: any strictly increasing subsequence can be
realized via a permutation.
-/
theorem exists_perm_extending_strictMono (k : Fin m → ℕ)
    (hk_mono : StrictMono k) (hk_bound : ∀ i, k i < n) (hmn : m ≤ n) :
    ∃ (σ : Equiv.Perm (Fin n)), ∀ (i : Fin m),
      (σ ⟨i.val, Nat.lt_of_lt_of_le i.isLt hmn⟩).val = k i := by
  classical
  -- Embed `Fin m` into `Fin n` via the initial segment.
  let ι : Fin m → Fin n := fun i => ⟨i.val, Nat.lt_of_lt_of_le i.isLt hmn⟩
  let p : Fin n → Prop := fun x => x.val < m
  let q : Fin n → Prop := fun x => ∃ i : Fin m, x = ⟨k i, hk_bound i⟩
  have hι_mem : ∀ i : Fin m, p (ι i) := fun i => i.isLt
  let kFin : Fin m → Fin n := fun i => ⟨k i, hk_bound i⟩
  have hk_mem : ∀ i : Fin m, q (kFin i) := fun i => ⟨i, rfl⟩
  haveI : DecidablePred p := fun _ => inferInstance
  haveI : DecidablePred q := fun _ => inferInstance
  -- Equivalence between the first `m` coordinates and `Fin m`.
  let e_dom : {x : Fin n // p x} ≃ Fin m :=
    { toFun := fun x => ⟨x.1.val, x.2⟩
    , invFun := fun i => ⟨ι i, by dsimp [p, ι]; exact i.isLt⟩
    , left_inv := by rintro ⟨x, hx⟩; ext; simp [ι]
    , right_inv := by intro i; cases i with | mk i hi => simp [ι] }
  -- Equivalence between the image of `k` and `Fin m`.
  -- For injectivity of k, we use that it's strictly monotone
  have hk_inj : Function.Injective kFin :=
    fun i j hij => hk_mono.injective (Fin.ext_iff.mp hij)
  let e_cod : Fin m ≃ {x : Fin n // q x} :=
    { toFun := fun i => ⟨kFin i, hk_mem i⟩
    , invFun := fun y => Classical.choose y.2
    , left_inv := by
        intro i
        have h_spec := Classical.choose_spec (hk_mem i)
        have : k (Classical.choose (hk_mem i)) = k i := by
          simpa [kFin] using (Fin.ext_iff.mp h_spec).symm
        exact hk_mono.injective this
    , right_inv := by
        rintro ⟨y, hy⟩
        apply Subtype.ext
        simp only [kFin]
        exact (Classical.choose_spec hy).symm }
  -- Equivalence between the subtypes describing the first `m` coordinates and the image of `k`.
  let e : {x : Fin n // p x} ≃ {x : Fin n // q x} := e_dom.trans e_cod
  -- Extend this equivalence to a permutation of `Fin n`.
  let σ : Equiv.Perm (Fin n) := Equiv.extendSubtype e
  have hσ_apply : ∀ i : Fin m, σ (ι i) = kFin i := by
    intro i
    have h_apply := Equiv.extendSubtype_apply_of_mem (e := e) (x := ι i) (hι_mem i)
    dsimp [σ, e, Equiv.trans, e_dom, e_cod, ι, Fin.castLEEmb, kFin] at h_apply
    simpa using h_apply
  refine ⟨σ, fun i => ?_⟩
  have hσ_val : (σ (ι i)).val = k i := by simpa [kFin] using congrArg Fin.val (hσ_apply i)
  simpa [ι] using hσ_val

end Combinatorics
