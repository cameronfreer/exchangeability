/-
Copyright (c) 2025 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Equiv.Fintype
import Mathlib.GroupTheory.Perm.Basic

/-!
# Permutation Extension for Injective Functions

This file proves that any injective function `k : Fin m → ℕ` with bounded range
can be extended to a permutation of `Fin n`.

## Main Results

* `exists_perm_extending_injective`: Given an injective `k : Fin m → ℕ` with all values `< n`
  and `m ≤ n`, there exists a permutation `σ : Perm (Fin n)` such that `σ(i) = k(i)` for all
  `i < m`.

* `exists_perm_extending_strictMono`: The special case for strictly monotone functions.

## Mathematical Context

This is a key combinatorial lemma in the proof that **exchangeability implies contractability**
for infinite sequences of random variables. The construction allows any injective
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
        exact Nat.succ_le_of_lt (Nat.lt_of_le_of_lt (ih (Nat.lt_of_succ_lt hn))
          (hk (Fin.mk_lt_mk.mpr (Nat.lt_succ_self n))))
  exact this i.val i.isLt

/--
Any injective function can be extended to a permutation.

**Statement:** Given an injective `k : Fin m → ℕ` with all values `< n`
and `m ≤ n`, there exists a permutation `σ : Perm (Fin n)` such that
`σ(i) = k(i)` for all `i < m`.

**Construction outline:**
1. **Domain partition:** `{0,...,m-1}` ∪ `{m,...,n-1}` = `Fin n`
2. **Codomain partition:** `{k(0),...,k(m-1)}` ∪ `complement` = `Fin n`
3. Map first `m` positions to `k`-values: `σ(i) = k(i)` for `i < m`
4. Extend arbitrarily to remaining positions using `Equiv.extendSubtype`

This is the key combinatorial lemma enabling the implication
**exchangeable → contractable**: any injective subsequence can be
realized via a permutation.
-/
theorem exists_perm_extending_injective (k : Fin m → ℕ)
    (hk_inj : Function.Injective k) (hk_bound : ∀ i, k i < n) (hmn : m ≤ n) :
    ∃ (σ : Equiv.Perm (Fin n)), ∀ (i : Fin m),
      (σ ⟨i.val, Nat.lt_of_lt_of_le i.isLt hmn⟩).val = k i := by
  let kFin : Fin m → Fin n := fun i => ⟨k i, hk_bound i⟩
  -- e_dom: first m elements of Fin n ≃ Fin m
  let e_dom : {x : Fin n // (x : ℕ) < m} ≃ Fin m := (Fin.castLEquiv hmn).symm
  -- e_cod: Fin m ≃ range of kFin (via injectivity)
  have hkFin_inj : Function.Injective kFin := fun i j h => hk_inj (Fin.ext_iff.mp h)
  let e_cod' : Fin m ≃ Set.range kFin := Equiv.ofInjective kFin hkFin_inj
  -- Convert between range representation and existential predicate
  let e_cod : Fin m ≃ {x : Fin n // ∃ i : Fin m, x = kFin i} :=
    e_cod'.trans (Equiv.subtypeEquivRight fun x => by simp [Set.mem_range, eq_comm])
  -- Compose and extend to full permutation
  let σ : Equiv.Perm (Fin n) := Equiv.extendSubtype (e_dom.trans e_cod)
  refine ⟨σ, fun i => ?_⟩
  have h := Equiv.extendSubtype_apply_of_mem (e := e_dom.trans e_cod)
    (x := Fin.castLE hmn i) i.isLt
  simp only [Equiv.trans_apply, e_cod, e_cod', Equiv.ofInjective_apply, kFin] at h
  exact congrArg Fin.val h

/-- Any strictly increasing function can be extended to a permutation.

This is a corollary of `exists_perm_extending_injective` since strict monotonicity
implies injectivity. -/
theorem exists_perm_extending_strictMono (k : Fin m → ℕ)
    (hk_mono : StrictMono k) (hk_bound : ∀ i, k i < n) (hmn : m ≤ n) :
    ∃ (σ : Equiv.Perm (Fin n)), ∀ (i : Fin m),
      (σ ⟨i.val, Nat.lt_of_lt_of_le i.isLt hmn⟩).val = k i :=
  exists_perm_extending_injective k hk_mono.injective hk_bound hmn

end Combinatorics
