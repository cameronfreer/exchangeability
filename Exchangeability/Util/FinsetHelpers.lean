/-
Copyright (c) 2025 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card

/-!
# Finset Helper Lemmas

General-purpose lemmas about Finsets and Fin types.

## Main Results

* `Finset.filter_val_lt_card`: Cardinality of filtered Fin elements by value bound
-/

namespace Finset

/-- **Cardinality of filtered Fin elements.**

For `m ≥ n`, the number of elements `i : Fin m` with `i.val < n` is exactly `n`.

This is because `Fin m = {0, 1, ..., m-1}` contains all of `{0, 1, ..., n-1}` when `m ≥ n`,
and these are precisely the elements satisfying `i.val < n`.

The proof uses an explicit bijection between `Fin n` and the filtered set. -/
lemma filter_val_lt_card {m n : ℕ} (h : m ≥ n) :
    (Finset.filter (fun i : Fin m => i.val < n) Finset.univ).card = n := by
  -- Establish bijection with Fin n via the natural inclusion
  let f : Fin n → Fin m := Fin.castLE h

  have hf_inj : Function.Injective f := Fin.castLE_injective h

  have h_image : Finset.filter (fun i : Fin m => i.val < n) Finset.univ =
                 Finset.image f Finset.univ := by
    ext i
    simp only [mem_filter, mem_univ, true_and, mem_image]
    constructor
    · intro hi_lt
      exact ⟨⟨i.val, hi_lt⟩, Fin.ext rfl⟩
    · rintro ⟨j, rfl⟩
      exact j.isLt

  rw [h_image, card_image_of_injective _ hf_inj]
  simp only [card_univ, Fintype.card_fin]

end Finset
