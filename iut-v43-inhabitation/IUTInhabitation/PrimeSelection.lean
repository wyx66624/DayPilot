/-
Copyright (c) 2026 ChatGPT. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ChatGPT
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.Prime.Infinite

/-!
# Finite prime avoidance

An elementary reduction used by the admissible-prime inhabitation theorem.
-/

namespace IUTInhabitation

open scoped BigOperators

private theorem mem_le_sum (s : Finset ℕ) {p : ℕ} (hp : p ∈ s) :
    p ≤ ∑ q in s, q := by
  classical
  induction s using Finset.induction_on with
  | empty => simp at hp
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha]
      simp only [Finset.mem_insert] at hp
      rcases hp with rfl | hp
      · exact Nat.le_add_right _ _
      · exact le_trans (ih hp) (Nat.le_add_left _ _)

/-- There is a prime strictly above a bound and outside a finite set. -/
theorem exists_prime_above_not_mem (N : ℕ) (s : Finset ℕ) :
    ∃ p : ℕ, p.Prime ∧ N < p ∧ p ∉ s := by
  classical
  let B : ℕ := max N (∑ q in s, q) + 1
  rcases Nat.exists_infinite_primes B with ⟨p, hBp, hpprime⟩
  refine ⟨p, hpprime, ?_, ?_⟩
  · exact lt_of_lt_of_le
      (Nat.lt_succ_of_le (le_max_left N (∑ q in s, q))) hBp
  · intro hps
    have hle : p ≤ ∑ q in s, q := mem_le_sum s hps
    have hsumB : (∑ q in s, q) < B := by
      exact Nat.lt_succ_of_le (le_max_right N (∑ q in s, q))
    have hsumP : (∑ q in s, q) < p := lt_of_lt_of_le hsumB hBp
    exact (not_lt_of_ge hle) hsumP

end IUTInhabitation
