/-
Copyright (c) 2026 ChatGPT. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ChatGPT
-/
import Mathlib

/-!
# Finite prime avoidance

An elementary reduction used by the admissible-prime inhabitation theorem.
-/

set_option linter.style.header false

namespace IUTInhabitation

private theorem mem_le_sum (s : Finset ℕ) {p : ℕ} (hp : p ∈ s) :
    p ≤ s.sum id := by
  classical
  induction s using Finset.induction_on with
  | empty => simp at hp
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha]
      simp only [Finset.mem_insert] at hp
      rcases hp with rfl | hp
      · omega
      · have h := ih hp
        omega

/-- There is a prime strictly above a bound and outside a finite set. -/
theorem exists_prime_above_not_mem (N : ℕ) (s : Finset ℕ) :
    ∃ p : ℕ, p.Prime ∧ N < p ∧ p ∉ s := by
  classical
  let B : ℕ := N + s.sum id + 1
  rcases Nat.exists_infinite_primes B with ⟨p, hBp, hpprime⟩
  refine ⟨p, hpprime, ?_, ?_⟩
  · dsimp [B] at hBp
    omega
  · intro hps
    have hle := mem_le_sum s hps
    dsimp [B] at hBp
    omega

end IUTInhabitation
