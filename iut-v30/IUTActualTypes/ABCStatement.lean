/-
Copyright (c) 2026 ChatGPT. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ChatGPT
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Factorization.Basic

/-!
# The logarithmic abc conjecture
-/

namespace IUTActualTypes

open scoped BigOperators

/-- Product of the distinct prime divisors. -/
def abcRadical (n : ℕ) : ℕ :=
  Finset.prod n.primeFactors id

/-- Pairwise coprimality of an abc triple. -/
def PairwiseCoprimeABC (a b c : ℕ) : Prop :=
  Nat.Coprime a b ∧ Nat.Coprime b c ∧ Nat.Coprime c a

/-- The standard logarithmic form of the abc conjecture. -/
def ABCConjecture : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ C : ℝ, ∀ a b c : ℕ,
      0 < a → 0 < b → 0 < c →
      a + b = c → PairwiseCoprimeABC a b c →
      Real.log (((max a (max b c) : ℕ) : ℝ)) ≤
        (1 + ε) * Real.log (((abcRadical (a * b * c) : ℕ) : ℝ)) + C

end IUTActualTypes
