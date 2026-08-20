import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Factorization.Basic

namespace IUTSourceShape

open scoped BigOperators

def abcRadical (n : ℕ) : ℕ :=
  ∏ p in n.primeFactors, p

def PairwiseCoprimeABC (a b c : ℕ) : Prop :=
  Nat.Coprime a b ∧ Nat.Coprime b c ∧ Nat.Coprime c a

def ABCConjecture : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ C : ℝ, ∀ a b c : ℕ,
      0 < a → 0 < b → 0 < c →
      a + b = c → PairwiseCoprimeABC a b c →
      Real.log (((max a (max b c) : ℕ) : ℝ)) ≤
        (1 + ε) *
          Real.log (((abcRadical (a * b * c) : ℕ) : ℝ)) + C

end IUTSourceShape
