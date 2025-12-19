import Mathlib.Tactic
import Mathlib.Util.Delaborators

section
variable (a b c d : Int)
variable (x y : Int)

-- this is euclid extended algo
theorem gcd_linear_combo : (a.gcd b = d) -> ∃ x y, ( a * x + b * y = d) := by sorry

def RelativelyPrime (a b : Int) : Prop := a.gcd b = 1

lemma rel_prime_swap : RelativelyPrime a b = RelativelyPrime b a := by
  unfold RelativelyPrime
  rw [Int.gcd_comm]

lemma rel_prime_mult : RelativelyPrime (a * c) b → RelativelyPrime a b := by
  sorry

-- Exercise 1.1
example (h : RelativelyPrime a b) :
  (c ∣ a) ∧ (d ∣ b) → (RelativelyPrime c d) := by
  intro ⟨⟨p, a_def⟩, ⟨q, b_def⟩⟩
  rw [a_def] at h
  rw [b_def] at h
  apply (rel_prime_mult _ _ p)
  rw [rel_prime_swap]
  apply (rel_prime_mult _ _ q)
  rw [rel_prime_swap]
  exact h

-- Exercise 1.2
example (h : RelativelyPrime a b ∧ RelativelyPrime b c) : RelativelyPrime a (b * c) := by
  sorry
