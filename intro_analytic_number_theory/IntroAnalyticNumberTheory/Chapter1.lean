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
  unfold RelativelyPrime
  rw [Int.gcd_eq_one_iff]
  intro ac_gcd_one_def
  rw [Int.gcd_eq_one_iff]
  intro c c_div_a c_div_b
  apply ac_gcd_one_def c (Int.dvd_mul_of_dvd_left c_div_a) c_div_b

lemma rel_prime_mult2 : RelativelyPrime (a * c) (b * d) → RelativelyPrime a b := by
  intro h
  apply (rel_prime_mult _ _ c)
  rw [rel_prime_swap]
  apply (rel_prime_mult _ _ d)
  rw [rel_prime_swap]
  exact h


-- Exercise 1.1
example (h : RelativelyPrime a b) :
  (c ∣ a) ∧ (d ∣ b) → (RelativelyPrime c d) := by
  intro ⟨⟨p, a_def⟩, ⟨q, b_def⟩⟩
  rw [a_def] at h
  rw [b_def] at h
  apply (rel_prime_mult2 _ _ p q)
  exact h

-- Exercise 1.2
example (h : RelativelyPrime a b ∧ RelativelyPrime b c) : RelativelyPrime a (b * c) := by
  sorry
