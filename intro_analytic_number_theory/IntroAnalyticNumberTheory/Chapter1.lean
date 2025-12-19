import Mathlib.Tactic
import Mathlib.Util.Delaborators

section
variable (a b c d : Int)
variable (x y : Int)

-- can use this:
-- https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Int/GCD.html#Int.gcd_dvd_iff

-- probably there is a shorter way to do this
theorem gcd_div_linear_combo (x y : Int) : ↑(a.gcd b) ∣ (a * x + b * y) := by
  have a_x : ↑(a.gcd b) ∣ (a * x) := Int.dvd_mul_of_dvd_left (Int.gcd_dvd_left _ _)
  have b_y : ↑(a.gcd b) ∣ (b * y) := Int.dvd_mul_of_dvd_left (Int.gcd_dvd_right _ _)
  exact (Int.dvd_add_right a_x).mpr b_y

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

-- don't need this since it's the same as Nat.eq_one_of_dvd_one
-- lemma div_one_means_one (n : ℕ) (h : n ∣ 1) : n = 1 := Nat.eq_one_of_dvd_one h

example (a b : ℤ) (h : a = b) : a ∣ b := by
  exact dvd_of_eq h

-- Exercise 1.2
example
  (h : RelativelyPrime a b)
  (h' : RelativelyPrime b c) : RelativelyPrime a (b * c) := by
-- argument is basically
-- ax + by = 1, ap + cq = 1
-- therefore acx + bcy = c
-- therefore ap + (acx + bcy) q = 1
-- therefore [collecting as] a(p + cx) + bc (yq) = 1
-- therefore gcd a bc | 1
-- therefore gcd a bc = 1
-- therefore (a,bc) rel prime
  unfold RelativelyPrime
  unfold RelativelyPrime at h h'
  have ab_linear : ∃ x y, (1 = a * x + b * y) := by
    apply dvd_of_eq at h
    rw [Int.gcd_dvd_iff] at h
    exact h
  have ac_linear : ∃ p q, (1 = b * p + c * q) := by
    apply dvd_of_eq at h'
    rw [Int.gcd_dvd_iff] at h'
    exact h'
  rcases ab_linear with ⟨x, ⟨y, xy_def⟩⟩
  rcases ac_linear with ⟨p, ⟨q, pq_def⟩⟩
  apply Nat.eq_one_of_dvd_one
  have : c = a * x * c + b * y * c := by
    sorry
  have foo : a * (p + c * x) + (b * c) * (y * q) = (1 : ℕ) := by sorry
  -- seems that were getting tripped up on ints/nats.  we can rewrite
  rw [<- Int.ofNat_dvd, <- foo]
  apply gcd_div_linear_combo
