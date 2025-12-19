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

lemma rel_prime_mult_elim : RelativelyPrime (a * c) b → RelativelyPrime a b := by
  unfold RelativelyPrime
  rw [Int.gcd_eq_one_iff]
  intro ac_gcd_one_def
  rw [Int.gcd_eq_one_iff]
  intro c c_div_a c_div_b
  apply ac_gcd_one_def c (Int.dvd_mul_of_dvd_left c_div_a) c_div_b

lemma rel_prime_mult_elim2 : RelativelyPrime (a * c) (b * d) → RelativelyPrime a b := by
  intro h
  apply (rel_prime_mult_elim _ _ c)
  rw [rel_prime_swap]
  apply (rel_prime_mult_elim _ _ d)
  rw [rel_prime_swap]
  exact h

-- Exercise 1.1
example (h : RelativelyPrime a b) :
  (c ∣ a) ∧ (d ∣ b) → (RelativelyPrime c d) := by
  intro ⟨⟨p, a_def⟩, ⟨q, b_def⟩⟩
  rw [a_def] at h
  rw [b_def] at h
  apply (rel_prime_mult_elim2 _ _ p q)
  exact h

-- Exercise 1.2
-- argument is basically
-- ax + by = 1, ap + cq = 1
-- therefore acx + bcy = c
-- therefore ap + (acx + bcy) q = 1
-- therefore [collecting as] a(p + cxq) + bc (yq) = 1
-- therefore gcd a bc | 1
-- therefore gcd a bc = 1
-- therefore (a,bc) rel prime
lemma rel_prime_mult_right
  (h : RelativelyPrime a b)
  (h' : RelativelyPrime a c) : RelativelyPrime a (b * c) := by
  unfold RelativelyPrime
  unfold RelativelyPrime at h h'
  have ab_linear : ∃ x y, (1 = a * x + b * y) := by
    apply dvd_of_eq at h
    rw [Int.gcd_dvd_iff] at h
    exact h
  have ac_linear : ∃ p q, (1 = a * p + c * q) := by
    apply dvd_of_eq at h'
    rw [Int.gcd_dvd_iff] at h'
    exact h'
  rcases ab_linear with ⟨x, ⟨y, xy_def⟩⟩
  rcases ac_linear with ⟨p, ⟨q, pq_def⟩⟩
  apply Nat.eq_one_of_dvd_one
  have : c = a * x * c + b * y * c := by
    grind
  have bar : a * (p + c * x * q) + (b * c) * (y * q) = (1 : ℕ) := by
    grind
  rw [<- Int.ofNat_dvd, <- bar]
  apply gcd_div_linear_combo

example {x : ℤ} {y : ℕ} : x^(y + 1) = x^y * x := Int.pow_succ x y

lemma rel_prime_power {n : ℕ} (h : RelativelyPrime a b) : RelativelyPrime a (b^(n + 1)) := by
  induction n with
    | zero => dsimp; rw [Int.pow_one]; exact h
    | succ n ih =>
      rw [Int.pow_succ, mul_comm]
      apply rel_prime_mult_right _ _ _ h ih

-- Exercise 1.3 (exact except for the bounds, need to figure out how to do this)
example (h : RelativelyPrime a b)
  (n k : ℕ) : RelativelyPrime (a^(n + 1)) (b^(k + 1)) := by
  have : RelativelyPrime a (b^(k + 1)) := rel_prime_power _ _ h
  have : RelativelyPrime (b^(k + 1)) a := by rw [rel_prime_swap]; exact this
  have : RelativelyPrime (b^(k + 1)) (a^(n + 1)) := (rel_prime_power _ _ this)
  rw [rel_prime_swap]; exact this

example (h : a ∣ c) (h' : a ∣ b + c) : a ∣ b := by
  exact (Int.dvd_iff_dvd_of_dvd_add h').mpr h

example (h : a ∣ c) (h' : a ∣ b) : a ∣ (b + c) := by
  exact (Int.dvd_add_right h').mpr h

-- Exercise 1.4
-- idea here:
-- d = (a + b).gcd(a - b)
-- a + b + a - b = 2a, so d | 2a
-- if d | a, then (since d | a + b), d| b , therefore d | 1 (def of gcd).  therefore d = 1.
-- if d | 2, then d = 2 or d = 1.
example (h : RelativelyPrime a b) : (a + b).gcd (a - b) = 1 ∨ (a + b).gcd (a - b) = 2 := by
  let d := (a + b).gcd (a - b)
  have h : ↑d ∣ (2 * a) := by
    have h' : (a + b).gcd (a - b) = d := by grind
    rw [Int.gcd_eq_iff] at h'
    rcases h' with ⟨d_div_a_plus_b, ⟨d_div_a_minus_b, _⟩⟩
    have r : (2 * a = (a - b) + (a + b)) := by ring
    rw [r]
    exact (Int.dvd_add_right d_div_a_minus_b).mpr d_div_a_plus_b
  rw [Int.dvd_mul] at h
  -- it's not 1 or 2, since it could be negative.
  have d_div_a_or_d_div_two : (↑d ∣ a) ∨ (d ∣ 2) := by
    -- OK so we know d | 2a, so we need to go through the cases here.
    -- NOTE a could be negative.
    -- rcases h with ⟨c1, ⟨c2, h'⟩⟩
    -- rcases h' with ⟨c1_div_2, ⟨c2_div_a, def_of_d⟩⟩
    -- have : c1 = -1 ∨ c1 = 1 ∨ c1 = -2 ∨ c1 = 2 := by
    --   sorry
    -- cases this
    -- case inl c1_neg_one =>
    --   left
    --   have c2_def : c2 = -a := by sorry
    --   rw [<- def_of_d, c2_def, c1_neg_one, neg_mul_neg, one_mul]
    -- case inr this =>
    --   cases this
    --   case inl c1_one =>
    --     left
    --     have c2_def : c2 = a := by sorry
    --     rw [<- def_of_d, c2_def, c1_one, one_mul]
    --   case inr this =>
    --     cases this
    --     case inl c1_neg_two =>
    --       right
    sorry
  cases d_div_a_or_d_div_two
  case inl d_div_a =>
    left
    apply Nat.eq_one_of_dvd_one
    have : ↑d ∣ (a + b) := by exact Int.gcd_dvd_left (a + b) (a - b)
    have d_div_b : ↑d ∣ b := by exact (Int.dvd_iff_dvd_of_dvd_add this).mp h
    have : ↑d ∣ 1 := by
      rcases h with ⟨c1, ⟨c2, h'⟩⟩
      rw [<- h, Int.dvd_gcd_iff]
      exact ⟨d_div_a, d_div_b⟩
    -- ugly by I mean it works.
    exact (Nat.ModEq.dvd_iff (congrFun rfl 1) this).mp this
  case inr h =>
    have : d = 1 ∨ d = 2 := by
      refine (Nat.dvd_prime ?_).mp h
      exact Nat.prime_two
    exact Or.symm (Or.symm this)

end
