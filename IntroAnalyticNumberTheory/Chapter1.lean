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

@[simp]
theorem RelativelyPrime_def (a b : Int) : RelativelyPrime a b ↔ a.gcd b = 1 := Iff.rfl

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

-- Claude's version - which does not compile
-- theorem int_dvd_prime_product {p : ℕ} {a b : ℤ} (pp : Nat.Prime p)
--   (h : a ∣ p * b) : (a ∣ b) ∨ ((a / p) ∣ b ∧ ↑p ∣ a) := by
--   obtain ⟨x, hx⟩ := h
--   have p_nz : (p : ℤ) ≠ 0 := Int.natCast_ne_zero_iff_pos.mpr pp.pos
--   by_cases h' : (p : ℤ) ∣ a
--   · right
--     exact ⟨⟨x, Int.eq_mul_div_of_mul_eq_mul_of_dvd_left p_nz h' hx⟩, h'⟩
--   · left
--     have : (p : ℤ) ∣ x := by
--       rcases Int.Prime.dvd_mul' pp ⟨b, hx⟩ with ha | hx
--       · exact absurd (Int.natCast_dvd_natCast.mpr (Int.natAbs_dvd.mp ha)) h'
--       · exact Int.natAbs_dvd.mp hx
--     refine ⟨x / p, ?_⟩
--     rw [mul_comm] at hx ⊢
--     exact Int.eq_mul_div_of_mul_eq_mul_of_dvd_left p_nz this hx

theorem int_dvd_prime_product {p : ℕ} {a b : ℤ} (pp : Nat.Prime p)
  (h : a ∣ p * b) : (a ∣ b) ∨ ((a / p) ∣ b ∧ ↑p ∣ a) := by
  rcases h with ⟨x, x_def⟩
  have p_nz : (↑p ≠ (0 : ℤ)) := by
    -- presumably this is easier
    intro h
    have : (p = 0) := by exact Int.ofNat_eq_zero.mp h
    rw [this] at pp
    apply (Nat.not_prime_zero pp)
  by_cases h' : (↑p ∣ a)
  · right
    constructor
    · use x
      refine Int.eq_mul_div_of_mul_eq_mul_of_dvd_left ?_ h' x_def
      exact p_nz
    · exact h'
  · left
    have : (↑p ∣ x) := by
      have : (↑p ∣ a * x) := by exact Dvd.intro b x_def
      have : (↑p ∣ a ∨ ↑p ∣ x) := (Int.Prime.dvd_mul' pp this)
      cases this
      · absurd h'
        (expose_names; exact Int.natAbs_dvd.mp h)
      · (expose_names; exact Int.natAbs_dvd.mp h)
    use (x / p)
    rw [mul_comm a x] at x_def
    rw [mul_comm a]
    refine Int.eq_mul_div_of_mul_eq_mul_of_dvd_left ?_ this x_def
    exact p_nz

theorem rel_prime_dvd ( h: RelativelyPrime a b) : (c ∣ a * b) → c ∣ a ∨ c ∣ b := by
  unfold RelativelyPrime at h
  rw [Int.gcd_eq_one_iff] at h
  rintro ⟨x, x_def⟩

-- Claude simplified this
lemma dvd_a_impl_eq_1 {a b : ℤ}
  (h : RelativelyPrime a b)
  (h' : ↑((a + b).gcd (a - b)) ∣ a) :
  ↑((a + b).gcd (a - b)) = 1 := by
    set d := (a + b).gcd (a - b)
    apply Nat.eq_one_of_dvd_one
    rw [<- h, Int.dvd_gcd_iff]
    exact ⟨h', (Int.dvd_iff_dvd_of_dvd_add (Int.gcd_dvd_left _ _)).mp h'⟩

lemma dvd_a_and_b_over_2_impl_eq_2 {a b : ℤ}
  (h : RelativelyPrime a b)
  (two_div : (2 : ℤ) ∣ ↑((a + b).gcd (a - b)))
  (h' : ↑((a + b).gcd (a - b)) / (2 : ℤ) ∣ a)
  (h'' : ↑((a + b).gcd (a - b)) / (2 : ℤ) ∣ b) :
  -- (h''' : ↑2 ∣ ↑((a + b).gcd (a - b))) :
  ↑((a + b).gcd (a - b)) = 2 := by
    let d := ↑((a + b).gcd (a - b))
    unfold RelativelyPrime at h
    rw [Int.gcd_eq_one_iff] at h
    have : ↑d / (2 : ℤ) = 1 := by
      have : (↑d / (2 : ℤ) ≥ 0) := by
        exact Int.zero_le_ofNat (d / 2)
      exact Int.eq_one_of_dvd_one this (h (↑d / 2) h' h'')
    have : ↑d = (2 : ℤ) := by
      have two_neq_0 : ↑2 ≠ ↑0 := by grind
      have := Int.eq_mul_of_ediv_eq_right two_div this
      linarith
    exact Eq.symm ((fun {m n} ↦ Int.ofNat_inj.mp) (id (Eq.symm this)))

-- Exercise 1.4
-- idea here:
-- d = (a + b).gcd(a - b)
-- a + b + a - b = 2a, so d | 2a
-- if d | a, then (since d | a + b), d| b , therefore d | 1 (def of gcd).  therefore d = 1.
-- if d | 2, then d = 2 or d = 1.
example (h : RelativelyPrime a b) : (a + b).gcd (a - b) = 1 ∨ (a + b).gcd (a - b) = 2 := by
  let d := (a + b).gcd (a - b)
  have d_div_2a : ↑d ∣ (2 * a) := by
    have h' : (a + b).gcd (a - b) = d := by grind
    rw [Int.gcd_eq_iff] at h'
    rcases h' with ⟨d_div_a_plus_b, ⟨d_div_a_minus_b, _⟩⟩
    have r : (2 * a = (a - b) + (a + b)) := by ring
    rw [r]
    exact (Int.dvd_add_right d_div_a_minus_b).mpr d_div_a_plus_b
  have d_div_2b : ↑d ∣ (2 * b) := by
    have h' : (a + b).gcd (a - b) = d := by grind
    rw [Int.gcd_eq_iff] at h'
    rcases h' with ⟨d_div_a_plus_b, ⟨d_div_a_minus_b, _⟩⟩
    have r : (2 * b = (a + b) - (a - b)) := by ring
    rw [r]
    exact Int.dvd_sub d_div_a_plus_b d_div_a_minus_b
  have d_div_a_or_d_div_two : (↑d ∣ a) ∨ ((↑d / (2:ℤ)) ∣ a ∧ (2 : ℤ) ∣ ↑d) := by
    apply int_dvd_prime_product _ d_div_2a
    exact Nat.prime_two
  cases d_div_a_or_d_div_two
  case inl d_div_a =>
    left
    apply dvd_a_impl_eq_1 h
    exact d_div_a
  case inr d_div_two_div_a =>
    have d_div_b_or_d_div_two : (↑d ∣ b) ∨ ((↑d / (2:ℤ)) ∣ b  ∧ (2 : ℤ) ∣ ↑d) := by
      apply int_dvd_prime_product _ d_div_2b
      exact Nat.prime_two
    cases d_div_b_or_d_div_two
    case inl d_div_b =>
      left
      have : (a + b).gcd (a - b) = (b + a).gcd (b - a) := by
        rw [Int.add_comm]
        refine Int.gcd_right_eq_iff.mpr ?_
        intro c c_div_plus
        exact dvd_sub_comm
      rw [this]
      rw [rel_prime_swap] at h
      apply dvd_a_impl_eq_1 h
      rw [<- this]
      exact d_div_b
    case inr h' =>
      -- in this situation, need to have d / 2 | b and then combine it to show d / 2 | 1
      rcases h' with ⟨d_div_two_div_b, two_div_gcd⟩
      right
      -- don't understand why I have to do this, d should be definitionally equal
      have j : ↑((a + b).gcd (a - b)) / (2 : ℤ) ∣ a := by grind
      have j' : ↑((a + b).gcd (a - b)) / (2 : ℤ) ∣ b := by grind
      apply dvd_a_and_b_over_2_impl_eq_2 h two_div_gcd j j'


-- Exercise 1.5 needs some scaffolding:
-- if p | d -> p = q (some prime) then d = 1 or d = q
-- then proof by cases.  possible but annoying, I'll return to this.

-- Exercise 1.6
example (h : RelativelyPrime a b) (h' : d ∣ (a + b)) : RelativelyPrime d a := by
  obtain ⟨k, hk⟩ := h'
  apply Nat.eq_one_of_dvd_one
  rw [RelativelyPrime_def, Int.gcd_eq_one_iff] at h
  apply Int.ofNat_dvd.mp
  apply h ↑(d.gcd a)
  · exact Int.gcd_dvd_right _ _
  · rw [← Int.gcd_mul_left_sub_right d a k]
    convert Int.gcd_dvd_right d (d * k - a)
    linarith

-- Execise 1.7 requires some definition of a rational number, will
-- return to this.
-- a/b + c/d = n --> a*d/b*d + c*b/b*d = n --> n (b * d) = (a + d * b + c)

-- Exercise 1.8 lemmas

theorem not_squarefree_implies_divisor (n : ℕ)
  : ¬ Squarefree n → ∃ p, (Nat.Prime p) ∧ p * p ∣ n := by
  intro not_sqfree
  unfold Squarefree at not_sqfree
  push_neg at not_sqfree
  obtain ⟨x, x_div, hx⟩ := not_sqfree
  have x_ne_one : x ≠ 1 := fun x_eq_one => hx ⟨1, x_eq_one.symm⟩
  obtain ⟨p, pp, y, rfl⟩ := Nat.ne_one_iff_exists_prime_dvd.mp x_ne_one
  obtain ⟨k, hk⟩ := x_div
  exact ⟨p, pp, y * y * k, by linarith⟩

theorem square_dvd_implies_not_squarefree {p n : ℕ} (h : Nat.Prime p) :
  (p * p ∣ n) → ¬ Squarefree n := by sorry

-- this is just sugar around Nat.squarefree_mul, probably better to just use that
theorem squarefree_mult {p n} (pp : Nat.Prime p) :
  (¬ p ∣ n) → (Squarefree n) → Squarefree (n * p) := by
  intro p_div sqfree_n
  have : n.Coprime p := by
    rw [Nat.coprime_comm]
    refine (Nat.Prime.coprime_iff_not_dvd pp).mpr p_div
  rw [Nat.squarefree_mul this]
  refine ⟨sqfree_n, Prime.squarefree (Nat.prime_iff.mp pp)⟩

theorem neg_squarefree_mult {x n : ℕ} :
  ¬ (Squarefree n) → ¬ Squarefree (n * x) := by
  sorry

theorem coprime_dvd_div {p n} (pp : Nat.Prime p) (h : p ∣ n) (h' : ¬ p * p ∣ n) :
  Nat.Coprime p (n / p) := by
  refine Nat.gcd_eq_one_iff.mpr fun c c_div_p c_div_n_p => ?_
  rcases Nat.dvd_prime pp |>.mp c_div_p with rfl | rfl
  · trivial
  · exact absurd ((Nat.dvd_div_iff_mul_dvd h).mp c_div_n_p) h'

-- we did it joe
-- with help from Claude of course
theorem squarefree_decidable (n : ℕ) : Squarefree n ∨ ¬ Squarefree n := by
  induction' n using Nat.strong_induction_on with n ih
  rcases n with _ | _ | n
  · exact .inr not_squarefree_zero
  · exact .inl squarefree_one
  · obtain ⟨p, pp, hp⟩ := Nat.exists_prime_and_dvd (by omega : n + 2 ≠ 1)
    by_cases h : p * p ∣ n + 2
    · exact .inr (square_dvd_implies_not_squarefree pp h)
    · rcases ih ((n + 2) / p) (Nat.div_lt_self (by omega) pp.one_lt) with r_sqfree | neg_r_sqfree
      · refine .inl (Nat.div_mul_cancel hp ▸ squarefree_mult pp ?_ r_sqfree)
        exact fun ⟨k, hk⟩ => h ⟨k, by rw [mul_assoc, ← hk, mul_comm, Nat.div_mul_cancel hp]⟩
      · exact .inr (Nat.div_mul_cancel hp ▸ neg_squarefree_mult neg_r_sqfree)

-- then grouping the factors together.
-- I think we can do this by strong induction on n.
-- we have to pull out the primes one by one, and we have to pull out the
-- biggest prime factor of a number when we do it.  p^{2k + 1} | n ->
-- by induction (n/p^{2k+1}) gives us a, b so that a^2 b = (n/p^{2k+1})
-- then n = (a p^k)^2 (bp).  lots of stuff will be a pain here.
-- must choose a prime by a defined order, and "remember" that the prime has
-- been chosen in later stages.
example (n : ℕ) : ∃ a b, n = (a * a) * b ∧ Squarefree b := by sorry

end
