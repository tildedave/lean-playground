import Mathlib.Tactic
import Mathlib.Util.Delaborators

set_option linter.style.induction false

section
variable (a b c d : ℤ)
variable (x y : ℤ)
variable (n : ℕ)

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

-- Exercise 1.8
-- bit of a saga
-- kind of nice to not deal with integers on this one

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
  (p * p ∣ n) → ¬ Squarefree n := by
  intro q n_sqfree
  obtain ⟨k, hk⟩ := q
  rw [hk, squarefree_mul_iff] at n_sqfree
  obtain ⟨_, p_sq_sqfree, _⟩ := n_sqfree
  unfold Squarefree at p_sq_sqfree
  obtain p_unit := (p_sq_sqfree p (dvd_refl _))
  apply Prime.not_unit at p_unit
  · contradiction
  · exact Nat.prime_iff.mp h

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
  intro neg_n_sqfree neg_n_x_sqfree
  rw [squarefree_mul_iff] at neg_n_x_sqfree
  rcases neg_n_x_sqfree with ⟨_, n_sqfree, _⟩
  contradiction

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
example (n : ℕ) : ∃ a b, n = (a * a) * b ∧ Squarefree b := by
  induction' n using Nat.strong_induction_on with n ih
  rcases n with _ | _ | n
  · exact ⟨0, 1, rfl, squarefree_one⟩
  · exact ⟨1, 1, rfl, squarefree_one⟩
  · set n' := n + 1 + 1
    obtain ⟨p, pp, hp⟩ := Nat.exists_prime_and_dvd (by omega : n + 2 ≠ 1)
    by_cases h : p * p ∣ n'
    · set r := n' / (p * p)
      have : r < n' := Nat.div_lt_self
        (Nat.zero_lt_succ (n + 1))
        (Nat.sqrt_lt.mp (Nat.Prime.one_lt pp))
      obtain ⟨qa, qb, ⟨hq, hsq⟩⟩ := (ih r this)
      refine ⟨qa * p, qb, ?_, hsq⟩
      rw [Nat.eq_mul_of_div_eq_left h hq]; ring
    · set r := n' / p
      have : r < n' := Nat.div_lt_self
        (Nat.zero_lt_succ (n + 1))
        (Nat.Prime.one_lt pp)
      obtain ⟨qa, qb, ⟨hq, hsq⟩⟩ := (ih r this)
      use qa
      use (qb * p)
      change (n' / p  = qa * qa * qb) at hq
      have clear_denom : n' = (qa * qa * qb) * p := by
        exact Nat.eq_mul_of_div_eq_left hp hq
      apply (squarefree_mult pp) at hsq
      · refine ⟨?_, hsq⟩
        grind
      · intro ⟨k, hk⟩
        apply h
        use (k * qa * qa)
        grind

-- 1.9a is wrong of course, 9, 25 | 225, 3 doesn't divide 5.
-- 1.9b is right because if you didn't have a division, it violates the
-- maximality.  Should be an easy proof... (ha ha ha)

theorem ndvd_impl_lcm_gt {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) (h : ¬a ∣ b) : b < a.lcm b := by
  by_contra hnlt
  push_neg at hnlt
  have hdvd : b ∣ a.lcm b := Nat.dvd_lcm_right a b
  have hlcm_pos : 0 < a.lcm b := Nat.lcm_pos
    (Nat.zero_lt_of_ne_zero ha)
    (Nat.zero_lt_of_ne_zero hb)
  have : b ≤ a.lcm b := Nat.le_of_dvd hlcm_pos hdvd
  have b_eq : a.lcm b = b := Nat.le_antisymm hnlt this
  have : a ∣ a.lcm b := Nat.dvd_lcm_left a b
  rw [b_eq] at this
  exact h this

-- theorem dvd_lcm_mul {a b n : ℕ} (ha : a ∣ n) (hb : b ∣ n) : a.lcm b ∣ n :=
--   by exact Nat.lcm_dvd ha hb

theorem lcm_square {a b : ℕ} : (a.lcm b * a.lcm b) = (a * a).lcm (b * b) := by
  repeat rw [<- Nat.pow_two]
  rw [Nat.pow_lcm_pow]

example {a b n : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) (h : b * b ∣ n ∧ ∀ a, a * a ∣ n → a^2 ≤ b^2)
  : a * a ∣ n → a ∣ b := by
  intro a_sq_div_n
  obtain ⟨bsq_div_n, bsq_maximal⟩ := h
  by_cases h : a ∣ b
  · trivial
  · have : (a.lcm b) * (a.lcm b) ∣ n := by
      rw [lcm_square]
      exact Nat.lcm_dvd a_sq_div_n bsq_div_n
    have a_gt_zero : b < a.lcm b := (ndvd_impl_lcm_gt ha hb h)
    have b_gt_zero : (a.lcm b) * (a.lcm b) > b * b := by
      exact Nat.mul_self_lt_mul_self a_gt_zero
    obtain bad_bound := bsq_maximal _ this
    linarith

-- Exercise 1.11

def Composite (n : ℤ) := ∃ a b, ¬ IsUnit a ∧ ¬ IsUnit b ∧ (n = a * b)

example (n : ℤ) (hn : n > 1) : Composite (n^4 + 4) := by
  have : (n^4 + 4) = (n^2 - 2*n + 2) * (n^2 + 2*n + 2) := by
    calc (n^4 + 4) = ((n^4 + 4*n^2 + 4) - 4*n^2) := by ring
         _ = (n^2 + 2)^2 - (2*n)^2 := by ring
         _ = (n^2 - 2*n + 2)*(n^2 + 2*n + 2) := by
          rw [sq_sub_sq, add_right_comm, <- sub_add_eq_add_sub, mul_comm]
  rw [this]
  refine ⟨n^2 - 2*n + 2, n^2 + 2*n + 2, ?_, ?_, rfl⟩
  all_goals {
    intro h
    rcases Int.isUnit_iff.mp h with h1 | h1 <;> nlinarith
  }

example (a b c : ℕ) : a * (b + c) = a * b + a * c := by exact Nat.mul_add a b c

-- Exercise 1.15. Prove every n ≥ 12 is the sum of two composite numbers.

theorem composite_even (a : ℤ) (ha : a > 2) : Even a -> Composite a := by
  rintro ⟨h⟩
  refine ⟨2, h, ?_, ?_, by grind⟩
  all_goals {
    rw [Int.isUnit_iff]
    push_neg
    refine ⟨by linarith, by linarith⟩
  }

theorem even_four : Even (4 : ℤ) := by rw [Int.even_iff]; dsimp
theorem odd_nine : Odd (9 : ℤ) := by rw [Int.odd_iff]; dsimp

theorem composite_four : Composite 4 := by
  refine composite_even 4 (by linarith) (even_four)

theorem composite_nine : Composite 9 := by
  refine ⟨3, 3, by rw [Int.isUnit_iff]; tauto, by rw [Int.isUnit_iff]; tauto, by dsimp⟩

example (n : ℤ) (ha : n ≥ 12) : ∃ a b, Composite a ∧ Composite b ∧ a + b = n := by
  rcases (Int.even_or_odd n) with even | odd
  · refine ⟨n - 4, 4, ?_, composite_four, by ring⟩
    apply composite_even _ (by omega)
    rw [Int.even_sub]
    exact ⟨fun _ ↦ even_four, fun _ ↦ even⟩
  · refine ⟨n - 9, 9, ?_, composite_nine, by ring⟩
    apply composite_even _ (by omega)
    rw [Int.even_sub']
    exact ⟨fun _ ↦ odd_nine, fun _ ↦ odd⟩

  -- argument here is:
  -- if n is even, n = n - 4 + 4
  -- if n is odd, n = (n - 9) + 9 -> n - 9 is even so composite.

-- Exercise 1.16. Prove that if 2^n - 1 is prime, then n is prime.
-- this is a contrapositive statement

lemma factor_power_2 (a b : ℕ) :
    (2^(a * b) : ℤ) - 1 = ((2^a : ℤ) - 1) * (∑ i ∈ Finset.range b, (2^(a * i) : ℤ)) := by
  induction b with
  | zero => simp
  | succ b ih =>
    rw [Finset.sum_range_succ, add_comm, Int.mul_add, <- ih]
    ring_nf

lemma nat_geo_sum_eq (x : ℕ) (h : x ≥ 2) (n : ℕ)
  : ∑ i ∈ Finset.range n, x ^ i = (x ^ n - 1) / (x - 1) := by
  rw [Nat.geomSum_eq]
  linarith

example (a n : ℕ) : 2^(a * n) = (2^a)^n := by exact Nat.pow_mul 2 a n

example (n : ℕ) (hn : n ≥ 2) : Nat.Prime (2^n - 1) → Nat.Prime n := by
  contrapose
  have twon_bound : (2 ^ n - 1 ≥ 2) := by
    refine (Nat.le_sub_one_iff_lt ?_).mpr ?_
    · exact Nat.two_pow_pos n
    · refine (Nat.log2_lt ?_).mp hn
      exact Ne.symm (Nat.zero_ne_add_one 1)
  rw [Nat.not_prime_iff_exists_mul_eq hn]
  intro ⟨a, b, a_bound, b_bound, hab⟩
  · rw [Nat.not_prime_iff_exists_mul_eq twon_bound]
    have two_pow_a_below : 0 < 2^a := by exact Nat.two_pow_pos a
    have two_pow_n_below : 0 < 2^n := by exact Nat.two_pow_pos n
    refine ⟨2^a - 1, ∑ i ∈ Finset.range b, 2^(a * i), ?_, ?_, ?_⟩
    · have : 2^a < 2^n := Nat.pow_lt_pow_right (by omega : 1 < 2) a_bound
      omega
    · have : ∑ i ∈ Finset.range b, 2 ^ (a * i) = ∑ i ∈ Finset.range b, (2 ^ a) ^ i := by
        simp only [← pow_mul]
      rw [this]
      have a_gt_1 : a > 1 := by
        by_cases h : a > 1
        · trivial
        · exfalso
          rw [Nat.not_lt] at h
          induction a
          · linarith
          · nlinarith [h]
      have : 2^a ≥ 2 := by exact Nat.le_pow (by linarith)
      rw [nat_geo_sum_eq _ this, <- pow_mul, hab]
      have : 2^ n - 1 ≥ 0 := by linarith
      refine Nat.div_lt_self (by linarith) (?_)
      refine Nat.lt_sub_of_add_lt ?_
      dsimp
      refine (Nat.log2_lt (by tauto)).mp a_gt_1
    · rw [<- hab]
      zify [Nat.one_le_two_pow, Nat.one_le_two_pow]
      exact_mod_cast (factor_power_2 a b).symm

-- 1.19 - Prove gcd(a_n, a_n + 1) = 1 for the fib sequence

def fib : ℕ -> ℤ
| 0 => 1
| 1 => 1
| (n + 2) => fib (n + 1) + fib n

example : fib 7 = 21 := by rfl

example : 1 + 1 = 2 := by exact Nat.one_add 1

lemma fib_zero : fib 0 = 1 := by rfl
lemma fib_one : fib 1 = 1 := by rfl
lemma fib_sub : fib (n + 2) - fib (n + 1) = fib n := by
  rw [fib]; ring

-- Thanks Claude
theorem fib_gt_0 : ∀ n, fib n > 0
| 0 => by unfold fib; linarith
| 1 => by unfold fib; linarith
| n + 2 => by
  have ih1 := fib_gt_0 (n + 1)
  have ih2 := fib_gt_0 n
  rw [fib]
  linarith

-- approach: show a_n * a_n - 3 - a_{n-1} a_{n-2} = ± 1
-- Int.gcd_dvd_iff is the way we'll do it

abbrev fib_diff (n : ℕ) : ℤ :=
  (fib (n + 3) * fib n) - fib (n + 2) * fib (n + 1)

lemma not_even_succ {n : ℤ} : Even n -> ¬ Even ( n + 1) := by
  intro ⟨a, _⟩ ⟨x, _⟩
  omega

lemma not_odd_succ {n : ℤ} : Odd n -> ¬ Odd ( n + 1) := by
  intro ⟨a, _⟩ ⟨x, _⟩
  omega

lemma odd_pred {n : ℕ} : Odd (n + 1) -> Even n := by
  intro ⟨a, _⟩
  exact ⟨a, by omega⟩

lemma even_pred {n : ℕ} : Even (n + 1) -> Odd n := by
  intro ⟨a, _⟩
  exact ⟨a - 1, by omega⟩

example : (a + b) * c = a * c + b * c := by exact Int.add_mul a b c
example : (-a + b) = -(a - b) := by
  rw [neg_add_eq_sub a b]
  exact Eq.symm (Int.neg_sub a b)

theorem parity_implies_fib_diff_value (n : ℕ) :
  (Odd n → fib_diff n = -1) ∧ (Even n → fib_diff n = 1) := by
  induction n with
  | zero =>
      exact ⟨by (intro _; exfalso; tauto), by (intro _; rfl)⟩
  | succ n ih =>
      rcases (Int.even_or_odd n) with even | odd
      · obtain ih := by
          rw [Int.even_coe_nat] at even
          exact (And.right ih even)
        refine ⟨?_, ?_⟩
        · intro _
          rw [fib_diff]
          rw [show fib (n + 1 + 3) * fib (n + 1) = (fib (n + 3) + fib (n + 2)) * fib (n + 1)
            by exact Int.neg_inj.mp rfl]
          rw [show fib (n + 1 + 2) * fib (n + 1 + 1) = fib (n + 3) * (fib (n + 1) + fib n)
            by exact Int.neg_inj.mp rfl]
          ring_nf -- must undo the weird pluses now
          repeat rw [<- add_comm n]
          rw [neg_add_eq_sub, <- Int.neg_sub]
          rw [<- fib_diff, ih]
        · intro even_n_plus_one
          rw [<- Int.even_coe_nat] at even_n_plus_one
          apply not_even_succ at even
          contradiction
      · obtain ih := by
          rw [Int.odd_coe_nat] at odd
          exact (And.left ih odd)
        refine ⟨?_, ?_⟩
        · intro odd_n_plus_one
          rw [<- Int.odd_coe_nat] at odd_n_plus_one
          apply not_odd_succ at odd
          contradiction
        · intros
          rw [fib_diff]
          rw [show fib (n + 1 + 3) * fib (n + 1) = (fib (n + 3) + fib (n + 2)) * fib (n + 1)
            by exact Int.neg_inj.mp rfl]
          rw [show fib (n + 1 + 2) * fib (n + 1 + 1) = fib (n + 3) * (fib (n + 1) + fib n)
            by exact Int.neg_inj.mp rfl]
          ring_nf -- must undo the weird pluses now
          repeat rw [<- add_comm n]
          rw [neg_add_eq_sub, <- Int.neg_sub]
          rw [<- fib_diff, ih]
          exact Int.neg_neg 1

-- actual Exercise 1.19

example (a : ℕ) (h : a ∣ 1) : ↑a ∣ (1 : ℤ) := by exact Int.ofNat_dvd_left.mpr h

-- Int.gcd_dvd_iff is the way we'll do it

theorem linear_combo_one_forces_gcd {a b : ℤ} :
  (∃ x y, a * x + b * y = 1) → a.gcd b = 1 := by
  intro ⟨x, y, h⟩
  have : ↑(a.gcd b) ∣ (1 : ℤ) := by
    have ha_dvd : ↑(a.gcd b) ∣ a := Int.gcd_dvd_left a b
    have hb_dvd : ↑(a.gcd b) ∣ b := Int.gcd_dvd_right a b
    rw [← h]
    exact gcd_div_linear_combo a b x y
  apply Int.eq_one_of_dvd_one (by omega) at this
  omega

theorem linear_combo_minus_one_forces_gcd {a b : ℤ} :
  (∃ x y, a * x + b * y = -1) → a.gcd b = 1 := by
  intro ⟨x, y, h⟩
  apply linear_combo_one_forces_gcd
  refine ⟨-x, -y, ?_⟩
  grind

-- full statement of 1.19 \yay/
example {n : ℕ} : (fib (n + 1)).gcd (fib n) = 1 := by
  rcases n with _ | _ | n
  · rfl
  · rfl
  · rcases (Int.even_or_odd n) with even | odd
    · have : (fib_diff n = 1) := by
        obtain ⟨_, l⟩ := parity_implies_fib_diff_value n
        rw [Int.even_coe_nat] at even
        exact (l even)
      apply linear_combo_one_forces_gcd
      use fib n, -fib (n + 1)
      rw [show fib (n + 2) * (-fib (n + 1)) = -(fib (n + 2) * fib (n + 1)) by ring]
      rw [Int.even_coe_nat] at even
      rw [add_comm, neg_add_eq_sub, <- fib_diff, parity_implies_fib_diff_value n |>.2 even]
    · apply linear_combo_minus_one_forces_gcd
      refine ⟨fib n, - 1 * fib (n + 1), ?_⟩
      rw [show fib (n + 2) * (-1 * fib (n + 1)) =  - (fib (n + 2) * fib (n + 1)) by ring]
      rw [Int.odd_coe_nat] at odd
      rw [add_comm, neg_add_eq_sub, <- fib_diff, parity_implies_fib_diff_value n |>.1 odd]
end
