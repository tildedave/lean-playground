import Mathlib.Tactic
import Mathlib.Util.Delaborators

-- This is an attempt to re-prove https://github.com/tildedave/coq-sum-of-squares
-- using Lean.

#check Nat.Coprime

def SumOfSquares (a : ℤ) : Prop
  := ∃ p > 0, ∃ q > 0, p.gcd q = 1 ∧ p^2 + q^2 = a

example {a : ℕ} : (a = 1) ∨ (a ≠ 1) := by exact eq_or_ne a 1

-- Lemma 1.4 Primes of the Form x^2 + nx^2
-- Suppose that N is a sum of two relatively prime squares, and that
-- q = x^2 + y^2 is a prime divisor of N. Then N/q is also a sum of two
-- relatively prime squares.


-- does not force coprime but this is a lemma
def PrimeSumOfSquares (q : ℕ) : Prop
  := Nat.Prime q ∧ (∃ x > 0, ∃ y > 0, x ^ 2 + y ^ 2 = (q : ℤ))

-- x and y have to be coprime or else q has a nontrivial divisor.
lemma prime_sumofsquares_coprime {q : ℕ} {x y : ℤ}
  (qprime : Nat.Prime q) (hx : x > 0) (hy : y > 0)
  (hq : x ^ 2 + y ^ 2 = (q : ℤ))
  : x.gcd y = 1 := by
    rcases eq_or_ne (x.gcd y) 1 with h | impossible
    · exact h
    · exfalso
      -- set d := x.gcd y
      have : ↑(x.gcd y) ∣ x^2 + y^2 := by
        repeat rw [pow_two]
        refine (Int.dvd_add_right ?_).mpr ?_
        · exact Int.dvd_mul_of_dvd_right (Int.gcd_dvd_left x y)
        · exact Int.dvd_mul_of_dvd_left (Int.gcd_dvd_right x y)
      have : (x.gcd y) ∣ q := by
        rw [hq] at this
        exact Int.ofNat_dvd.mp this
      rw [Nat.dvd_prime qprime] at this
      rcases this with eq_1 | eq_p
      · tauto
      · nlinarith [Int.gcd_le_left y hx]

lemma relprime_lemma {c d x y : ℤ} (h : (c * x - d * y).gcd (d * x + c * y) = 1)
  : c.gcd d = 1 := by
  rw [Int.gcd_eq_one_iff]
  intro q qdivc qdivd
  obtain h' := by
    rw [Int.gcd_eq_one_iff] at h
    exact h q
  exact h'
    (Int.dvd_sub (Int.dvd_mul_of_dvd_left qdivc) (Int.dvd_mul_of_dvd_left qdivd))
    (Int.dvd_add (Int.dvd_mul_of_dvd_left qdivd) (Int.dvd_mul_of_dvd_left qdivc))

-- example {x y q : ℤ} (hq : q ≠ 0) (h : x = y) : (x * q = y * q) := by exact
--   (Int.mul_eq_mul_right_iff hq).mpr h

lemma sum_of_squares_descent (N : ℤ) (h : SumOfSquares N) (q : ℕ)
  (hq : PrimeSumOfSquares q ∧ ↑q ∣ N) :
  (SumOfSquares (N / q)) := by
  obtain ⟨a, a_bound, b, b_bound, ab_coprime, hab⟩ := h
  have qprime : (Nat.Prime q) := by
    obtain ⟨⟨qprime, _⟩, _⟩ := hq
    exact qprime
  -- therefore we should have q divides (xb - ay) (xb + ay)
  -- the wlog argument in the book relies on the ability to switch x and y
  -- around which we can't do if we've already extracted them.
  have exists_d : ∃x > 0, ∃y > 0, ∃d > 0, x^2 + y^2 = (q : ℤ) ∧ q * d = x * b - a * y := by
    obtain ⟨⟨_, x, x_bound, y, y_bound, hxy⟩, qdiv⟩ := hq
    have q_div : ↑q ∣ (x * b - a * y) * (x * b + a * y) := by
      rw [show (x * b - a * y) * (x * b + a * y) = x^2 * N - a^2 * q by
        calc (x * b - a * y) * (x * b + a * y) = x^2 * b^2 - a^2 * y^2 := by ring
           _ = x^2 * (a^2 + b^2) - a^2 * (x^2 + y^2) := by ring
           _ = x^2 * N - a^2 * q := by rw [hab, hxy]]
      exact Int.dvd_sub (Int.dvd_mul_of_dvd_right qdiv) (Int.dvd_mul_left (a ^ 2) ↑q)
    have q_div_or : ↑q ∣ x * b - a * y ∨ ↑q ∣ x * b + a * y := by
      exact Int.Prime.dvd_mul' qprime q_div
    -- now we can do cases based on negative/positive so that we can find that
    -- positive d, and we can switch x/y/neg x,neg y around etc.
    sorry
  obtain ⟨x, x_bound, y, y_bound, d, d_bound, hxy, hd⟩ := exists_d
  have xy_coprime : x.gcd y = 1 := prime_sumofsquares_coprime qprime x_bound y_bound hxy
  have x_div_a_plus_dy_rel : (a + d * y) * y = x * (b - d * x) := by
    calc (a + d * y) * y = a * y + d * y^2 := by ring
              _              = x * b - d * q + d * y^2 := by linarith [hd]
              _              = x * b - d * (x^2 + y^2) + d * y^2 := by rw [hxy]
              _              = x * (b - d * x) := by ring
  have claim : x ∣ (a + d * y) := by
    refine Int.dvd_of_dvd_mul_left_of_gcd_one ?_ xy_coprime
    use (b - d * x)
  have : ∃c > 0, a + d * y = c * x := by
    obtain ⟨c', hc⟩ := claim
    rcases (Int.lt_trichotomy c' 0) with lt | impossible | gt
    · nlinarith
    · nlinarith
    · exact ⟨c', by omega, by linarith [hc]⟩
  obtain ⟨c, c_bound, hc⟩ := this
  have hd : b = d * x + c * y := by
    -- this is supposed to follow by from cxy = (a + dy)y = xb - dx^2
    -- I don't really understand why however.
    -- OK so cxy = xb - dx^2 -> cy = b - dx.  Easy enough
    rw [hc,
        show c * x * y = x * (c * y) by ring,
        Int.mul_eq_mul_left_iff (by omega)] at x_div_a_plus_dy_rel
    linarith [x_div_a_plus_dy_rel]
  refine ⟨c, by omega, d, by omega, ?_, ?_⟩
  · rw [hd] at ab_coprime
    -- a + d * y = c * x
    rw [show a = c * x - d * y by omega] at ab_coprime
    apply relprime_lemma ab_coprime
  · refine Int.eq_ediv_of_mul_eq_right ?_ ?_
    · refine Int.ofNat_ne_zero.mpr ?_
      apply Nat.Prime.ne_zero qprime
    · calc ↑q * (c ^ 2 + d ^ 2) = (x^2  + y^2) * (c^2 + d^2) := by rw [hxy]
            _ = (c * x - d * y)^2 + (d * x + c * y)^2 := by ring
            _ = a^2 + b^2 := by nlinarith [hc, hd]
      exact hab
