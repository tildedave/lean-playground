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

example {x y : ℕ} (h : ↑x ∣ ↑y) : (x ∣ y) := by exact (Nat.ModEq.dvd_iff rfl h).mp h

lemma sum_of_squares_descent (N : ℤ) (h : SumOfSquares N) (q : ℕ)
  (hq : Nat.Prime q ∧ (∃ x > 0, ∃ y > 0, x ^ 2 + y ^ 2 = (q : ℤ)) ∧ ↑q ∣ N) :
  (SumOfSquares (N / q)) := by
  obtain ⟨a, a_bound, b, b_bound, ab_coprime, hab⟩ := h
  obtain ⟨qprime, ⟨x, x_bound, y, y_bound, hxy⟩, qdiv⟩ := hq
  -- therefore we should have q divides (xb - ay) (xb + ay)
  have q_div : ↑q ∣ (x * b - a * y) * (x * b + a * y) := by sorry
  have xy_coprime : x.gcd y = 1 := by
    -- x and y have to be coprime or else q has a nontrivial divisor.
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
        rw [hxy] at this
        exact Int.ofNat_dvd.mp this
      rw [Nat.dvd_prime qprime] at this
      rcases this with eq_1 | eq_p
      · tauto
      · sorry
  have q_div_or : ↑q ∣ x * b - a * y ∨ ↑q ∣ x * b + a * y := by
    exact Int.Prime.dvd_mul' qprime q_div
  -- some wlog stuff I don't know how to fix here
  wlog h : ↑q ∣ x * b - a * y
  -- rcases q_div_or with left | right
  · sorry
    -- need to show this is the same logic, but it requires a different
    -- choice of a/b :/  we can crunch through with some duplication certainly
  · obtain ⟨d, hd⟩ := h
    have d_bound : d > 0 := by sorry
    have claim : x ∣ (a + d * y) := by
      refine Int.dvd_of_dvd_mul_left_of_gcd_one ?_ xy_coprime
      use (b - d * x)
      calc (a + d * y) * y = a * y + d * y^2 := by ring
            _              = x * b - d * q + d * y^2 := by linarith [hd]
            _              = x * b - d * (x^2 + y^2) + d * y^2 := by rw [hxy]
            _              = x * (b - d * x) := by ring
    have : ∃c > 0, a + d * y = c * x := by
      obtain ⟨c', hc⟩ := claim
      rcases (Int.lt_trichotomy c' 0) with lt | impossible | gt
      · nlinarith
      · nlinarith
      · exact ⟨c', by omega, by linarith [hc]⟩
    obtain ⟨c, c_bound, hc⟩ := this
    refine ⟨c, by omega, d, by omega, ?_, ?_⟩
    · sorry -- show c/d gcd is 1
    · refine Int.eq_ediv_of_mul_eq_right ?_ ?_
      · refine Int.ofNat_ne_zero.mpr ?_
        apply Nat.Prime.ne_zero qprime
      · have hd : b = d * x + c * y := by sorry
        calc ↑q * (c ^ 2 + d ^ 2) = (x^2  + y^2) * (c^2 + d^2) := by rw [hxy]
             _ = (c * x - d * y)^2 + (d * x + c * y)^2 := by ring
             _ = a^2 + b^2 := by nlinarith [hc, hd]
        exact hab
