import Mathlib.Tactic
import Mathlib.Util.Delaborators

-- This is an attempt to re-prove https://github.com/tildedave/coq-sum-of-squares
-- using Lean.

#check Nat.Coprime

def SumOfSquares (a : ℤ) : Prop
  := ∃ p q, p.gcd q = 1 ∧ p^2 + q^2 = a

example {a : ℕ} : (a = 1) ∨ (a ≠ 1) := by exact eq_or_ne a 1

-- Lemma 1.4 Primes of the Form x^2 + nx^2
-- Suppose that N is a sum of two relatively prime squares, and that
-- q = x^2 + y^2 is a prime divisor of N. Then N/q is also a sum of two
-- relatively prime squares.

-- does not force coprime but this is a lemma
def PrimeSumOfSquares (q : ℕ) : Prop
  := Nat.Prime q ∧ (∃ x y, x ^ 2 + y ^ 2 = (q : ℤ))

lemma prime_sumofsquares_coprime {q : ℕ} {x y : ℤ}
  (qprime : Nat.Prime q)
  (hq : x ^ 2 + y ^ 2 = (q : ℤ))
  : x.gcd y = 1 := by
    have q_bound : (1 < q) := by exact Nat.Prime.one_lt qprime
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
      · -- x and y having q as their common divisor means that it looks
        -- something like (qf)^2 + (qg)^2 = q which is obviously silly.
        have q_div_x : ↑q ∣ x := by
          rw [<- eq_p]
          exact Int.gcd_dvd_left x y
        have q_div_y : ↑q ∣ y := by
          rw [<- eq_p]
          exact Int.gcd_dvd_right x y
        obtain ⟨f, hf⟩ := q_div_x
        obtain ⟨g, hg⟩ := q_div_y
        rw [
          show ↑q = (↑q) * (1 : ℤ) by ring,
          hf,
          hg,
          show (↑q * f)^2 + (↑q * g)^2 = ↑q * (↑q * f * f + ↑q * g * g) by ring
        ] at hq
        rw [Int.mul_eq_mul_left_iff (by omega)] at hq
        have : ↑q ∣ (1 : ℤ) := by
          use (f * f + g * g)
          calc (1 : ℤ) = ↑q * f * f + ↑q * g * g := hq.symm
               _ = ↑q * (f * f + g * g) := by ring
        have : q ∣ 1 := Int.ofNat_dvd.mp this
        rw [Nat.dvd_one] at this
        omega

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

lemma natabs_sq {y : ℤ} {n : ℕ} (h : y.natAbs = n) : y^2 = n * n := by
  grind

lemma eq_mult_self_implies_one {a : ℤ} (ha : a ≠ 0) (h : a * a = a) : a = 1 := by
  rw [show a = a * 1 by ring, show a * 1 * (a * 1) = a * a by ring] at h
  rw [Int.mul_eq_mul_left_iff ha] at h
  exact h

lemma prime_sum_of_squares_neq_zero_left {x y : ℤ} {p : ℕ} (pp : Nat.Prime p)
  (h : x ^ 2 + y ^ 2 = p) : x ≠ 0 := by
  intro hx
  rw [hx] at h
  ring_nf at h
  have : y ∣ ↑p := by
    use y
    linarith
  have : y.natAbs ∣ p := by exact Int.ofNat_dvd_right.mp this
  apply (Nat.Prime.eq_one_or_self_of_dvd pp) at this
  rcases this with left | right
  · apply Nat.Prime.ne_one pp
    apply natabs_sq at left; rw [left] at h
    grind
  · apply Nat.Prime.ne_one pp
    apply natabs_sq at right; rw [right] at h
    apply eq_mult_self_implies_one (Int.ofNat_ne_zero.mpr (Nat.Prime.ne_zero pp)) at h
    rw [<- Int.ofNat_inj]
    exact h

lemma sum_of_squares_descent (N : ℤ) (h : SumOfSquares N) (q : ℕ)
  (hq : PrimeSumOfSquares q ∧ ↑q ∣ N) :
  (SumOfSquares (N / q)) := by
  obtain ⟨a, b, ab_coprime, hab⟩ := h
  have qprime : (Nat.Prime q) := by
    obtain ⟨⟨qprime, _⟩, _⟩ := hq
    exact qprime
  -- therefore we should have q divides (xb - ay) (xb + ay)
  -- the wlog argument in the book relies on the ability to switch x and y
  -- around which we can't do if we've already extracted them.  so we need to
  -- extract them all together.
  have exists_d : ∃x y d, x^2 + y^2 = (q : ℤ) ∧ q * d = x * b - a * y := by
    obtain ⟨⟨_, x, y, hxy⟩, qdiv⟩ := hq
    have xy_coprime : x.gcd y = 1 := prime_sumofsquares_coprime qprime hxy
    have q_div : ↑q ∣ (x * b - a * y) * (x * b + a * y) := by
      rw [show (x * b - a * y) * (x * b + a * y) = x^2 * N - a^2 * q by
        calc (x * b - a * y) * (x * b + a * y) = x^2 * b^2 - a^2 * y^2 := by ring
           _ = x^2 * (a^2 + b^2) - a^2 * (x^2 + y^2) := by ring
           _ = x^2 * N - a^2 * q := by rw [hab, hxy]]
      exact Int.dvd_sub (Int.dvd_mul_of_dvd_right qdiv) (Int.dvd_mul_left (a ^ 2) ↑q)
    have q_div_or : ↑q ∣ x * b - a * y ∨ ↑q ∣ x * b + a * y := by
      exact Int.Prime.dvd_mul' qprime q_div
    -- now we can do cases based on negative/positive so that we can find that
    -- q ∣ xb — ay
    rcases q_div_or with left | right
    · obtain ⟨d, hd⟩ := by exact left
      refine ⟨x, y, d, by tauto⟩
    · obtain ⟨d, hd⟩ := by exact right
      refine ⟨x, -y, d, ?_⟩
      constructor <;> grind
  obtain ⟨x, y, d, hxy, hd⟩ := exists_d
  have xy_coprime : x.gcd y = 1 := prime_sumofsquares_coprime qprime hxy
  have x_div_a_plus_dy_rel : (a + d * y) * y = x * (b - d * x) := by
    calc (a + d * y) * y = a * y + d * y^2 := by ring
              _              = x * b - d * q + d * y^2 := by linarith [hd]
              _              = x * b - d * (x^2 + y^2) + d * y^2 := by rw [hxy]
              _              = x * (b - d * x) := by ring
  have claim : x ∣ (a + d * y) := by
    refine Int.dvd_of_dvd_mul_left_of_gcd_one ?_ xy_coprime
    use (b - d * x)
  have : ∃c, a + d * y = c * x := by
    obtain ⟨c', hc⟩ := claim
    refine ⟨c', ?_⟩
    linarith [hc]
  obtain ⟨c, hc⟩ := this
  have hd : b = d * x + c * y := by
    -- this is supposed to follow by from cxy = (a + dy)y = xb - dx^2
    -- I don't really understand why however.
    -- OK so cxy = xb - dx^2 -> cy = b - dx.  Easy enough
    have x_neq_0 : x ≠ 0 := by
      apply prime_sum_of_squares_neq_zero_left qprime hxy
    rw [hc,
        show c * x * y = x * (c * y) by ring,
        Int.mul_eq_mul_left_iff x_neq_0] at x_div_a_plus_dy_rel
    linarith [x_div_a_plus_dy_rel]
  refine ⟨c, d, ?_, ?_⟩
  · rw [hd] at ab_coprime
    -- a + d * y = c * x
    rw [show a = c * x - d * y by omega] at ab_coprime
    apply relprime_lemma ab_coprime
  · refine Int.eq_ediv_of_mul_eq_right ?_ ?_
    · refine Int.ofNat_ne_zero.mpr ?_
      apply Nat.Prime.ne_zero qprime
    · calc ↑q * (c ^ 2 + d ^ 2) = (x^2  + y^2) * (c^2 + d^2) := by rw [hxy]
            _ = (c * x - d * y)^2 + (d * x + c * y)^2 := by ring
            _ = a^2 + b^2 := by grind
      exact hab
