import Mathlib
import Mathlib.Tactic
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.FieldTheory.PrimitiveElement

/-! Solutions to exercises from Marcus's Number Fields -/

section Chapter2

section Question1

open IntermediateField Polynomial

example (K : Type*) [Field K] [CharZero K] (x : K) (p q : ℚ)
    (hroot : q • (1 : K) + p • x + x ^ 2 = 0) :
    ((p.den * q.den : ℤ) : K) * x ^ 2 + ((p.num * q.den : ℤ) : K) * x
      + ((q.num * p.den : ℤ) : K) = 0 := by
  rw [Rat.smul_def, Rat.smul_def] at hroot
  have hp' : (p : K) * p.den = p.num := by exact_mod_cast Rat.mul_den_eq_num p
  have hq' : (q : K) * q.den = q.num := by exact_mod_cast Rat.mul_den_eq_num q
  push_cast
  linear_combination ((p.den : K) * q.den) * hroot - ((q.den : K) * x) * hp' - (p.den : K) * hq'

-- geez this is pretty intense
-- Marcus Number Fields Chapter 2 Exercise 1(a)
-- "Show every number field of degree 2 over Q is one of the quadratic fields."
theorem quadratic_field_eq_adjoin_sqrt (K : Type*) [Field K] [NumberField K]
    (hK : Module.finrank ℚ K = 2) :
    ∃ m : ℤ, ∃ α : K, α ^ 2 = m ∧ ℚ⟮α⟯ = ⊤ := by
    obtain ⟨x, hx⟩ := Field.exists_primitive_element ℚ K
    have hint : IsIntegral ℚ x := Algebra.IsIntegral.isIntegral x
    have hdeg : (minpoly ℚ x).natDegree = 2 := by
      rw [← IntermediateField.adjoin.finrank hint, hx, IntermediateField.finrank_top', hK]
    have hmonic : (minpoly ℚ x).Monic := minpoly.monic hint
    have hroot : aeval x (minpoly ℚ x) = 0 := minpoly.aeval ℚ x
    rw [aeval_eq_sum_range, hdeg] at hroot
    have h2 : (minpoly ℚ x).coeff 2 = 1 := by
      rw [← hdeg]
      exact hmonic.coeff_natDegree
    simp only [Finset.sum_range_succ, h2] at hroot
    set p := (minpoly ℚ x).coeff 1 with hp
    set q := (minpoly ℚ x).coeff 0 with hq
    refine ⟨(p.num * q.den )^2 - 4 * (p.den * q.den * p.den * q.num), ?_⟩
    refine ⟨2 * p.den * q.den * x + p.num * q.den, ⟨?_, ?_⟩⟩
    · simp only [Finset.sum_range_zero, pow_zero, pow_one, zero_add, Rat.smul_def,
      mul_one] at hroot
      have hp' : (p : K) * p.den = p.num := by exact_mod_cast Rat.mul_den_eq_num p
      have hq' : (q : K) * q.den = q.num := by exact_mod_cast Rat.mul_den_eq_num q
      have hroot' : ((p.den * q.den : ℤ) : K) * x ^ 2 + ((p.num * q.den : ℤ) : K) * x
          + ((q.num * p.den : ℤ) : K) = 0 := by
        push_cast
        linear_combination
          ((p.den : K) * q.den) * hroot - ((q.den : K) * x) * hp' - (p.den : K) * hq'
      push_cast at hroot' ⊢
      linear_combination (4 * (p.den : K) * q.den) * hroot'
    · set α := 2 * (p.den : K) * q.den * x + p.num * q.den with hα
      have hden : (2 * (p.den : K) * q.den) ≠ 0 := by
        simp [p.den_ne_zero, q.den_ne_zero]
      have hx' : x = (α - p.num * q.den) / (2 * p.den * q.den) := by
        rw [hα]; field_simp; ring
      rw [← top_le_iff, ← hx, adjoin_simple_le_iff, hx']
      have hαmem : α ∈ ℚ⟮α⟯ := mem_adjoin_simple_self ℚ α
      refine div_mem (sub_mem hαmem ?_) ?_
      · exact mul_mem (IntermediateField.intCast_mem _ _) (IntermediateField.natCast_mem _ _)
      · exact mul_mem
          (mul_mem (IntermediateField.natCast_mem _ _) (IntermediateField.natCast_mem _ _))
          (IntermediateField.natCast_mem _ _)

-- Marcus Number Fields Chapter 2 Exercise 1(b)
-- Show every ℚ[√m] is distinct, e.g. if √n ∈ ℚ[√m], then m = n

-- need this first
theorem no_sqrt_is_rational {m : ℤ} (hm : m ≠ 1 ∧ Squarefree m)
  : ∀ (b : ℚ), b^2 ≠ m := by
    intro b hm'
    have m_sqfree := hm.2
    -- obtain ⟨m_neq_one, m_sqfree⟩ := hm
    have msq : IsSquare (m : ℚ) := hm' ▸ IsSquare.sq b
    -- alternatively
    -- have msq: IsSquare (m : ℚ) := ⟨b, by rw [← hm, pow_two]⟩
    obtain ⟨r, hr⟩ := Rat.isSquare_intCast_iff.mp msq
    have hu : IsUnit r := m_sqfree r (by rw [hr])
    rcases Int.isUnit_iff.mp hu with rfl | rfl <;> simp_all

lemma sqrt_of_int_is_integral {K : Type*} [Field K] [CharZero K] {m : ℤ} {s : K}
  (hm : Squarefree m) (hm1 : m ≠ 1) (hs : s ^ 2 = m)
  : IsIntegral ℚ s ∧ minpoly ℚ s = X ^ 2 - C (m : ℚ) := by
    constructor
    · refine ⟨X^2 - C (m : ℚ), ?_, ?_⟩
      · exact Polynomial.monic_X_pow_sub (by compute_degree; simp)
      · rw [← aeval_def]; simp [hs]
    · refine (minpoly.eq_of_irreducible_of_monic ?_ ?_ ?_).symm
      · exact X_pow_sub_C_irreducible_of_prime Nat.prime_two (no_sqrt_is_rational ⟨hm1, hm⟩)
      · simp [hs]
      · exact monic_X_pow_sub_C _ two_ne_zero

-- need this second: if you're in a quadratic field, you can be written using the basis element
lemma exists_rat_add_rat_mul_sqrt {K : Type*} [Field K] [CharZero K] {m : ℤ} {s : K}
    (hm : Squarefree m) (hm1 : m ≠ 1) (hs : s ^ 2 = m)
    (hdim : Module.finrank ℚ ℚ⟮s⟯ = 2) {t : K} (ht : t ∈ ℚ⟮s⟯) :
    ∃ p q : ℚ, t = p + q * s := by
    have s_integral := (sqrt_of_int_is_integral hm hm1 hs).1
    set basis := adjoin.powerBasis s_integral
    have hbasis_2 : basis.dim = 2 :=
      by rw [adjoin.powerBasis_dim, ← adjoin.finrank s_integral, hdim]
    obtain ⟨f, hf, hft⟩ := basis.exists_eq_aeval ⟨t, ht⟩
    obtain ⟨q, p, rfl⟩ := exists_eq_X_add_C_of_natDegree_le_one (by omega : f.natDegree ≤ 1)
    refine ⟨p, q, ?_⟩
    have := congrArg Subtype.val hft
    simpa [basis, Algebra.smul_def, add_comm] using this

theorem quadratic_fields_are_unique {K : Type*} [Field K] [CharZero K] {m n : ℤ}
  (hm : Squarefree m) (hm1 : m ≠ 1) (hn : Squarefree n) (hn1 : n ≠ 1)
  {s t : K} (hs : s ^ 2 = m) (ht : t ^ 2 = n) (hmem : t ∈ ℚ⟮s⟯) :
  n = m := by
  have hdim : Module.finrank ℚ ℚ⟮s⟯ = 2 := by
    obtain ⟨s_integral, s_minpoly⟩ := (sqrt_of_int_is_integral hm hm1 hs)
    rw [adjoin.finrank s_integral, s_minpoly, natDegree_X_pow_sub_C]
  obtain ⟨p, q, texpr⟩ := (exists_rat_add_rat_mul_sqrt hm hm1 hs hdim hmem)
  -- OK write t = p + qs by previous lemma.  therefore n = t^2 = p^2 + 2pqs + q^2m
  have : ↑n = p^2 + 2 * (p * q) * s + q^2 * ↑m := by grind
  by_cases h : (↑p : K) * (↑q : K) = ↑0
  · simp only [h, mul_zero, zero_mul, add_zero] at this
    obtain hp | hq := mul_eq_zero.mp h
    · simp only [hp, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_add] at this
      have hQ : (n : ℚ) = q ^ 2 * m := by exact_mod_cast this
      have hZ : (q.den : ℤ)^2 * n = (q.num)^2 * m := by
        have : (q.den : ℚ)^2 * (n : ℚ) = (q.num : ℚ)^2 * (m : ℚ) := by
          rw [← Rat.num_div_den q] at hQ
          have : (q.den : ℚ) ≠ 0 := by exact_mod_cast q.den_ne_zero
          rw [hQ]
          field_simp
        exact_mod_cast this
      have : q.den = 1 := by
        -- q divides m, so q in a unit
        have hint : IsCoprime ↑(q.den ^ 2) (q.num ^ 2) := by
          push_cast
          exact IsCoprime.pow (Rat.isCoprime_num_den q).symm
        have hdvd : (q.den  : ℤ)^2 ∣ q.num^2 * m := by
          exact Dvd.intro n hZ
        have : IsUnit (q.den : ℤ) := by
          apply hm
          rw [<- pow_two]
          apply IsCoprime.dvd_of_dvd_mul_left hint
          exact hdvd
        exact ZMod.eq_one_of_isUnit_natCast this
      -- because q.den = 1 then q.num = 1 too
      simp only [this, Nat.cast_one, one_pow, one_mul] at hZ
      have : IsUnit (q.num : ℤ) := by
        apply hn
        rw [<- pow_two]
        symm at hZ
        exact Dvd.intro m hZ
      have qnumsq_one := by exact Int.isUnit_sq this
      simp only [qnumsq_one, one_mul] at hZ
      exact hZ
    · exfalso
      simp only [hq, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul,
        add_zero] at this
      -- so p.num and p.den are units
      have hN : (p.den : ℤ)^2 * n = p.num^2 := by
        have hQ : (n : ℚ) = p ^ 2 := by exact_mod_cast this
        have hZ : (p.den : ℤ) ^ 2 * n = p.num ^ 2 := by
          have : (p.den : ℚ) ^ 2 * n = (p.num : ℚ) ^ 2 := by
            rw [← Rat.num_div_den p] at hQ
            have : (p.den : ℚ) ≠ 0 := by exact_mod_cast p.den_ne_zero
            rw [hQ]
            field_simp
          exact_mod_cast this
        exact_mod_cast hZ
      have : IsUnit (p.num : ℤ) := by
        -- have : IsCoprime p.num p.den := Rat.isCoprime_num_den p
        have : p.num ^ 2 ∣ (p.den : ℤ)^2 * n := by
          simp_all only [ne_eq, zero_mul, add_zero, SubfieldClass.ratCast_mem, mul_zero,
            Rat.cast_eq_zero, dvd_refl]
        apply hn
        rw [← pow_two]
        exact IsCoprime.dvd_of_dvd_mul_left (IsCoprime.pow (Rat.isCoprime_num_den p)) this
      rw [Int.isUnit_sq this] at hN
      have hd : (p.den : ℤ) ^ 2 = 1 := Int.eq_one_of_mul_eq_one_right (by positivity) hN
      rw [hd, one_mul] at hN
      exact hn1 hN
  · exfalso
    set u := ((n : ℚ) - p^2 - q ^ 2 * (m : ℚ)) / (2 * p * q) with hu
    apply no_sqrt_is_rational ⟨hm1, hm⟩ u
    rw [hu]
    have : s = (↑n - ↑p^2 - ↑q ^ 2 * ↑m) / (2 * p * ↑q) := by grind
    rw [this] at hs
    exact_mod_cast hs

end Question1

section Question2

open Zsqrtd

/-- The ideal `I = (2, 1 + √-3)` in `ℤ[√-3]`. -/
def I : Ideal (ℤ√(-3)) := Ideal.span {2, 1 + sqrtd}

-- I ≠ (2), but I² = 2I
theorem I_ne_two_and_sq : I ≠ Ideal.span {2} ∧ I ^ 2 = Ideal.span {2} * I := by
  constructor
  · intro span
    have : (1 + sqrtd : ℤ√(-3)) ∈ I := Ideal.subset_span (by simp)
    rw [span, Ideal.mem_span_singleton] at this
    obtain ⟨c, hc⟩ := this
    have hre := congrArg Zsqrtd.re hc
    simp at hre
    omega
  · apply le_antisymm
    · rw [sq]
      unfold I
      rw [Ideal.span_pair_mul_span_pair, Ideal.span_le]
      simp only [Set.insert_subset_iff, Set.singleton_subset_iff, SetLike.mem_coe,
        Ideal.mem_span_singleton_mul]
      refine ⟨?_, ?_, ?_, ?_⟩
      · -- ∃ z ∈ Ideal.span {2, 1 + sqrtd}, 2 * z = 2 * 2
        refine ⟨2, ⟨Ideal.subset_span (by simp), by simp⟩⟩
      · -- ∃ z ∈ Ideal.span {2, 1 + sqrtd}, 2 * z = 2 * (1 + sqrtd)
        refine ⟨1 + sqrtd, ⟨Ideal.subset_span (by simp), by simp⟩⟩
      · -- ∃ z ∈ Ideal.span {2, 1 + sqrtd}, 2 * z = (1 + sqrtd) * 2
        refine ⟨1 + sqrtd, ⟨Ideal.subset_span (by simp), by ring_nf⟩⟩
      · -- ∃ z ∈ Ideal.span {2, 1 + sqrtd}, 2 * z = (1 + sqrtd) * (1 + sqrtd)
        -- 2 * z = (1 + sqrtd) * (1 + sqrtd)
        -- 2 * z = (1 + 2sqrtd - 3) = (2sqrtd - 2) = 2 * (sqrtd - 1)
        refine ⟨sqrtd - 1, ⟨?_, ?_⟩⟩
        · apply Ideal.mem_span_pair.mpr
          refine ⟨-1, 1, by ring⟩
        · ring_nf
          rw [sq, dmuld]
          push_cast
          ring
    · rw [sq]
      exact Ideal.mul_mono_left (Ideal.span_mono (by simp))

lemma mem_I_iff (z : ℤ√(-3)) : z ∈ I ↔ 2 ∣ (z.re + z.im) := by
  unfold I
  rw [Ideal.mem_span_pair]
  constructor
  · rintro ⟨a, b, rfl⟩
    simp
    omega
  · intro ⟨k, hk⟩
    refine ⟨k - z.im, z.im, ?_⟩
    ring_nf
    have : ((2 * ↑k) : ℤ√(-3)) = ↑(2 * k) := by norm_num
    rw [mul_comm, this, ← hk]
    push_cast
    ring_nf
    ext <;> simp

-- OK so now take a b in I, munge through the algebra to see it's right
theorem I_prime : I.IsPrime := by
  rw [Ideal.isPrime_iff, Ideal.ne_top_iff_one, mem_I_iff]
  constructor
  · simp
  · intro x y
    repeat rw [mem_I_iff]
    intro hxy
    have : 2 ∣ (x.re + x.im) * (y.re + y.im) := by
      -- Claude got this
      have key : (x * y).re + (x * y).im = (x.re + x.im) * (y.re + y.im) - 2 * (2 * x.im * y.im) := by
        simp
        ring
      rw [key] at hxy
      exact (dvd_sub_left (dvd_mul_right 2 _)).mp hxy
    apply Prime.dvd_or_dvd (Int.prime_two) this

theorem I_lies_over_two : Ideal.span {2} ≤ I := by
  apply Ideal.span_mono (by simp)

-- I is the unique prime ideal containing (2)
theorem I_unique_prime_over_two :
    ∀ P : Ideal (ℤ√(-3)), P.IsPrime → Ideal.span {2} ≤ P → P = I := by
  -- argument:
  -- OK if you have a prime ideal over 2, 4 must be in it
  -- since 4 is in it, (1 + √−3)(1−√−3) = 4 ∈ P, therefore
  -- one of (1 + √-3), (1 - √3) ∈ P, so P contains 1 + √-3, 2, QED I guess
  intro P hP hP_le
  have two_in_P : (2 : (ℤ√(-3))) ∈ P := by
    simp_all only [Int.reduceNeg, Submodule.span_singleton_le_iff_mem]
  have four_in_P : (4 : (ℤ√(-3))) ∈ P := by
    exact (Submodule.sub_mem_iff_left P two_in_P).mp two_in_P
  have one_plus_sqrtd_in_P : (1 + sqrtd ∈ P) := by
    have : (1 + sqrtd) * (1 - sqrtd) = (4 : ℤ√(-3)) := by
      ring_nf
      rw [sq, dmuld]
      ring
    rw [← this] at four_in_P
    obtain hplus | hminus := hP.mem_or_mem' four_in_P
    · exact hplus
    · -- −1⋅(1−√−3)+2=1 +√−3
      have : ((1 + sqrtd) : ℤ√(-3)) = -1 * (1 - sqrtd) + 2 := by
        ring_nf
      rw [this]
      apply P.add_mem
      · exact Ideal.mul_mem_left P (-1) hminus
      · exact two_in_P
  have I_le_P : I ≤ P := Ideal.span_le.mpr (Set.pair_subset two_in_P one_plus_sqrtd_in_P)
  symm
  apply Ideal.IsMaximal.eq_of_le ?_ (Ideal.IsPrime.ne_top hP) I_le_P
  apply Ideal.isMaximal_iff.mpr
  rw [mem_I_iff]
  constructor
  · simp
  · intro J x I_lt_J hx x_in_J
    rw [mem_I_iff] at hx
    have x_minus_1_in_I : x - 1 ∈ I := by rw [mem_I_iff (x - 1)] ; dsimp; grind
    have x_minus_1_in_J : x - 1 ∈ J := I_lt_J x_minus_1_in_I
    exact (Submodule.sub_mem_iff_right J x_in_J).mp x_minus_1_in_J

end Question2

-- question 3 is just more int/rat munging which I've done a bunch



end Chapter2
