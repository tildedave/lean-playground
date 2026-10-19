import Mathlib
import Mathlib.Tactic
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.FieldTheory.PrimitiveElement

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

-- would like to simplify this to improve future arguments, for now nothing
lemma exists_quadratic_of_finrank_eq_two (K : Type*) [Field K] [NumberField K]
    (hK : Module.finrank ℚ K = 2) :
    ∃ x : K, ℚ⟮x⟯ = ⊤ ∧ ∃ p q : ℚ, x ^ 2 + p * x + q = 0 := by sorry

-- geez
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
