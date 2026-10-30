import Mathlib

/-! Chapter 6: Linear Algebra -/

section Section4

section Question5

theorem annihilator_iff_quotient_embeds {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (I : Ideal R) :
    (∃ m : M, Ideal.torsionOf R M m = I) ↔
      ∃ f : (R ⧸ I) →ₗ[R] M, Function.Injective f := by
  constructor
  · intro ⟨m, hm⟩
    -- multiply by m
    set φ : R →ₗ[R] M := LinearMap.toSpanSingleton R M m
    -- example {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    --   (r : R) (m : M) : (LinearMap.toSpanSingleton R M m) r = r • m := by
    --     simp
    have hφ : I ≤ φ.ker := by
        intro r hr
        rw [LinearMap.mem_ker]
        unfold φ
        simp only [LinearMap.toSpanSingleton_apply]
        rwa [← Ideal.mem_torsionOf_iff, hm]
    refine ⟨I.liftQ φ hφ, ?_⟩
    rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
    change φ r = 0 at hx
    rwa [Ideal.Quotient.eq_zero_iff_mem, ← hm, Ideal.mem_torsionOf_iff]
  · intro ⟨φ, hφ⟩
    refine ⟨φ 1, ?_⟩
    ext r
    rw [Ideal.mem_torsionOf_iff, <- map_smul, φ.map_eq_zero_iff hφ]
    simp [Algebra.smul_def, Ideal.Quotient.eq_zero_iff_mem]

end Question5

section Question6

-- Let M be a module over a commutative ring R, and consider the family
-- of ideals Ann(m), as m ranges over the nonzero elements of M.

-- Prove that the maximal elements in this family are prime ideals of R.
theorem maximal_annihilator_isPrime {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (I : Ideal R)
    (hI : Maximal (fun J : Ideal R => ∃ m : M, m ≠ 0 ∧ Ideal.torsionOf R M m = J) I) :
    I.IsPrime := by
  rw [@Ideal.isPrime_iff]
  obtain ⟨m, ⟨mneq0, rfl⟩⟩ := Maximal.prop hI
  constructor
  · rw [Ne, Ideal.torsionOf_eq_top_iff]
    trivial
  · intro a b hab
    by_cases ha : (a • m = 0)
    · left
      rwa [@Ideal.mem_torsionOf_iff]
    · right
      have hle : Ideal.torsionOf R M m ≤ Ideal.torsionOf R M (a • m) := by
        intro r hr
        rw [Ideal.mem_torsionOf_iff, smul_comm]
        simp_all only [ne_eq, Ideal.mem_torsionOf_iff, smul_zero]
      have heq := Maximal.eq_of_le hI ⟨a • m, ha, rfl⟩ hle
      rw [heq, @Ideal.mem_torsionOf_iff, smul_comm, <- smul_assoc]
      exact hab

-- Conclude that if R is Noetherian, then Ass_R(M) ≠ 0
theorem exists_associated_prime {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [IsNoetherianRing R] [Nontrivial M] :
    ∃ P : Ideal R, P.IsPrime ∧ ∃ m : M, Ideal.torsionOf R M m = P := by
  -- This uses Zorn's Lemma
  -- Argument: Ann(m) is defined for all m - and always includes 0 (so nonempty)
  -- By Zorn's Lemma there is a maximal element to Ann(m) - part 1 gives that
  -- it is prime.
  let F : Ideal R → Prop := fun P => ∃ m : M, m ≠ 0 ∧ Ideal.torsionOf R M m = P
  obtain ⟨m, hm⟩ := exists_ne (0 : M)
  obtain ⟨P, -, hP⟩ := exists_maximal_ge_of_wellFoundedGT F (Ideal.torsionOf R M m) ⟨m, hm, rfl⟩
  exists P
  constructor
  · apply maximal_annihilator_isPrime P hP
  · obtain ⟨mp, ⟨_, rfl⟩⟩ := hP.prop
    exists mp

end Question6


end Section4
