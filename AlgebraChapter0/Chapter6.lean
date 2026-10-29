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
-- of ideals Ann(m), as m ranges over the nonzero elements of M. Prove that the
-- maximal elements in this family are prime ideals of R. Conclude that if R. is
-- Noetherian, then AuR (M) #ø

end Question6


end Section4
