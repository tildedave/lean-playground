import Mathlib

/-! Chapter 8: Linear Algebra, reprise -/

/- Section 2 -/

section Section2

section Question5

open TensorProduct

-- let us learn the mathlib verbiage
-- submonoid = multiplicative set (thanks guys)
variable {R : Type*} [CommRing R] (S : Submonoid R)
  (M : Type*) [AddCommGroup M] [Module R M]

-- could do (TensorProduct.mk R M (Localization S)).flip 1 instead
@[simps]
def m_inj {S : Submonoid R} {M : Type*} [AddCommGroup M] [Module R M] := ({
    toFun m := m ⊗ₜ 1,
    map_add' x y := add_tmul x y 1
    map_smul' m x := by trivial
} : M →ₗ[R] M ⊗[R] Localization S)

def s_invertible {S : Submonoid R} {M : Type*} [AddCommGroup M] [Module R M]
    (s : S) : (Module.End R (M ⊗[R] Localization S)) :=
    (LinearMap.mulLeft R (Localization.mk 1 s)).lTensor M

@[simp] theorem s_invertible_tmul {S : Submonoid R} {M : Type*} [AddCommGroup M] [Module R M]
    (s : S) (m : M) (y : Localization S) :
    (s_invertible s) (m ⊗ₜ y) = m ⊗ₜ (Localization.mk 1 s * y) := rfl

-- j is a bilinear map from M -> N -> P that gets lifted to tensor product
-- we have to give its definition here, the proofs show it is bilinear
noncomputable def j {S : Submonoid R} {M : Type*} [AddCommGroup M] [Module R M]
  : (M →ₗ[R] Localization S →ₗ[R] LocalizedModule S M) :=
  LinearMap.mk₂ R (fun m x => x • LocalizedModule.mk m 1)
    (fun x y s => by
      rw [<- smul_add, LocalizedModule.mk_add_mk]
      simp only [one_smul, mul_one])
    (fun r m s => by rw [<- LocalizedModule.smul'_mk, smul_comm])
    (fun m s1 s2 => add_smul _ _ _)
    (fun r m s => smul_assoc _ _ _)

-- Claude suggests this to make the identity proofs easier
@[simp] theorem j_apply {S : Submonoid R} {M : Type*} [AddCommGroup M] [Module R M]
    (m : M) (y : Localization S) : j m y = y • LocalizedModule.mk m (1 : S) := rfl

-- Claude suggested this as a way to clean up the left/right inverse proofs,
-- makes sense
/-- `s⁻¹ • (m ⊗ 1) = m ⊗ 1/s`, for any proof that `s` acts invertibly. -/
@[simp] theorem inv_tmul_one (m : M) (s : S)
    (h : IsUnit ((algebraMap R (Module.End R (M ⊗[R] Localization S))) s)) :
    (↑h.unit⁻¹ : Module.End R (M ⊗[R] Localization S)) (m ⊗ₜ 1) = m ⊗ₜ Localization.mk 1 s := by
  rw [Module.End.algebraMap_isUnit_inv_apply_eq_iff, ← TensorProduct.tmul_smul,
    Localization.smul_mk, smul_eq_mul, mul_one, Localization.mk_self]

noncomputable def localizedModuleEquivTensor
  : LocalizedModule S M ≃ₗ[R] M ⊗[R] Localization S := by
  -- we're going to prove this by lifted maps between S M -> M ⊗[R] Localization S
  -- and the reverse
  refine LinearEquiv.ofLinearMap
    (LocalizedModule.lift S m_inj ?hunit)
    (TensorProduct.lift j)
    ?left ?right
  -- hunit - must show M ⊗[R] Localization S is inverted by s_intervible, so
  -- that a universal map from the localization exists
  case hunit =>
    intro s
    rw [isUnit_iff_exists]
    refine ⟨s_invertible s, ?_, ?_⟩ <;> (
      rw [Module.End.mul_eq_comp]
      ext x s'
      simp only [AlgebraTensorModule.curry_apply, LinearMap.restrictScalars_self, curry_apply,
        LinearMap.coe_comp, Function.comp_apply, s_invertible_tmul, Module.algebraMap_end_apply,
        Module.End.one_apply, map_smul]
      rw [<- TensorProduct.tmul_smul]
      congr 1
      rw [<- smul_mul_assoc, Localization.smul_mk, smul_eq_mul, mul_one, Localization.mk_self, one_mul]
    )
  case left =>
    -- TensorProduct.ext', TensorProduct.lift.tmul, LocalizedModule.lift_mk
    apply TensorProduct.ext'
    intro m s
    simp only [LinearMap.coe_comp, Function.comp_apply, lift.tmul, j_apply, LinearMap.id_coe, id_eq]
    induction s using LocalizedModule.induction_on with
    | h r s =>
      simp only [OreLocalization.smul_div_one, LocalizedModule.lift_mk, map_smul, m_inj_apply]
      rw [inv_tmul_one, <- TensorProduct.tmul_smul, Localization.smul_mk, smul_eq_mul, mul_one]
      rfl
  case right =>
    -- time for the same thing in reverse lol
    apply LinearMap.ext
    intro s
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.id_coe, id_eq]
    induction s using LocalizedModule.induction_on with
    | h r s =>
      simp only [LocalizedModule.lift_mk, m_inj_apply]
      rw [inv_tmul_one, TensorProduct.lift.tmul, j_apply, LocalizedModule.mk_smul_mk, one_smul, mul_one]

-- OK well that was a journey.  explicit maps are wild.

end Question5

end Section2
