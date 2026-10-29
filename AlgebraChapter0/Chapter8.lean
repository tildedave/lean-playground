import Mathlib

/-! Chapter 8: Linear Algebra, reprise -/

/- Section 2 -/

section Section2

open TensorProduct

-- let us learn the mathlib verbiage
-- submonoid = multiplicative set (thanks guys)
variable {R : Type*} [CommRing R] (S : Submonoid R) (M : Type*) [AddCommGroup M] [Module R M]

-- Claude suggested this as a way to clean up the left/right inverse proofs,
-- makes sense
/-- `s⁻¹ • (m ⊗ 1) = m ⊗ 1/s`, for any proof that `s` acts invertibly. -/
@[simp] theorem inv_tmul_one (m : M) (s : S)
    (h : IsUnit ((algebraMap R (Module.End R (M ⊗[R] Localization S))) s)) :
    (↑h.unit⁻¹ : Module.End R (M ⊗[R] Localization S)) (m ⊗ₜ 1) = m ⊗ₜ Localization.mk 1 s := by
  rw [Module.End.algebraMap_isUnit_inv_apply_eq_iff, ← TensorProduct.tmul_smul,
    Localization.smul_mk, smul_eq_mul, mul_one, Localization.mk_self]

section Question5

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
    induction s with
    | h r s =>
      simp only [OreLocalization.smul_div_one, LocalizedModule.lift_mk, map_smul, m_inj_apply]
      rw [inv_tmul_one, <- TensorProduct.tmul_smul, Localization.smul_mk, smul_eq_mul, mul_one]
      rfl
  case right =>
    -- time for the same thing in reverse lol
    apply LinearMap.ext
    intro s
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.id_coe, id_eq]
    induction s with
    | h r s =>
      simp only [LocalizedModule.lift_mk, m_inj_apply]
      rw [inv_tmul_one, TensorProduct.lift.tmul, j_apply, LocalizedModule.mk_smul_mk, one_smul, mul_one]

-- OK well that was a journey.  explicit maps are wild.

end Question5

section Question6

-- Let N be an S^-1R-module. R-module. Prove that (S^-1 M) ⊗[S^-1R] N ≅ M ⊗[R] N
-- pg 533

variable (N : Type*) [AddCommGroup N] [Module (Localization S) N]
  [Module R N]
  [IsScalarTower R (Localization S) N]

omit [Module R N] [IsScalarTower R (Localization S) N] in
lemma change_of_basis_simple_tensors (m : M) (s : S) (n : N) :
  (LocalizedModule.mk m s) ⊗ₜ[Localization S] n =
  (LocalizedModule.mk m 1) ⊗ₜ[Localization S] (Localization.mk 1 s • n) := by
  have h : LocalizedModule.mk m s = Localization.mk 1 s • LocalizedModule.mk m (1 : S) := by
    rw [LocalizedModule.mk_smul_mk, one_smul, mul_one]
  rw [h, <- TensorProduct.smul_tmul', TensorProduct.tmul_smul]

-- we used the following to prove
--  ← TensorProduct.tmul_smul,
    -- Localization.smul_mk, smul_eq_mul, mul_one, Localization.mk_self]
  -- TensorProduct.smul_tmul'

-- send m / s ⊗ n --> m ⊗ n/s
lemma mk_cancel_left {S : Submonoid R} (n d : S)
  : Localization.mk (↑n) (n * d) = Localization.mk 1 d := by
  rw [Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  exact ⟨1, by push_cast; ring⟩

lemma mk_smul_one {S : Submonoid R} (n d : S) : Localization.mk (↑n • 1) d
  = Localization.mk ↑n d := by
  rw [Submonoid.smul_def, smul_eq_mul, mul_one]


/-- An `S`-scalar on the `M` side cancels against the same factor in the denominator. -/
lemma smul_tmul_cancel {S : Submonoid R} {M : Type*} {N : Type*}
  [AddCommGroup N] [Module (Localization S) N] [Module R N]
  [IsScalarTower R (Localization S) N] [AddCommMonoid M] [Module R M] (x d : S) (a : M) (n : N) :
    (x • a) ⊗ₜ[R] (Localization.mk 1 (x * d) • n) = a ⊗ₜ[R] (Localization.mk 1 d • n) := by
  rw [Submonoid.smul_def, smul_tmul (R' := R), ← smul_assoc, Localization.smul_mk,
    smul_eq_mul, mul_one, mk_cancel_left]

variable {S M N} in
noncomputable def unlocalize : LocalizedModule S M →ₗ[R] N →ₗ[R] M ⊗[R] N :=
  (LinearMap.mk₂ R (fun m n =>
    m.liftOn
    (fun p => (p.1 ⊗ₜ (Localization.mk 1 p.2 • n) : M ⊗[R] N))
    (fun p p' hpp' => by
        -- well-definedness: p ≈ p' means ∃ u, u • p'.2 • p.1 = u • p.2 • p'.1
        obtain ⟨u, hu⟩ := hpp'
        rw [<- mk_cancel_left (u * p.2) p'.2, <- mk_cancel_left (u * p'.2) p.2]
        push_cast
        rw [mul_right_comm u p.2 p'.2]
        --  p.1 ⊗ₜ[R] (Localization.mk (↑u * ↑p'.2) (u * p'.2 * p.2) • n
        -- pull out u / p'.2 now
        -- must move the R stuff to the left
        repeat rw [<- smul_eq_mul]
        repeat rw [<- Localization.smul_mk]
        -- m ⊗ₜ (u • (r/d)) • n = (u * r) • m ⊗ₜ (1/d) • n
        have hint : ∀ (r : R) (d : S) (m : M),
          m ⊗ₜ[R] (((u : R) • Localization.mk r d) • n) =
          (((u : R) * r) • m) ⊗ₜ[R] ((Localization.mk 1 d) • n) := by
          intro r d m
          have move_out : (u : R) • Localization.mk r d =
            ((u : R) * r) • Localization.mk (1 : R) d := by
            repeat rw [Localization.smul_mk]
            simp only [smul_eq_mul, mul_one]
          rw [move_out, smul_assoc, TensorProduct.smul_tmul (R' := R)]
        rw [hint, hint]
        simp only [Submonoid.smul_def, smul_smul] at hu
        rw [hu]))
    (by
      intro m1 m2 n
      induction m1 with
      | h a s =>
      induction m2 with
      | h b t =>
      simp only [LocalizedModule.mk_add_mk, LocalizedModule.liftOn_mk]
      -- (t•a + s•b)/(st) ⊗ n splits, and each scalar cancels into the denominator
      rw [add_tmul, smul_tmul_cancel, mul_comm s t, smul_tmul_cancel])
    (by
      intro c m n
      induction m with
      | h a s =>
      simp only [LocalizedModule.smul'_mk, LocalizedModule.liftOn_mk]
      rfl)
     (by
        intro m n1 n2
        induction m with
        | h a s =>
        simp only [smul_add, LocalizedModule.liftOn_mk]
        rw [tmul_add])
     (by
        intro c m n
        induction m with
        | h a s =>
        simp only [LocalizedModule.liftOn_mk]
        rw [<- tmul_smul, smul_comm]
     ))

lemma add_mk_self (m1 m2 : M) (s : S) :
  LocalizedModule.mk (m1 + m2) s = LocalizedModule.mk m1 s + LocalizedModule.mk m2 s := by
  rw [LocalizedModule.mk_add_mk, ← smul_add, LocalizedModule.mk_cancel_common_left]

variable {M N S} in
noncomputable def localize : M →ₗ[R] N →ₗ[R] LocalizedModule S M ⊗[Localization S] N :=
  (LinearMap.mk₂ R (fun m n => (LocalizedModule.mk m (1 : ↑S)) ⊗ₜ[Localization S] n)
    (fun m1 m2 n => by rw [add_mk_self, add_tmul])
    (fun c m n => by rw [← LocalizedModule.smul'_mk, smul_tmul'])
    (fun m n1 n2 => by rw [tmul_add])
    (fun c m n => by rw [tmul_smul]))

noncomputable def localizationChangeOfBasis
  : LocalizedModule S M ⊗[Localization S] N ≃ₗ[R] M ⊗[R] N := by
  refine LinearEquiv.ofLinearMap
    { toAddHom := (TensorProduct.liftAddHom (R := Localization S)
        (LinearMap.toAddMonoidHom'.comp unlocalize.toAddMonoidHom) ?hf).toAddHom
      map_smul' := ?unlocalize_smul }
    (TensorProduct.lift localize) ?left ?right
  case hf =>
    intro r' m n
    induction r' with
    | H p =>
    induction m with
    | h m' s =>
    simp only [AddMonoidHom.coe_comp, LinearMap.toAddMonoidHom_coe, Function.comp_apply,
      LinearMap.toAddMonoidHom'_apply]
    unfold unlocalize
    simp only [LinearMap.mk₂_apply]
    rw [@LocalizedModule.mk_smul_mk]
    rw [LocalizedModule.liftOn_mk]
    rw [LocalizedModule.liftOn_mk]
    simp only
    rw [TensorProduct.smul_tmul, <- smul_assoc, Localization.smul_mk]
    rw [smul_smul, Localization.mk_mul, mul_comm, smul_eq_mul, mul_one, one_mul]
  case unlocalize_smul =>
    intro m s
    induction s with
    | tmul m' n =>  -- m' is in S^-1M, n is in N
      -- good times
      change _ = m • (unlocalize m') n
      simp only [ZeroHom.toFun_eq_coe, AddMonoidHom.toZeroHom_coe]
      rw [smul_tmul', liftAddHom_tmul]
      change unlocalize (m • m') n = _
      simp only [map_smul, LinearMap.smul_apply]
      | add x y left right => simp_all [smul_add]
  case left =>
    ext m n
    simp only [AlgebraTensorModule.curry_apply, LinearMap.restrictScalars_self, curry_apply,
      LinearMap.coe_comp, LinearMap.coe_mk, AddHom.coe_mk, ZeroHom.toFun_eq_coe,
      AddMonoidHom.toZeroHom_coe, Function.comp_apply, lift.tmul, LinearMap.id_coe, id_eq]
    unfold localize
    unfold unlocalize
    simp only [LinearMap.mk₂_apply, liftAddHom_tmul, AddMonoidHom.coe_comp,
      LinearMap.toAddMonoidHom_coe, Function.comp_apply, LinearMap.toAddMonoidHom'_apply]
    rw [LocalizedModule.liftOn_mk]
    simp only
    rw [Localization.mk_one, one_smul]
  case right =>
    ext t
    simp only [LinearMap.coe_comp, LinearMap.coe_mk, AddHom.coe_mk, ZeroHom.toFun_eq_coe,
      AddMonoidHom.toZeroHom_coe, Function.comp_apply, LinearMap.id_coe, id_eq]
    induction t with
    | tmul m n =>
      simp only [liftAddHom_tmul, AddMonoidHom.coe_comp, LinearMap.toAddMonoidHom_coe,
        Function.comp_apply, LinearMap.toAddMonoidHom'_apply]
      induction m with
      | h m' s =>
      unfold localize
      unfold unlocalize
      simp only [LinearMap.mk₂_apply]
      rw [LocalizedModule.liftOn_mk]
      simp only [lift.tmul, LinearMap.map_smul_of_tower, LinearMap.mk₂_apply]
      rw [TensorProduct.smul_tmul']
      rw [LocalizedModule.mk_smul_mk, one_smul, mul_one]
    | add x y left right => simp_all only [map_add]

end Question6

end Section2
