import Mathlib.Algebra.Exact.Basic
import Mathlib.Algebra.Ring.Opposite
import Mathlib.Basic.Real.Basic
import Mathlib.Data.Matrix.Basic

/-! Chapter 3 -/

/-! Section 5 -/
section Section5

variable {R : Type*} [Ring R]

namespace Question1

/-- Aluffi III.5.1 -/
theorem exercise5_1_pt1 (R : Type*) [Ring R] :
    (∃ e : R ≃+* Rᵐᵒᵖ, ⇑e = MulOpposite.op) ↔ ∀ a b : R, a * b = b * a := by
    constructor
    · intro ⟨e, he⟩
      have hinv : ∀ x : R, e.symm (MulOpposite.op x) = x := by
        intro x
        rw [← he]
        exact e.symm_apply_apply x
      intro a b
      open MulOpposite in
      calc a * b = e.symm (op a) * e.symm (op b) := by rw [hinv, hinv]
        _ = e.symm (op a * op b) := (map_mul e.symm (op a) (op b)).symm
        _ = e.symm (op (b * a)) := by rw [op_mul]
        _ = b * a := hinv (b * a)
    · intro hcomm
      open MulOpposite in
      refine ⟨{ toFun := op
                invFun := unop
                left_inv := ?_
                right_inv := ?_
                map_mul' := ?_
                map_add' := ?_ }, rfl⟩
      · exact Function.RightInverse.leftInverse (congrFun rfl)
      · exact Function.LeftInverse.rightInverse (congrFun rfl)
      · intro x y; rw [hcomm]; simp
      · intro x y; simp

theorem exercise5_1_pt2 (n : ℕ) :
  Nonempty (Matrix (Fin n) (Fin n) ℝ ≃+* (Matrix (Fin n) (Fin n) ℝ)ᵐᵒᵖ) := by
  refine ⟨{ toFun := fun A => MulOpposite.op A.transpose
            invFun := fun B => (MulOpposite.unop B).transpose
            left_inv := ?_
            right_inv := ?_
            map_mul' := ?_
            map_add' := ?_ }⟩
  · exact Function.RightInverse.leftInverse (congrFun rfl)
  · exact Function.LeftInverse.rightInverse (congrFun rfl)
  · simp
  · simp

-- M is a right module, define a left action

open scoped RightActions

/-- Aluffi III.5.1 -/
@[instance_reducible]
def exercise5_1_pt3a {M : Type*} [AddCommGroup M] [Module Rᵐᵒᵖ M]
    (e : R ≃+* Rᵐᵒᵖ) : Module R M where
  smul a x := (e a) •> x
  one_smul b := show (e 1) •> b = b by simp
  mul_smul a b x := by
    change e (a * b) •> x = e a •> (e b •> x)
    rw [map_mul]
    exact mul_smul (e a) (e b) x
  smul_zero b := MulActionWithZero.smul_zero (e b)
  smul_add a x y := show (e a) • (x + y) = (e a) • x + (e a) • y by simp
  add_smul a b x :=
    show e (a + b) •> x = (e a) •> x + (e b) •> x
    by simp [map_add, Module.add_smul]
  zero_smul m := show (e 0) •> m = 0 by simp

-- N is a left-module, define a right action

-- seems like we could

/-- Aluffi III.5.1 -/
@[instance_reducible]
def exercise5_1_pt3b {N : Type*} [AddCommGroup N] [Module R N]
    (e : R ≃+* Rᵐᵒᵖ) : Module (Rᵐᵒᵖ) N :=
  let einv := e.symm
  { smul a x := (einv a) •> x
    one_smul b := show (einv 1) •> b = b by simp
    mul_smul a b x := by
        change einv (a * b) •> x = einv a •> (einv b •> x)
        rw [map_mul]
        exact mul_smul (einv a) (einv b) x
    smul_zero b := MulActionWithZero.smul_zero (einv b)
    smul_add a x y := show (einv a) • (x + y) = (einv a) • x + (einv a) • y by simp
    add_smul a b x :=
        show einv (a + b) •> x = (einv a) •> x + (einv b) •> x
        by simp [map_add, Module.add_smul]
    zero_smul m := show (einv 0) •> m = 0 by simp }

end Question1

-- 5.2 is sort of inconvenient to state so we won't do it

section Question3

variable {M : Type*} [AddCommGroup M] [Module R M]
theorem exercise5_3_pt1 : ∀ (m : M), (0 : R) • m = 0 := by
    intro m
    rw [<- add_neg_cancel (1 : R), add_smul, neg_smul]
    apply add_neg_cancel


theorem exercise5_3_pt2 : ∀ (m : M), (-1 : R) • m = -m := by
    intro m
    simp

end Question3

section Question4

variable {M : Type*}

def Simple (R M : Type*) [Ring R] [AddCommGroup M] [Module R M] : Prop :=
  Nontrivial M ∧ ∀ P : Submodule R M, P = ⊥ ∨ P = ⊤

variable {R : Type*} [Ring R]
variable {M : Type*} [AddCommGroup M] [Module R M]
variable {N : Type*} [AddCommGroup N] [Module R N]

-- Schur's Lemma
theorem exercise5_4 (φ : M →ₗ[R] N) (hm : Simple R M) (hn : Simple R N) :
    φ = 0 ∨ Function.Bijective φ := by
    have hker : LinearMap.ker φ = ⊥ ∨ LinearMap.ker φ = ⊤ := hm.2 (LinearMap.ker φ)
    rcases hker with hk | hk
    · have hrange : LinearMap.range φ = ⊥ ∨ LinearMap.range φ = ⊤ := hn.2 (LinearMap.range φ)
      rcases hrange with hr | hr
      · left
        exact LinearMap.range_eq_bot.mp hr
      · right
        exact ⟨LinearMap.ker_eq_bot.mp hk, LinearMap.range_eq_top.mp hr⟩
    · left
      simp_all only [LinearMap.ker_eq_top]

end Question4

section Question5

variable {R : Type*} [CommRing R]
variable {M : Type*} [AddCommGroup M] [Module R M]

@[simps]
def evalOne : (R →ₗ[R] M) →ₗ[R] M where
  toFun ψ := ψ 1
  map_add' := by intros; rw [LinearMap.add_apply]
  map_smul' := by simp

@[simps]
def evalOneInv : M →ₗ[R] (R →ₗ[R] M) where
  toFun m := {
    toFun r := r • m
    map_add' := fun x y ↦ Module.add_smul x y m
    map_smul' := fun m_2 x ↦ IsScalarTower.smul_assoc m_2 x m
  }
  map_add' := by
    intros
    ext ; simp
  map_smul' := by
    intro x y
    ext ; simp

-- no longer needed but keeping it around
lemma linearMap_apply_eq_smul_one (φ : R →ₗ[R] M) (x : R) : φ x = x • φ 1 := by
  rw [← map_smul, smul_eq_mul, mul_one]

def exercise_hom_R_M : (R →ₗ[R] M) ≃ₗ[R] M :=
  LinearEquiv.ofLinearMap evalOne evalOneInv (by ext ; simp) (by ext ; simp)

end Question5

section Question6

variable {G : Type*} [AddCommGroup G]

-- Argument
-- A Q-vector space on G is just a map from Q to Hom(ab)(G)
theorem exercise5_6' : Subsingleton (Module ℚ G) := by
  constructor
  intro M N
  -- alpha and beta are the ℚ-vector spaces, represented by maps from
  -- Q into the hom ring of the group
  set alpha := @Module.toAddMonoidEnd ℚ G _ _ M
  set beta := @Module.toAddMonoidEnd ℚ G _ _ N
  -- iota is _the_ map from Z into Q
  set iota := Int.castRingHom ℚ
  -- of course, alpha.comp iota = beta.comp iota, since Z -> Q is unique
  have composed_maps_are_equal := RingHom.ext_int (alpha.comp iota) (beta.comp iota)
  -- casting things
  have : (∀ m : ℤ, alpha.comp iota m = beta.comp iota m) := by intros ; rw [composed_maps_are_equal]
  have h_int : ∀ m : ℤ, alpha m = beta m := by
    intro m
    exact this m
  ext q g
  change alpha q g = beta q g
  -- If monoid with zero homs f and g from ℚ agree on the integers then they are equal.
  rw [MonoidWithZeroHomClass.ext_rat' h_int]

end Question6

end Section5



/-! Section 7 -/
section Section7

variable {R : Type*} [CommRing R]
variable {Z : Type*} [AddCommGroup Z] [Module R Z] [Subsingleton Z]
variable {M : Type*} [AddCommGroup M] [Module R M]

lemma zeromap_injective
    {M' : Type*} [AddCommGroup M'] [Module R M']
    (f : Z →ₗ[R] M) (g : M →ₗ[R] M') (hexact : Function.Exact f g) :
    Function.Injective g := by
    rw [injective_iff_map_eq_zero]
    intro a ha
    obtain ⟨z, rfl⟩ := (hexact a).mp ha
    rw [Subsingleton.elim z 0]
    apply map_zero

lemma surjective_zeromap
    {M' : Type*} [AddCommGroup M'] [Module R M']
    (f : M →ₗ[R] M') (g : M' →ₗ[R] Z) (hexact : Function.Exact f g) :
    Function.Surjective f := by
    intro b
    exact (hexact b).mp (Subsingleton.eq_zero (g b))

-- 7.1
theorem exercise_7_1
    (f : Z →ₗ[R] M) (φ : M →ₗ[R] Z) (hexact : Function.Exact f φ) :
    Subsingleton M := by
    constructor
    intro a b
    apply zeromap_injective f φ hexact
    exact Subsingleton.elim (φ a) (φ b)

-- 7.2
noncomputable def exercise_7_2
    {Z M M' Z' : Type*} [AddCommGroup Z] [Module R Z] [Subsingleton Z]
    [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module R M']
    [AddCommGroup Z'] [Module R Z'] [Subsingleton Z']
    (f : Z →ₗ[R] M) (ψ : M →ₗ[R] M') (φ : M' →ₗ[R] Z')
    (hM : Function.Exact f ψ) (hM' : Function.Exact ψ φ) :
    M ≃ₗ[R] M' :=
    LinearEquiv.ofBijective ψ
        ⟨zeromap_injective f ψ hM,
         surjective_zeromap ψ φ hM'⟩

end Section7
