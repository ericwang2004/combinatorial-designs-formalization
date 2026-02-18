import Mathlib.LinearAlgebra.QuadraticForm.Prod
import Mathlib.LinearAlgebra.Reflection

/-!
# Witt Cancellation for Quadratic Forms

This file proves Witt's cancellation theorem for quadratic forms over fields of
characteristic ≠ 2: if q ⊕ q₁ ≅ q ⊕ q₂ then q₁ ≅ q₂.

## Main Definitions

* `qReflection` - Reflection of a quadratic space through a nondegenerate vector
* `qReflectionIsometryEquiv` - A quadratic reflection as an isometry equivalence

## Main Results

* `qReflection_isometry` - Quadratic reflections preserve the quadratic form
* `cancel_one_dim` - One-dimensional cancellation: a·x² ⊕ q₁ ≅ a·x² ⊕ q₂ implies q₁ ≅ q₂
* `witt_cancellation` - Witt's cancellation theorem for quadratic forms
-/

open QuadraticMap LinearMap Module

noncomputable section

variable {F : Type*} [Field F] [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V]
variable {V₀ : Type*} [AddCommGroup V₀] [Module F V₀] [FiniteDimensional F V₀]
variable {V₁ : Type*} [AddCommGroup V₁] [Module F V₁] [FiniteDimensional F V₁]
variable {V₂ : Type*} [AddCommGroup V₂] [Module F V₂] [FiniteDimensional F V₂]

namespace QuadraticForm

/-- The dual functional used to define reflections through a vector -/
def reflectionDual (Q : QuadraticForm F V) (y : V) (_ : Q y ≠ 0) :
    Module.Dual F V :=
  (2 * (Q y)⁻¹) • (associated (R := F) Q y)

/-- The reflection dual applied to its defining vector gives 2 -/
theorem reflectionDual_apply_self (Q : QuadraticForm F V) (y : V) (hy : Q y ≠ 0) :
    reflectionDual Q y hy y = 2 := by
  simp only [reflectionDual, LinearMap.smul_apply, smul_eq_mul]
  rw [QuadraticMap.associated_eq_self_apply]
  field_simp

/-- Reflection of a quadratic space through a nondegenerate vector -/
def qReflection (Q : QuadraticForm F V) (y : V) (hy : Q y ≠ 0) :
    V ≃ₗ[F] V :=
  Module.reflection (reflectionDual_apply_self Q y hy)

/-- The explicit formula for the quadratic reflection -/
theorem qReflection_apply (Q : QuadraticForm F V) (y : V) (hy : Q y ≠ 0) (x : V) :
    qReflection Q y hy x = x - (reflectionDual Q y hy x) • y :=
  Module.preReflection_apply y (reflectionDual Q y hy) x

/-- A quadratic reflection sends y to -y -/
@[simp]
theorem qReflection_apply_self (Q : QuadraticForm F V) (y : V) (hy : Q y ≠ 0) :
    qReflection Q y hy y = -y :=
  Module.reflection_apply_self (reflectionDual_apply_self Q y hy)

/-- Quadratic reflections are involutions -/
theorem qReflection_involutive (Q : QuadraticForm F V) (y : V) (hy : Q y ≠ 0) :
    Function.Involutive (qReflection Q y hy) :=
  Module.involutive_reflection (reflectionDual_apply_self Q y hy)

omit [Invertible (2 : F)] in
private theorem quad_sub_smul_expand (Q : QuadraticForm F V) (x y : V) (c : F) :
    Q (x - c • y) = Q x - c * QuadraticMap.polar (↑Q) x y + c ^ 2 * Q y := by
  have h1 := QuadraticMap.map_add (⇑Q) x (-(c • y))
  have h2 : Q (-(c • y)) = c ^ 2 * Q y := by
    rw [Q.map_neg, Q.map_smul, smul_eq_mul, @_root_.sq]
  have h3 : QuadraticMap.polar (↑Q) x (-(c • y)) = -(c * QuadraticMap.polar (↑Q) x y) := by
    rw [QuadraticMap.polar_neg_right, QuadraticMap.polar_smul_right, smul_eq_mul]
  rw [sub_eq_add_neg, h1, h2, h3]
  ring

private theorem polar_eq_two_mul_associated (Q : QuadraticForm F V) (x y : V) :
    QuadraticMap.polar (↑Q) x y = 2 * associated (R := F) Q x y := by
  have : QuadraticMap.polar (↑Q) x y = 2 • associatedHom F Q x y := by
    rw [two_smul]
    change Q (x + y) - Q x - Q y = associatedHom F Q x y + associatedHom F Q x y
    rw [QuadraticMap.associated_apply]
    simp only [Module.End.smul_def, half_moduleEnd_apply_eq_half_smul,
      invOf_eq_inv, smul_eq_mul]
    field_simp
    ring_nf
  rw [this]
  simp only [associated_apply, Module.End.smul_def, nsmul_eq_mul, Nat.cast_ofNat]

/-- Quadratic reflections preserve the quadratic form -/
theorem qReflection_isometry (Q : QuadraticForm F V) (y : V) (hy : Q y ≠ 0) (x : V) :
    Q (qReflection Q y hy x) = Q x := by
  rw [qReflection_apply]
  set c := reflectionDual Q y hy x
  rw [quad_sub_smul_expand, polar_eq_two_mul_associated]
  simp only [c, reflectionDual, LinearMap.smul_apply, smul_eq_mul]
  rw [QuadraticMap.associated_isSymm F Q x y]
  field_simp
  ring

/-- A quadratic reflection as an isometry equivalence -/
def qReflectionIsometryEquiv (Q : QuadraticForm F V) (y : V) (hy : Q y ≠ 0) :
    Q.IsometryEquiv Q where
  toLinearEquiv := qReflection Q y hy
  map_app' := qReflection_isometry Q y hy

omit [Invertible (2 : F)] in
/-- The parallelogram identity: Q(x+y) + Q(x-y) = 2(Q(x) + Q(y)) -/
theorem four_squares_identity (Q : QuadraticForm F V) (x y : V) :
    Q (x + y) + Q (x - y) = 2 * (Q x + Q y) := by
  have h1 := QuadraticMap.map_add (⇑Q) x y
  have h2 : Q (x - y) = Q x + Q y - QuadraticMap.polar (↑Q) x y := by
    have h2a : Q (x + (-y)) = Q x + Q (-y) + QuadraticMap.polar (↑Q) x (-y) := by
      simp [QuadraticMap.polar]
    rw [sub_eq_add_neg, h2a, Q.map_neg, QuadraticMap.polar_neg_right]
    ring
  rw [h1, h2]; ring

/-- Reflection through x - y sends x to y when Q(x) = Q(y) -/
theorem qReflection_sub_sends_to
    (Q : QuadraticForm F V) (x y : V)
    (heq : Q x = Q y) (hne : Q (x - y) ≠ 0) :
    qReflection Q (x - y) hne x = y := by
  rw [qReflection_apply]
  suffices h : reflectionDual Q (x - y) hne x = 1 by
    rw [h, one_smul, sub_sub_cancel]
  simp only [reflectionDual, LinearMap.smul_apply, smul_eq_mul]
  have h1 : associated (R := F) Q (x - y) x = Q x - associated (R := F) Q y x := by
    rw [map_sub, LinearMap.sub_apply, QuadraticMap.associated_eq_self_apply]
  have h2 : Q (x - y) = 2 * (Q x - associated (R := F) Q y x) := by
    have expand : Q (x - y) = Q x + Q y - QuadraticMap.polar (↑Q) x y := by
      have h2a : Q (x + (-y)) = Q x + Q (-y) + QuadraticMap.polar (↑Q) x (-y) := by
        simp [QuadraticMap.polar]
      rw [sub_eq_add_neg, h2a, Q.map_neg, QuadraticMap.polar_neg_right]; ring
    rw [expand, heq, polar_eq_two_mul_associated,
        QuadraticMap.associated_isSymm F Q x y]
    ring
  rw [h1, h2]
  ring_nf
  field_simp
  simp_all only [associated_apply, ne_eq, mul_eq_zero, not_or, not_false_eq_true, div_self]

/-- Given Q(x) = Q(y) ≠ 0, there exists an isometry sending x to y -/
def exists_isometry_of_eq_value
    (Q : QuadraticForm F V) (x y : V) (heq : Q x = Q y) (hne : Q x ≠ 0) :
    Σ' τ : Q.IsometryEquiv Q, τ x = y := by
  by_cases hxy : Q (x - y) ≠ 0
  · exact ⟨qReflectionIsometryEquiv Q (x - y) hxy, qReflection_sub_sends_to Q x y heq hxy⟩
  · push_neg at hxy
    have hsum : Q (x + y) ≠ 0 := by
      intro habs
      have h4sq := four_squares_identity Q x y
      rw [habs, hxy, zero_add, heq] at h4sq
      have h2ne : (2 : F) ≠ 0 := isUnit_of_invertible (2 : F) |>.ne_zero
      have : Q y + Q y = 0 := by
        rcases mul_eq_zero.mp h4sq.symm with h | h
        · exact absurd h h2ne
        · exact h
      have hQy0 : Q y = 0 := by
        have h2Q : 2 * Q y = 0 := by rw [two_mul]; exact this
        exact (mul_eq_zero.mp h2Q).resolve_left h2ne
      exact hne (heq ▸ hQy0)
    have h_sends_neg : qReflection Q (x + y) hsum x = -y := by
      rw [qReflection_apply]
      suffices h : reflectionDual Q (x + y) hsum x = 1 by
        rw [h, one_smul]; abel
      simp only [reflectionDual, LinearMap.smul_apply, smul_eq_mul]
      have h1 : associated (R := F) Q (x + y) x = Q x + associated (R := F) Q y x := by
        rw [map_add, LinearMap.add_apply, QuadraticMap.associated_eq_self_apply]
      have h2 : Q (x + y) = 2 * (Q x + associated (R := F) Q y x) := by
        have expand : Q (x + y) = Q x + Q y + QuadraticMap.polar (↑Q) x y := by
          simp [QuadraticMap.polar]
        rw [expand, heq, polar_eq_two_mul_associated,
            QuadraticMap.associated_isSymm F Q x y]
        ring
      rw [h1, h2]; field_simp
      simp_all only [ne_eq, associated_apply, mul_eq_zero, not_or, map_add, not_false_eq_true, div_self]
    have hqy : Q y ≠ 0 := heq ▸ hne
    have h_final : qReflection Q y hqy (-y) = y := by
      rw [← qReflection_apply_self Q y hqy, qReflection_involutive Q y hqy y]
    let τ := (qReflectionIsometryEquiv Q (x + y) hsum).trans (qReflectionIsometryEquiv Q y hqy)
    refine ⟨τ, ?_⟩
    change qReflection Q y hqy (qReflection Q (x + y) hsum x) = y
    rw [h_sends_neg, h_final]

/-! ## Cancellation -/

/-- Given an isometry a·x² ⊕ q₁ ≅ a·x² ⊕ q₂, find one that fixes the generator (1, 0) -/
def exists_isometry_fixing_generator
    (q₁ : QuadraticForm F V₁) (q₂ : QuadraticForm F V₂)
    (a : F) (ha : a ≠ 0)
    (φ : ((a • (QuadraticMap.sq (R := F))).prod q₁).IsometryEquiv
         ((a • (QuadraticMap.sq (R := F))).prod q₂)) :
    Σ' ψ : ((a • (QuadraticMap.sq (R := F))).prod q₂).IsometryEquiv
           ((a • (QuadraticMap.sq (R := F))).prod q₂),
      (φ.trans ψ) ((1 : F), (0 : V₁)) = ((1 : F), (0 : V₂)) := by
  let Q₂ := (a • (QuadraticMap.sq (R := F))).prod q₂
  let e₁ : F × V₁ := (1, 0)
  let e₂ : F × V₂ := (1, 0)
  have hval_e₂ : Q₂ e₂ = a := by
    simp [Q₂, e₂, QuadraticMap.prod_apply, QuadraticMap.smul_apply,
          QuadraticMap.sq_apply, map_zero, smul_eq_mul]
  have hval_φe₁ : Q₂ (φ e₁) = a := by
    rw [show Q₂ (φ e₁) = ((a • (QuadraticMap.sq (R := F))).prod q₁) e₁ from φ.map_app e₁]
    simp [e₁, QuadraticMap.prod_apply, QuadraticMap.smul_apply,
          QuadraticMap.sq_apply, map_zero, smul_eq_mul]
  have hne : Q₂ (φ e₁) ≠ 0 := by rw [hval_φe₁]; exact ha
  have heq : Q₂ (φ e₁) = Q₂ e₂ := by rw [hval_φe₁, hval_e₂]
  exact exists_isometry_of_eq_value Q₂ (φ e₁) e₂ heq hne

/-- An isometry fixing the generator restricts to an isometry of the complements -/
def isometry_fixing_generator_restricts
    (q₁ : QuadraticForm F V₁) (q₂ : QuadraticForm F V₂)
    (a : F) (ha : a ≠ 0)
    (ψ : ((a • (QuadraticMap.sq (R := F))).prod q₁).IsometryEquiv
         ((a • (QuadraticMap.sq (R := F))).prod q₂))
    (hfix : ψ ((1 : F), (0 : V₁)) = ((1 : F), (0 : V₂))) :
    q₁.IsometryEquiv q₂ := by
  have polar_pres : ∀ x y : F × V₁,
      QuadraticMap.polar (↑((a • (QuadraticMap.sq (R := F))).prod q₂)) (ψ x) (ψ y) =
      QuadraticMap.polar (↑((a • (QuadraticMap.sq (R := F))).prod q₁)) x y := by
    intro x y
    simp only [QuadraticMap.polar]
    rw [show ψ x + ψ y = ψ (x + y) from (map_add ψ.toLinearEquiv x y).symm]
    rw [ψ.map_app, ψ.map_app, ψ.map_app]
  have fst_zero : ∀ v : V₁, (ψ ((0 : F), v)).1 = 0 := by
    intro v
    have h : QuadraticMap.polar (↑((a • (QuadraticMap.sq (R := F))).prod q₂))
        ((1 : F), (0 : V₂)) (ψ ((0 : F), v)) = 0 := by
      rw [← hfix, polar_pres]; simp [QuadraticMap.polar]
    simp only [QuadraticMap.polar_prod] at h
    simp only [QuadraticMap.polar, QuadraticMap.smul_apply, QuadraticMap.sq_apply,
               map_zero, smul_eq_mul] at h
    rw [zero_add, sub_zero, sub_self, add_zero] at h
    have h2a : 2 * a * (ψ ((0 : F), v)).1 = 0 := by linear_combination h
    have h2ne : (2 : F) ≠ 0 := isUnit_of_invertible (2 : F) |>.ne_zero
    rcases mul_eq_zero.mp h2a with h2z | haf
    · exact absurd (mul_eq_zero.mp h2z |>.resolve_left h2ne) ha
    · exact haf
  let ψ_rest : V₁ →ₗ[F] V₂ :=
    { toFun := fun v => (ψ ((0 : F), v)).2
      map_add' := fun x y => by
        have := congr_arg Prod.snd (map_add ψ.toLinearEquiv ((0 : F), x) ((0 : F), y))
        simpa using this
      map_smul' := fun c x => by
        have := congr_arg Prod.snd (map_smulₛₗ ψ.toLinearEquiv c ((0 : F), x))
        simpa using this }
  have preserves : ∀ v : V₁, q₂ (ψ_rest v) = q₁ v := by
    intro v
    have hψ := ψ.map_app ((0 : F), v)
    simp only [QuadraticMap.prod_apply, QuadraticMap.smul_apply, QuadraticMap.sq_apply,
               smul_eq_mul] at hψ
    simp_rw [fst_zero, mul_zero, zero_add] at hψ
    exact hψ
  have hψ_inj : Function.Injective ψ_rest := by
    intro v₁ v₂ hv
    have h2 : ψ ((0, v₁)) = ψ ((0, v₂)) := Prod.ext (by rw [fst_zero, fst_zero]) hv
    exact congr_arg Prod.snd (ψ.toLinearEquiv.injective h2)
  have hdim : finrank F V₁ = finrank F V₂ := by
    have h1 : finrank F (F × V₁) = finrank F (F × V₂) := ψ.toLinearEquiv.finrank_eq
    simp only [finrank_prod, finrank_self] at h1; omega
  have hψ_surj := (ψ_rest.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hψ_inj
  exact ⟨LinearEquiv.ofBijective ψ_rest ⟨hψ_inj, hψ_surj⟩, fun v => preserves v⟩

/-- One-dimensional cancellation: a·x² ⊕ q₁ ≅ a·x² ⊕ q₂ implies q₁ ≅ q₂ -/
def cancel_one_dim
    (q₁ : QuadraticForm F V₁) (q₂ : QuadraticForm F V₂)
    (a : F) (ha : a ≠ 0)
    (h : ((a • (QuadraticMap.sq (R := F))).prod q₁).IsometryEquiv
         ((a • (QuadraticMap.sq (R := F))).prod q₂)) :
    q₁.IsometryEquiv q₂ := by
  obtain ⟨τ, hτ⟩ := exists_isometry_fixing_generator q₁ q₂ a ha h
  exact isometry_fixing_generator_restricts q₁ q₂ a ha (h.trans τ) hτ

omit [FiniteDimensional F V₁] [FiniteDimensional F V₂] in
/-- Associativity of products of quadratic forms -/
def isometryEquivProdAssoc
    (q₁ : QuadraticForm F V₁) (q₂ : QuadraticForm F V₂) (q₃ : QuadraticForm F V) :
    ((q₁.prod q₂).prod q₃).IsometryEquiv (q₁.prod (q₂.prod q₃)) where
  toLinearEquiv := LinearEquiv.prodAssoc F V₁ V₂ V
  map_app' := by
    intro ⟨⟨x₁, x₂⟩, x₃⟩
    simp [QuadraticMap.prod_apply, add_assoc]

omit [FiniteDimensional F V₁] in
/-- The zero quadratic form is a left identity for products -/
def isometryEquivZeroProd
    (q : QuadraticForm F V₁) :
    ((0 : QuadraticForm F (Fin 0 → F)).prod q).IsometryEquiv q where
  toLinearEquiv := {
    toFun := fun p => p.2
    invFun := fun w => (0, w)
    left_inv := by intro ⟨f, w⟩; simp [Subsingleton.elim f 0]
    right_inv := by intro w; simp
    map_add' := by intros; simp
    map_smul' := by intros; simp
  }
  map_app' := by
    intro ⟨f, w⟩
    simp only [QuadraticMap.prod_apply, QuadraticMap.zero_apply, zero_add]

omit [Invertible (2 : F)] in
private def cancel_zero_dim
    (q₁ : QuadraticForm F V₁) (q₂ : QuadraticForm F V₂)
    (ψ : ((0 : QuadraticForm F F).prod q₁).IsometryEquiv
         ((0 : QuadraticForm F F).prod q₂)) :
    q₁.IsometryEquiv q₂ := by
  suffices key : ∀ (ψ' : ((0 : QuadraticForm F F).prod q₁).IsometryEquiv
      ((0 : QuadraticForm F F).prod q₂)),
      (ψ' ((1 : F), (0 : V₁))).1 ≠ 0 → q₁.IsometryEquiv q₂ by
    by_cases hα : (ψ ((1 : F), (0 : V₁))).1 ≠ 0
    · exact key ψ hα
    · push_neg at hα
      have hu : (ψ ((1 : F), (0 : V₁))).2 ≠ 0 := by
        intro h0
        have h00 : ψ ((1 : F), (0 : V₁)) = (0, 0) := Prod.ext hα h0
        exact one_ne_zero (congr_arg Prod.fst
          (ψ.toLinearEquiv.injective (h00.trans (map_zero ψ.toLinearEquiv).symm)))
      let ⟨ℓ, hℓ_prop⟩ := Classical.indefiniteDescription _
        (Submodule.exists_le_ker_of_notMem (p := ⊥)
          (show (ψ ((1 : F), (0 : V₁))).2 ∉ (⊥ : Submodule F V₂) by rwa [Submodule.mem_bot]))
      let shear_fwd : F × V₂ →ₗ[F] F × V₂ :=
        { toFun := fun p => (p.1 + ℓ p.2, p.2)
          map_add' := fun ⟨c₁, w₁⟩ ⟨c₂, w₂⟩ => by
            ext <;> simp [map_add, add_add_add_comm]
          map_smul' := fun r ⟨c, w⟩ => by
            ext <;> simp [Prod.smul_def, map_smul, smul_eq_mul, mul_add] }
      let shear_bwd : F × V₂ →ₗ[F] F × V₂ :=
        { toFun := fun p => (p.1 - ℓ p.2, p.2)
          map_add' := fun ⟨c₁, w₁⟩ ⟨c₂, w₂⟩ => by
            ext <;> simp [map_add, sub_add_sub_comm]
          map_smul' := fun r ⟨c, w⟩ => by
            ext <;> simp [Prod.smul_def, map_smul, smul_eq_mul, mul_sub] }
      have hcomp1 : shear_bwd.comp shear_fwd = LinearMap.id := by
        ext x <;> simp [shear_fwd, shear_bwd]
      have hcomp2 : shear_fwd.comp shear_bwd = LinearMap.id := by
        ext x <;> simp [shear_fwd, shear_bwd]
      let τ_le : (F × V₂) ≃ₗ[F] (F × V₂) :=
        LinearEquiv.ofLinear shear_fwd shear_bwd hcomp2 hcomp1
      have τ_pres : ∀ p : F × V₂,
          ((0 : QuadraticForm F F).prod q₂) (τ_le p) = ((0 : QuadraticForm F F).prod q₂) p := by
        intro ⟨c, w⟩
        simp only [QuadraticMap.prod_apply, QuadraticMap.zero_apply, zero_add,
                   τ_le, LinearEquiv.ofLinear_apply, shear_fwd, LinearMap.coe_mk, AddHom.coe_mk]
      let τ : ((0 : QuadraticForm F F).prod q₂).IsometryEquiv
              ((0 : QuadraticForm F F).prod q₂) :=
        ⟨τ_le, τ_pres⟩
      have hα_new : ((ψ.trans τ) ((1 : F), (0 : V₁))).1 ≠ 0 := by
        show (τ_le (ψ.toLinearEquiv ((1 : F), (0 : V₁)))).1 ≠ 0
        simp only [τ_le, LinearEquiv.ofLinear_apply, shear_fwd, LinearMap.coe_mk, AddHom.coe_mk]
        rw [← hα]
        simp_all only [ne_eq, IsometryEquiv.coe_toLinearEquiv, zero_add, not_false_eq_true]
      exact key (ψ.trans τ) hα_new
  intro ψ' hα'
  let α : F := (ψ' ((1 : F), (0 : V₁))).1
  let u : V₂ := (ψ' ((1 : F), (0 : V₁))).2
  let β : V₁ →ₗ[F] F :=
    { toFun := fun v => (ψ' ((0 : F), v)).1
      map_add' := fun x y => by
        have := congr_arg Prod.fst (map_add ψ'.toLinearEquiv ((0 : F), x) ((0 : F), y))
        simpa using this
      map_smul' := fun c x => by
        have := congr_arg Prod.fst (map_smulₛₗ ψ'.toLinearEquiv c ((0 : F), x))
        simpa using this }
  let δ : V₁ →ₗ[F] V₂ :=
    { toFun := fun v => (ψ' ((0 : F), v)).2
      map_add' := fun x y => by
        have := congr_arg Prod.snd (map_add ψ'.toLinearEquiv ((0 : F), x) ((0 : F), y))
        simpa using this
      map_smul' := fun c x => by
        have := congr_arg Prod.snd (map_smulₛₗ ψ'.toLinearEquiv c ((0 : F), x))
        simpa using this }
  have hδ_pres : ∀ v : V₁, q₂ (δ v) = q₁ v := by
    intro v
    have := ψ'.map_app ((0 : F), v)
    simp only [QuadraticMap.prod_apply, QuadraticMap.zero_apply, zero_add] at this
    exact this
  have hqu : q₂ u = 0 := by
    have := ψ'.map_app ((1 : F), (0 : V₁))
    simp only [QuadraticMap.prod_apply, QuadraticMap.zero_apply, zero_add, map_zero, add_zero] at this
    exact this
  have hpolar_uδ : ∀ v : V₁, QuadraticMap.polar (↑q₂) u (δ v) = 0 := by
    intro v
    have h1' := ψ'.map_app ((1 : F), v)
    simp only [QuadraticMap.prod_apply, QuadraticMap.zero_apply, zero_add] at h1'
    have hlin : ψ' ((1 : F), v) = ψ' ((1 : F), (0 : V₁)) + ψ' ((0 : F), v) := by
      conv_lhs => rw [show ((1 : F), v) = ((1 : F), (0 : V₁)) + ((0 : F), v) from by simp]
      exact map_add ψ' _ _
    have h12 : (ψ' ((1 : F), v)).2 = u + δ v := congr_arg Prod.snd hlin
    rw [h12] at h1'
    simp only [QuadraticMap.polar]
    simp_all only [ne_eq, LinearMap.coe_mk, AddHom.coe_mk, Prod.snd_add, sub_zero, sub_self, δ, u]
  let δ' : V₁ →ₗ[F] V₂ := δ - (α⁻¹ • β).smulRight u
  have hδ'_pres : ∀ v : V₁, q₂ (δ' v) = q₁ v := by
    intro v
    show q₂ (δ v - (α⁻¹ * β v) • u) = q₁ v
    rw [quad_sub_smul_expand, hqu, mul_zero, add_zero,
      QuadraticMap.polar_comm, hpolar_uδ, mul_zero, sub_zero, hδ_pres]
  have hδ'_inj : Function.Injective δ' := by
    intro v₁ v₂ hv
    have hd : δ' (v₁ - v₂) = 0 := by rw [map_sub, sub_eq_zero.mpr hv]
    let w := v₁ - v₂
    change δ w - (α⁻¹ * β w) • u = 0 at hd
    have hδw : δ w = (α⁻¹ * β w) • u := sub_eq_zero.mp hd
    have hψbα : ψ' ((β w * α⁻¹ : F), (0 : V₁)) = (β w, (β w * α⁻¹) • u) := by
      have heq : ((β w * α⁻¹ : F), (0 : V₁)) = (β w * α⁻¹) • ((1 : F), (0 : V₁)) := by
        simp [Prod.smul_def]
      conv_lhs => rw [heq]; rw [map_smul ψ']
      simp [Prod.smul_def, α, u, smul_eq_mul]
      simp_all only [ne_eq, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.sub_apply,
        coe_smulRight, LinearMap.smul_apply, smul_eq_mul, Prod.smul_mk, mul_one,
        smul_zero, not_false_eq_true, inv_mul_cancel_right₀, δ, u, δ', α, β, w]
    have hψw_eq : ψ' ((0 : F), w) = ψ' ((β w * α⁻¹ : F), (0 : V₁)) := by
      rw [hψbα]; ext
      · simp_all only [ne_eq, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.sub_apply, δ, u, δ', α, β, w]
      · simp_all only [ne_eq, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.sub_apply, δ, u, δ', α, β, w]
        rw [mul_comm]
    have h_eq := EquivLike.injective ψ' hψw_eq
    exact sub_eq_zero.mp (congr_arg Prod.snd h_eq)
  have hdim : finrank F V₁ = finrank F V₂ := by
    have h1 : finrank F (F × V₁) = finrank F (F × V₂) := ψ'.toLinearEquiv.finrank_eq
    simp only [finrank_prod, finrank_self] at h1; omega
  have hδ'_surj := (δ'.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hδ'_inj
  exact ⟨LinearEquiv.ofBijective δ' ⟨hδ'_inj, hδ'_surj⟩, fun v => hδ'_pres v⟩

private def weightedSumSquares_succ_equiv (n : ℕ) (w : Fin (n + 1) → F) :
    (weightedSumSquares F w).IsometryEquiv
    ((w 0 • (QuadraticMap.sq (R := F))).prod (weightedSumSquares F (w ∘ Fin.succ))) where
  toLinearEquiv := (Fin.consLinearEquiv F (fun _ => F)).symm
  map_app' := by
    intro v
    simp only [QuadraticMap.prod_apply, smul_eq_mul, weightedSumSquares_apply, Function.comp]
    simp_rw [Fin.sum_univ_succ, Nat.succ_eq_add_one]
    rfl

/-- Cancellation for weighted sums of squares by induction on dimension -/
def witt_cancel_wss
    (n : ℕ) (w : Fin n → F)
    (q₁ : QuadraticForm F V₁) (q₂ : QuadraticForm F V₂)
    (h : ((weightedSumSquares F w).prod q₁).IsometryEquiv
         ((weightedSumSquares F w).prod q₂)) :
    q₁.IsometryEquiv q₂ := by
  induction n with
  | zero =>
    have h0 : weightedSumSquares F w = 0 := by
      ext v; simp [weightedSumSquares_apply, Finset.univ_eq_empty]
    rw [h0] at h
    exact (isometryEquivZeroProd q₁).symm.trans (h.trans (isometryEquivZeroProd q₂))
  | succ n ih =>
    let decomp := weightedSumSquares_succ_equiv n w
    let w' := w ∘ Fin.succ
    have h' :
      (((w 0 • (QuadraticMap.sq (R := F))).prod (weightedSumSquares F w')).prod q₁).IsometryEquiv
        (((w 0 • (QuadraticMap.sq (R := F))).prod (weightedSumSquares F w')).prod q₂) :=
      (decomp.symm.prod (QuadraticMap.IsometryEquiv.refl q₁)).trans
        (h.trans (decomp.prod (QuadraticMap.IsometryEquiv.refl q₂)))
    have h'' :
      ((w 0 • (QuadraticMap.sq (R := F))).prod ((weightedSumSquares F w').prod q₁)).IsometryEquiv
        ((w 0 • (QuadraticMap.sq (R := F))).prod ((weightedSumSquares F w').prod q₂)) :=
      (isometryEquivProdAssoc _ _ q₁).symm.trans
        (h'.trans (isometryEquivProdAssoc _ _ q₂))
    have h_inner : ((weightedSumSquares F w').prod q₁).IsometryEquiv
                   ((weightedSumSquares F w').prod q₂) := by
      by_cases hw0 : w 0 = 0
      · rw [hw0, zero_smul] at h''
        exact cancel_zero_dim _ _ h''
      · exact cancel_one_dim _ _ (w 0) hw0 h''
    exact ih w' h_inner

/-- Witt's cancellation theorem: q ⊕ q₁ ≅ q ⊕ q₂ implies q₁ ≅ q₂ -/
def witt_cancellation
    (q : QuadraticForm F V₀) (q₁ : QuadraticForm F V₁) (q₂ : QuadraticForm F V₂)
    (h : (q.prod q₁).IsometryEquiv (q.prod q₂)) :
    q₁.IsometryEquiv q₂ := by
  have ⟨w, hw⟩ := Classical.indefiniteDescription _ q.equivalent_weightedSumSquares
  let hw' := hw.some
  have h' : ((weightedSumSquares F w).prod q₁).IsometryEquiv
            ((weightedSumSquares F w).prod q₂) :=
    (hw'.prod (QuadraticMap.IsometryEquiv.refl q₁)).symm.trans
      (h.trans (hw'.prod (QuadraticMap.IsometryEquiv.refl q₂)))
  exact witt_cancel_wss _ w q₁ q₂ h'

end QuadraticForm

end
