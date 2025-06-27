import BalancedIncompleteBlockDesign.IncidenceMatrix
import Mathlib.GroupTheory.GroupAction.Quotient

open BalancedIncompleteBlockDesign Finset MulAction Quotient Equiv
namespace BalancedIncompleteBlockDesign

variable {X : Type*} [Fintype X] [DecidableEq X]
  {Y : Type*} [Fintype Y] [DecidableEq Y]
  {Z : Type*} [Fintype Z] [DecidableEq Z]
  {b : ℕ} {α : Type*} [LinearOrderedRing α]

@[ext]
structure DesignIsomorphism (Φ₁ : Design X b) (Φ₂ : Design Y b)
    extends X ≃ Y where
  perm : Fin b ≃ Fin b
  map_blocks : ∀ i, image toFun (Φ₁.blocks i) = Φ₂.blocks (perm i)

variable {Φ₁ : Design X b} {Φ₂ : Design Y b} {Φ₃ : Design Z b}

@[symm]
def symm (f : DesignIsomorphism Φ₁ Φ₂) : DesignIsomorphism Φ₂ Φ₁ where
  toEquiv := f.toEquiv.symm
  perm := f.perm.symm
  map_blocks := by
    simp only [Equiv.toFun_as_coe]
    intro j
    let i := f.perm.symm j
    have hi : j = f.perm i := (symm_apply_eq _).mp rfl
    rw [hi, Equiv.symm_apply_apply, ←f.map_blocks]
    aesop

@[trans]
def trans (f : DesignIsomorphism Φ₁ Φ₂) (g : DesignIsomorphism Φ₂ Φ₃)
    : DesignIsomorphism Φ₁ Φ₃ where
  toEquiv := Equiv.trans f.toEquiv g.toEquiv
  perm := Equiv.trans f.perm g.perm
  map_blocks i := by
    simp only [toFun_as_coe, coe_trans, trans_apply]
    rw [←g.map_blocks, ←f.map_blocks]
    aesop

variable (Φ : Design X b)

@[refl]
def refl : DesignIsomorphism Φ Φ where
  toEquiv := Equiv.refl _
  perm := Equiv.refl _
  map_blocks := by simp

@[simp]
theorem self_trans_symm (f : DesignIsomorphism Φ₁ Φ₂) : trans f (symm f) = refl Φ₁ := by
  ext; all_goals
  simp only [trans, symm, Equiv.self_trans_symm, toFun_as_coe, coe_refl,
    refl_symm, invFun_as_coe]; rfl

@[simp]
theorem symm_trans_self (f : DesignIsomorphism Φ₁ Φ₂) : trans (symm f) f = refl Φ₂ := by
  ext; all_goals
  simp only [trans, symm, Equiv.symm_trans_self, toFun_as_coe, coe_refl,
    refl_symm, invFun_as_coe]; rfl

abbrev DesignAut := DesignIsomorphism Φ Φ

instance : Group (DesignAut Φ) where
  mul g h := trans h g
  one := refl Φ
  inv := symm
  mul_assoc _ _ _ := rfl
  one_mul _ := rfl
  mul_one _ := rfl
  inv_mul_cancel := self_trans_symm

theorem ite_eq_ite' {α : Type*} [Zero α] [One α] [NeZero (R := α) 1]
    {P Q : Prop} [Decidable P] [Decidable Q] :
    (if P then (1 : α) else 0) = (if Q then 1 else 0) ↔ (P ↔ Q) := by
  constructor <;> intro hyp
  · constructor
    all_goals
    intro h
    by_contra nh
    simp only [h, if_true, nh, if_false] at hyp
    apply zero_ne_one (α := α)
    tauto
  · exact if_ctx_congr hyp (congrFun rfl) (congrFun rfl)

def isoOfPerm (Φ₁ : Design X b) (Φ₂ : Design Y b)
    (γ : X ≃ Y) (σ : Fin b ≃ Fin b)
    (hyp : ∀ i j, (toIncMat α Φ₁) i j = (toIncMat α Φ₂) (γ i) (σ j))
    : DesignIsomorphism Φ₁ Φ₂ where
  toFun := γ
  invFun := γ.invFun
  left_inv := γ.left_inv
  right_inv := γ.right_inv
  perm := σ
  map_blocks := by
    have hyp i j := ite_eq_ite'.mp (hyp i j)
    intro; ext
    constructor <;> intro hy <;>
      simp only [Function.comp_apply, mem_image] at hy ⊢
    · obtain ⟨_, _, rfl⟩ := hy
      rwa [←hyp]
    · exact ⟨γ.symm _, by rwa [hyp, γ.apply_symm_apply], γ.apply_symm_apply _⟩

theorem perm_of_iso (Φ₁ : Design X b) (Φ₂ : Design Y b)
    (iso : DesignIsomorphism Φ₁ Φ₂) :
    ∀ i j, (toIncMat α Φ₁) i j = (toIncMat α Φ₂) (iso.toFun i) (iso.perm j) := by
  intro x j
  simp only [toIncMat, Matrix.of_apply]
  rw [ite_eq_ite']
  calc
    x ∈ Φ₁.blocks j ↔ iso.toFun x ∈ iso.toFun '' (Φ₁.blocks j) := by
      rw [Set.mem_image_iff_of_inverse iso.left_inv iso.right_inv,
        iso.toFun_as_coe, iso.invFun_as_coe, iso.symm_apply_apply, mem_coe]
    _ ↔ iso.toFun x ∈ image iso.toFun (Φ₁.blocks j) := by
      simp only [Equiv.toFun_as_coe, Set.mem_image_equiv, Equiv.symm_apply_apply,
        mem_coe, mem_image, EmbeddingLike.apply_eq_iff_eq, exists_eq_right]
    _ ↔ iso.toFun x ∈ Φ₂.blocks (iso.perm j) := by
      apply Finset.ext_iff.mp (iso.map_blocks _)

variable {G : Type*} [Fintype G] [Group G] [MulAction G X]

instance : SMul G (Finset X) where
  smul g S := image (g • ·) S

omit [Fintype X] [Fintype G] in
theorem mem_smul_subset {g : G} {S : Finset X} {x : X} :
    x ∈ g • S ↔ ∃ w ∈ S, g • w = x := by
  constructor <;> intro hx
  · have : x ∈ image (fun x ↦ g • x) S := hx
    rwa [Finset.mem_image] at this
  · have : g • S = image (fun x ↦ g • x) S := rfl
    rwa [this, Finset.mem_image]

instance : MulAction G (Finset X) where
  one_smul S := by
    ext
    rw [mem_smul_subset]
    exact ⟨fun ⟨_, _, ha⟩ ↦ by rwa [←ha, one_smul],
      fun hx ↦ ⟨_, hx, by rw [one_smul]⟩⟩
  mul_smul x y S := by
    ext
    simp only [mem_smul_subset, exists_exists_and_eq_and]
    constructor; all_goals
    exact fun ⟨_, hw, ha⟩ ↦ ⟨_, hw, by rw [←ha, mul_smul]⟩

variable (G X)
abbrev jOrbits := Quotient <| orbitRel G (Finset X)

noncomputable instance : DecidableEq (Quotient <| orbitRel G X) :=
  Classical.typeDecidableEq _

noncomputable def countSubsetOrbit (O : jOrbits X G) (P : jOrbits X G) : ℕ :=
  Quotient.lift (fun Yi ↦ #{A | ⟦A⟧ = O ∧ Yi ⊆ A}) (by
  intro Y₁ Y₂ ⟨g, hg⟩
  simp only at hg ⊢
  have hg' : Y₂ = g⁻¹ • Y₁ := eq_inv_smul_iff.mpr hg
  apply card_bijective (fun S ↦ g⁻¹ • S) (MulAction.bijective _)
  intro S
  constructor <;> intro hS <;>
    simp only [mem_filter, mem_univ, true_and] at hS ⊢
  · constructor
    · rw [←hS.1]
      exact sound (by use g⁻¹)
    · intro x hx
      rw [hg', mem_smul_subset] at hx
      obtain ⟨_, hw, rfl⟩ := hx
      rw [mem_smul_subset]
      exact ⟨_, hS.2 hw, rfl⟩
  · constructor
    · rw [←hS.1]
      exact sound (by use g; simp only [smul_inv_smul])
    · intro x hx
      rw [←hg, mem_smul_subset] at hx
      obtain ⟨w, hw, rfl⟩ := hx
      sorry
  ) P

variable {G X}
def orbitCard (O : jOrbits X G) : ℕ :=
  Quotient.lift (fun Yi ↦ #Yi) (by
  intro Y₁ Y₂ ⟨g, hg⟩
  simp only at hg ⊢
  apply card_bijective (fun x ↦ g • x) (MulAction.bijective _)
  intro x
  sorry) O

variable (G X)
noncomputable def A (k₁ k₂ : ℕ) :
    Matrix {O : jOrbits X G // orbitCard O = k₁} {O : jOrbits X G // orbitCard O = k₂} ℕ :=
  Matrix.of (countSubsetOrbit X G · ·)
