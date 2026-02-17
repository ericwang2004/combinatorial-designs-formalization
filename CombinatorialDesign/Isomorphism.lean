import CombinatorialDesign.IncidenceMatrix

/-!

# Isomorphism of designs

This file defines the notion of isomorphism of designs.

Let Φ = (X, A) and Ψ = (Y, B) be designs. We say Φ and Ψ
are isomorphic if there exists a bijection f : X → Y such that
f(A) = B, where f(A) means "transform every point and every
block in A by f."

-/

open CombinatorialDesign Finset Equiv
namespace CombinatorialDesign

variable {ι X Y Z : Type*} [DecidableEq X] [DecidableEq ι] [DecidableEq Y] [DecidableEq Z]

@[ext]
structure DesignIsomorphism (Φ₁ : Design ι X) (Φ₂ : Design ι Y)
    extends X ≃ Y where
  perm : ι ≃ ι
  map_blocks : ∀ i, image toFun (Φ₁.blocks i) = Φ₂.blocks (perm i)

variable {Φ₁ : Design ι X} {Φ₂ : Design ι Y} {Φ₃ : Design ι Z}

-- ## DesignIsomorphism is an equivalence relation on the type Design ι X

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

variable (Φ : Design ι X)

@[refl]
def refl : DesignIsomorphism Φ Φ where
  toEquiv := Equiv.refl _
  perm := Equiv.refl _
  map_blocks := by simp

omit [DecidableEq ι]
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

/-- An automorphism is an isomorphism from a design to itself -/
abbrev DesignAut := DesignIsomorphism Φ Φ

/-- The type of automorphisms on a design Φ forms a group under composition -/
instance : Group (DesignAut Φ) where
  mul g h := trans h g
  one := refl Φ
  inv := symm
  mul_assoc _ _ _ := rfl
  one_mul _ := rfl
  mul_one _ := rfl
  inv_mul_cancel := self_trans_symm

/-
The rest of the file proves a characterization of isomorphism
in terms of incidence matrices. Specifically:

Let M, N be v × b incidence matrices of Φ and Ψ. Then Φ and Ψ are
isomorphic if and only if there exist permutations
γ : [v] → [v] and β : [b] → [b]
such that M i j = N (γ i) (β j), all i and j.
-/

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

def isoOfPerm {α : Type*} [One α] [Zero α] [NeZero (R := α) 1]
    (Φ₁ : Design ι X) (Φ₂ : Design ι Y) (γ : X ≃ Y) (σ : ι ≃ ι)
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
      simp only [mem_image] at hy ⊢
    · obtain ⟨_, _, rfl⟩ := hy
      rwa [←hyp]
    · exact ⟨γ.symm _, by rwa [hyp, γ.apply_symm_apply], γ.apply_symm_apply _⟩

theorem perm_of_iso {α : Type*} [One α] [Zero α] [NeZero (R := α) 1]
    (Φ₁ : Design ι X) (Φ₂ : Design ι Y) (iso : DesignIsomorphism Φ₁ Φ₂) :
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

end CombinatorialDesign
