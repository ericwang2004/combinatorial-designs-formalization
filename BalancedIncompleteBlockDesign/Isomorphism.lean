import BalancedIncompleteBlockDesign.IncidenceMatrix
import Mathlib.GroupTheory.GroupAction.Quotient

open BalancedIncompleteBlockDesign Finset MulAction
namespace BalancedIncompleteBlockDesign

variable {X : Type*} [Fintype X] [DecidableEq X]
  {Y : Type*} [Fintype Y] [DecidableEq Y] {b : ℕ}
  {α : Type*} [LinearOrderedRing α]

structure DesignIsomorphism (Φ₁ : Design X b) (Φ₂ : Design Y b)
    extends X ≃ Y where
  perm : Fin b ≃ Fin b
  map_blocks : image toFun ∘ Φ₁.blocks = Φ₂.blocks ∘ perm

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
    ext
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
      suffices h : image iso.toFun (Φ₁.blocks j) = Φ₂.blocks (iso.perm j) from
        (Finset.ext_iff.mp h) _
      have := funext_iff.mp iso.map_blocks j
      rwa [Function.comp] at this

variable {G : Type*} [Fintype G] [Group G] [MulAction G X]

abbrev jSubsets (j : ℕ) (X : Type*) := { s : Finset X // s.card = j }

instance : SMul G (Finset X) where
  smul g S := image (g • ·) S

instance (j : ℕ) : SMul G (jSubsets j X) where
  smul g S := ⟨g • S.val, by
    calc
      #(g • S.val) = #(image (fun x ↦ g • x) S.val) := rfl
      _ = #S.val := by
        rw [card_image_of_injective]
        exact MulAction.injective _
      _ = j := S.property
    ⟩

omit [Fintype X] [Fintype G] in
theorem mem_smul_jset {j : ℕ} {S : jSubsets j X} {g : G} {x : X} :
    x ∈ (g • S).val ↔ ∃ w ∈ S.val, g • w = x := by
  constructor <;> intro hx
  · have : x ∈ image (fun x ↦ g • x) S.val := hx
    rwa [Finset.mem_image] at this
  · have : (g • S).val = image (fun x ↦ g • x) S.val := rfl
    rwa [this, Finset.mem_image]

instance (j : ℕ) : MulAction G (jSubsets j X) where
  one_smul S := by
    apply Subtype.ext
    ext x
    constructor <;> intro hx
    · rw [mem_smul_jset] at hx
      obtain ⟨w, hw₁, hw₂⟩ := hx
      rw [one_smul] at hw₂
      rwa [←hw₂]
    · rw [mem_smul_jset]
      exact ⟨x, hx, by rw [one_smul]⟩
  mul_smul x y S := by
    apply Subtype.ext
    ext a
    constructor <;> intro ha <;> rw [mem_smul_jset] at ha ⊢ <;>
      obtain ⟨w, hw₁, hw₂⟩ := ha
    · use y • w
      constructor
      · rw [mem_smul_jset]
        use w
      · rwa [smul_smul]
    · rw [mem_smul_jset] at hw₁
      obtain ⟨z, hz₁, hz₂⟩ := hw₁
      exact ⟨z, hz₁, by rw [←hw₂, ←hz₂, smul_smul]⟩

def jOrbits (G : Type*) [Fintype G] [Group G] [∀ j, MulAction G (jSubsets j X)]
    (X : Type*) [Fintype X] [MulAction G X] (j : ℕ) :=
  Quotient |> orbitRel G (jSubsets j X) -- doesn't work
