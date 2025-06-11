import BalancedIncompleteBlockDesign.IncidenceMatrix
import Mathlib.Tactic.Linarith

open BalancedIncompleteBlockDesign
namespace BalancedIncompleteBlockDesign

variable {X : Type*} [Fintype X] [DecidableEq X] {v b₁ b₂ b k l₁ l₂ l : ℕ}
open Finset

#eval (Fin.castAdd 3) (2 : Fin 3)
#eval (Fin.natAdd 3) (2 : Fin 3)
#check Fin.castLE_injective

theorem natAdd_inj : Function.Injective (Fin.natAdd b₁ : Fin b₂ → Fin (b₁ + b₂)) := by
  intro a b hab
  simp only [Fin.natAdd, Fin.mk.injEq, add_right_inj] at hab
  exact Fin.eq_of_val_eq hab

theorem natAdd_ne_castAdd {i₁ : Fin b₁} {i₂ : Fin b₂} (h : Fin.natAdd b₁ i₂ = Fin.castAdd b₂ i₁) : False := by
  simp only [Fin.natAdd, Fin.castAdd, Fin.castLE, Fin.mk.injEq] at h
  have : b₁ + i₂ > i₁ := by
    exact Nat.lt_add_right (↑i₂) i₁.isLt
  rw [h] at this
  exact (lt_self_iff_false _).mp this

def sum (Φ₁ : BIBD X v b₁ k l₁) (Φ₂ : BIBD X v b₂ k l₂) :
    BIBD X v (b₁ + b₂) k (l₁ + l₂) := {
  blocks := Fin.addCases Φ₁.blocks Φ₂.blocks
  hX := Φ₁.hX
  hvk := Φ₁.hvk
  hA i := by
    simp only
    cases i using Fin.addCases with
    | left i₁ => rw [Fin.addCases_left]; exact Φ₁.hA i₁
    | right i₂ => rw [Fin.addCases_right]; exact Φ₂.hA i₂
  balance x y hxy := by
    simp only
    let S₁' : Finset (Fin b₁) := {i | x ∈ Φ₁.blocks i ∧ y ∈ Φ₁.blocks i}
    let S₁ : Finset (Fin (b₁ + b₂)) := S₁'.image (Fin.castAdd b₂)
    let S₂' : Finset (Fin b₂) := {i | x ∈ Φ₂.blocks i ∧ y ∈ Φ₂.blocks i}
    let S₂ : Finset (Fin (b₁ + b₂)) := S₂'.image (Fin.natAdd b₁)
    have disj : Disjoint S₁ S₂ := by
      rw [disjoint_iff_inter_eq_empty]
      ext i
      constructor
      · intro hi
        simp only [S₁, S₂, mem_inter, mem_image] at hi
        rcases hi with ⟨⟨i₁, mem₁, add₁⟩, ⟨i₂, mem₂, add₂⟩⟩
        rw [←add₂] at add₁
        exact False.elim (natAdd_ne_castAdd add₁.symm)
      intro hi
      simp only [not_mem_empty] at hi
    have size₁ : #S₁ = l₁ := by
      rw [card_image_of_injective _ (Fin.castAdd_injective _ _)]
      exact Φ₁.balance _ _ hxy
    have size₂ : #S₂ = l₂ := by
      rw [card_image_of_injective _ (natAdd_inj)]
      exact Φ₂.balance _ _ hxy
    have size_union : #(S₁ ∪ S₂) = l₁ + l₂ := by
      rw [←size₁, ←size₂]
      exact card_union_eq_card_add_card.mpr disj
    rw [←size_union]
    congr
    ext i
    constructor
    · intro hi
      simp only [mem_filter, mem_univ, true_and] at hi
      cases i using Fin.addCases with
      | left i₁ =>
        rw [Fin.addCases_left] at hi
        simp only [mem_union, S₁, mem_image, Fin.castAdd_inj, exists_eq_right, S₁',
          mem_filter, mem_univ, true_and]
        exact (Or.inr hi).symm
      | right i₂ =>
        rw [Fin.addCases_right] at hi
        simp only [mem_union, S₂, mem_image]
        exact Or.inr ⟨i₂,
          ⟨by simp only [S₂', mem_filter, mem_univ, true_and]; exact hi, rfl⟩⟩
    · intro hi
      simp only [mem_filter, mem_univ, true_and]
      rw [mem_union] at hi
      cases i using Fin.addCases with
      | left i₁ =>
        rw [Fin.addCases_left]
        cases hi with
        | inl hi =>
          simp only [S₁, mem_image, Fin.castAdd_inj, exists_eq_right, S₁',
            mem_filter, mem_univ, true_and] at hi
          exact hi
        | inr hi =>
          simp only [S₂, mem_image] at hi
          -- hi should give contradiction
          obtain ⟨a, _, ha⟩ := hi
          exact False.elim (natAdd_ne_castAdd ha)
      | right i₂ =>
        rw [Fin.addCases_right]
        cases hi with
        | inl hi =>
          simp only [S₁, mem_image] at hi
          -- hi should give contradiction
          obtain ⟨a, _, ha⟩ := hi
          exact False.elim (natAdd_ne_castAdd ha.symm)
        | inr hi =>
          simp only [S₂, mem_image] at hi
          rcases hi with ⟨a, ha₁, ha₂⟩
          simp only [S₂', mem_filter, mem_univ, true_and] at ha₁
          have := natAdd_inj ha₂
          subst this
          exact ha₁
}

def complement [Inhabited X] (Φ : BIBD X v b k l) (hyp : v - k ≥ 2) :
    BIBD X v b (v - k) (b - 2 * rep Φ + l) := {
  blocks := (Φ.blocks ·)ᶜ
  hX := Φ.hX
  hvk := ⟨by have := Φ.hvk; norm_num; constructor <;> linarith, hyp⟩
  hA i := by simp only [Pi.compl_apply]; rw [card_compl, Φ.hX, Φ.hA i]
  balance x y hxy := by
    simp only [Pi.compl_apply, mem_compl]
    let S₁ : Finset (Fin b) := {i | x ∈ Φ.blocks i ∧ y ∈ Φ.blocks i}
    let S₂ : Finset (Fin b) := {i | x ∈ Φ.blocks i ∧ y ∉ Φ.blocks i}
    let S₃ : Finset (Fin b) := {i | x ∉ Φ.blocks i ∧ y ∈ Φ.blocks i}
    let S₄ : Finset (Fin b) := {i | x ∉ Φ.blocks i ∧ y ∉ Φ.blocks i}
    have union₁₂ : S₁ ∪ S₂ = {i | x ∈ Φ.blocks i} := by
      ext i
      constructor
      · intro hi
        simp only [coe_union, coe_filter, mem_univ, true_and,
          Set.mem_union, Set.mem_setOf_eq, S₁, S₂] at hi
        simp only [Set.mem_setOf_eq]
        cases hi with
        | inl h => exact h.1
        | inr h => exact h.1
      · intro hi
        simp only [coe_union, Set.mem_union, mem_coe]
        simp only [Set.mem_setOf_eq] at hi
        by_cases hy : y ∈ Φ.blocks i
        · left
          simp only [S₁, mem_filter, mem_univ, true_and]
          exact ⟨hi, hy⟩
        · right
          simp only [S₂, mem_filter, mem_univ, true_and]
          exact ⟨hi, hy⟩
    sorry

}


end BalancedIncompleteBlockDesign
