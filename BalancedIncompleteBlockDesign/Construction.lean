import BalancedIncompleteBlockDesign.IncidenceMatrix
import Mathlib.Tactic.Linarith

open BalancedIncompleteBlockDesign
namespace BalancedIncompleteBlockDesign

variable {X : Type*} [Fintype X] [DecidableEq X] {v b₁ b₂ b k l₁ l₂ l : ℕ}
open Finset

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
    rw [← Finset.card_map finSumFinEquiv.symm.toEmbedding,
      Finset.map_filter, Finset.map_univ_equiv, Equiv.symm_symm,
      ← Finset.univ_disjSum_univ, ← Finset.map_inl_disjUnion_map_inr,
      Finset.filter_disj_union, Finset.card_disjUnion]
    simp [Finset.filter_map, Function.comp_def, Φ₁.balance x y hxy, Φ₂.balance x y hxy]
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
