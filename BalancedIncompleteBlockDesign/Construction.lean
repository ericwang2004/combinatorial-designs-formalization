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
    BIBD X v b (v - k) (b - (2 * rep Φ - l)) := {
  blocks := (Φ.blocks ·)ᶜ
  hX := Φ.hX
  hvk := ⟨by have := Φ.hvk; norm_num; constructor <;> linarith, hyp⟩
  hA i := by simp only [Pi.compl_apply]; rw [card_compl, Φ.hX, Φ.hA i]
  balance x y hxy := by
    simp only [Pi.compl_apply, mem_compl]
    rw [@filter_and_not, @filter_not, @sdiff_sdiff_left, @card_univ_diff]
    simp only [Fintype.card_fin, sup_eq_union]
    rw [@card_union, ← rep_elem, ← rep_elem, rep_eq_rep_elem, rep_eq_rep_elem,
      ← @filter_and, Φ.balance x y hxy, ← Nat.two_mul]
}

end BalancedIncompleteBlockDesign
