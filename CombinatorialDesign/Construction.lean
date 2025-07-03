import CombinatorialDesign.SymmetricBIBD
import Mathlib.Tactic.Linarith

open CombinatorialDesign
namespace CombinatorialDesign

variable {X} [Fintype X] [DecidableEq X] {v b₁ b₂ b k l₁ l₂ l : ℕ}
open Finset

def sum (Φ₁ : BIBD X v b₁ k l₁) (Φ₂ : BIBD X v b₂ k l₂) :
    BIBD X v (b₁ + b₂) k (l₁ + l₂) where
  blocks := Fin.addCases Φ₁.blocks Φ₂.blocks
  hX := Φ₁.hX
  hvk := Φ₁.hvk
  hA i := by
    cases i using Fin.addCases with
    | left i₁ => rw [Fin.addCases_left]; exact Φ₁.hA i₁
    | right i₂ => rw [Fin.addCases_right]; exact Φ₂.hA i₂
  balance x y hxy := by
    rw [←card_map finSumFinEquiv.symm.toEmbedding, map_filter, map_univ_equiv,
      Equiv.symm_symm, ←univ_disjSum_univ, ←map_inl_disjUnion_map_inr, filter_disjUnion,
      Finset.card_disjUnion]
    simp [Finset.filter_map, Function.comp_def, Φ₁.balance x y hxy, Φ₂.balance x y hxy]

noncomputable def complement [Inhabited X] (Φ : BIBD X v b k l) (hyp : v - k ≥ 2) :
    BIBD X v b (v - k) (b - (2 * rep Φ - l)) where
  blocks := (Φ.blocks ·)ᶜ
  hX := Φ.hX
  hvk := ⟨by have := Φ.hvk; norm_num; constructor <;> linarith, hyp⟩
  hA i := by simp only [Pi.compl_apply]; rw [card_compl, Φ.hX, Φ.hA i]
  balance x y hxy := by
    simp only [Pi.compl_apply, mem_compl]
    rw [filter_and_not, filter_not, sdiff_sdiff_left, card_univ_diff]
    simp only [Fintype.card_fin, sup_eq_union]
    rw [card_union, ←rep_elem, ←rep_elem, rep_eq_rep_elem, rep_eq_rep_elem,
      ←filter_and, Φ.balance x y hxy, ←Nat.two_mul]

end CombinatorialDesign
