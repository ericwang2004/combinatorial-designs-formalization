import CombinatorialDesign.SymmetricBIBD
import Mathlib.Tactic.Linarith

open CombinatorialDesign
namespace CombinatorialDesign

variable {ι ι₁ ι₂ X : Type*} [Fintype X] [DecidableEq X]
  [Fintype ι] [DecidableEq ι] [Fintype ι₁] [DecidableEq ι₁] [Fintype ι₂] [DecidableEq ι₂]
  {k l₁ l₂ l : ℕ}
open Finset

def sum (Φ₁ : BIBD ι₁ X k l₁) (Φ₂ : BIBD ι₂ X k l₂) :
    BIBD (ι₁ ⊕ ι₂) X k (l₁ + l₂) where
  blocks := by
    apply Sum.elim
    exact (fun i => Φ₁.blocks i)
    exact (fun j => Φ₂.blocks j)
  hvk := Φ₁.hvk
  hA u := by
    cases u with
    | inl i => simpa using Φ₁.hA i
    | inr j => simpa using Φ₂.hA j
  balance x y hxy := by
    have balance₁ := Φ₁.balance x y hxy
    have balance₂ := Φ₂.balance x y hxy
    simp_rw [← balance₁ , ← balance₂]
    rw [← @card_disjSum]
    congr
    ext u
    cases u with
    | inl i => simp
    | inr j => simp

noncomputable def complement [Inhabited X] (Φ : BIBD ι X k l) (hyp : (Fintype.card X) - k ≥ 2) :
    BIBD ι X ((Fintype.card X) - k) ((Fintype.card ι) - (2 * rep Φ - l)) where
  blocks := (Φ.blocks ·)ᶜ
  hvk := ⟨by have := Φ.hvk; norm_num; constructor <;> linarith, hyp⟩
  hA i := by
    have h := Φ.hA i
    simpa [← h] using card_compl (Φ.blocks i)
  balance x y hxy := by
    simp only [Pi.compl_apply, mem_compl]
    rw [filter_and_not, filter_not, sdiff_sdiff_left, card_univ_diff]
    simp only [Fintype.card_fin, sup_eq_union]
    rw [card_union, ←rep_elem, ←rep_elem, rep_eq_rep_elem, rep_eq_rep_elem,
      ←filter_and, Φ.balance x y hxy, ←Nat.two_mul]

end CombinatorialDesign
