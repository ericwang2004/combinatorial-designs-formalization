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
  blocks := Sum.elim Φ₁.blocks Φ₂.blocks
  hvk := Φ₁.hvk
  hA u := by
    cases u with
    | inl => simpa using Φ₁.hA _
    | inr => simpa using Φ₂.hA _
  balance x y hxy := by
    simp_rw [←Φ₁.balance x y hxy , ←Φ₂.balance x y hxy, ←card_disjSum]
    congr
    ext u
    cases u with
    | inl => simp
    | inr => simp

def complement [Inhabited X] (Φ : BIBD ι X k l) (hyp : (Fintype.card X) - k ≥ 2) :
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

def derived [Inhabited X] (Φ : BIBD X X k l) (i₀ : X) (hl : 2 ≤ l) :
    BIBD {i // i ≠ i₀} {x // x ∈ Φ.blocks i₀} l (l - 1) where
  blocks i := map (Subtype.impEmbedding _ _ inter_subset_right) (Φ.blocks i ∩ Φ.blocks i₀).attach
  hvk := by
    constructor
    · rw [Fintype.card_coe, Φ.hA]
      exact l_lt_k_of_symmBIBD Φ
    · exact hl
  hA i := by
    simp only [card_map, card_attach]
    exact card_inter_block_eq_l _ i.property
  balance x y hxy := by
    simp only [mem_map]
    let S : Finset X := erase {i | x.val ∈ Φ.blocks i ∧ y.val ∈ Φ.blocks i} i₀
    have hSi₀ : i₀ ∉ S := notMem_erase _ _
    let T : Finset {i // i ≠ i₀} := map
      (Subtype.impEmbedding _ _  (fun _ hx ↦ ne_of_mem_of_not_mem hx hSi₀))
      S.attach
    have cardT : #T = l - 1 := by
      rw [card_map, card_attach]
      apply Nat.eq_sub_of_add_eq
      rw [←Subtype.coe_ne_coe.mpr hxy |> Φ.balance _ _]
      apply card_erase_add_one
      simp only [mem_filter, mem_univ, coe_mem, and_self, S]
    rw [←cardT]
    congr
    ext i
    constructor <;> intro hi
    · simp only [T, mem_map, Subtype.exists]
      use i
      simp only [ne_eq, mem_attach, true_and, Subtype.exists,
        mem_inter, mem_filter, mem_univ, T] at hi
      obtain ⟨⟨_, _, rfl⟩, ⟨_, _, rfl⟩⟩ := hi
      exact ⟨by
        simp only [mem_erase, mem_filter, mem_univ, true_and, S]
        exact ⟨i.property, by simp_all, by simp_all⟩,
        mem_attach _ _, rfl⟩
    · simp only [ne_eq, mem_map, mem_attach, true_and,
        Subtype.exists, T, S] at hi
      obtain ⟨a, ha, rfl⟩ := hi
      aesop

def residual [Inhabited X] (Φ : BIBD X X k l) (i₀ : X) (hkl : 2 ≤ k - l) :
    BIBD {i // i ≠ i₀} {x // x ∉ Φ.blocks i₀} (k - l) l where
  blocks i := map
    (Subtype.impEmbedding _ _ (fun _ hx ↦ mem_sdiff.mp hx |>.2))
    (Φ.blocks i \ Φ.blocks i₀).attach
  hvk := by
    constructor
    · rw [Fintype.card_subtype_compl, Fintype.card_coe, Φ.hA]
      have hkl' : l + 2 ≤ k := by
        rw [←Nat.le_sub_iff_add_le']
        · exact hkl
        · exact l_le_k_of_symmBIBD Φ
      exact k_sub_l_lt_v_minus_k_of_symmBIBD Φ hkl'
    · exact hkl
  hA i := by
    have : Inhabited X := ⟨i₀⟩
    simp only [card_map, card_attach]
    rw [←sdiff_inter_self_left, card_sdiff inter_subset_left,
      Φ.hA, card_inter_block_eq_l]
    exact i.property
  balance x y hxy := by
    let S : Finset {i // i ≠ i₀} := map (Subtype.impEmbedding
      (fun i ↦ (x : X) ∈ Φ.blocks i ∧ (y : X) ∈ Φ.blocks i)
      _ (by rintro _ ⟨hi, _⟩ rfl; exact x.property hi))
      {j | (x : X) ∈ Φ.blocks j ∧ (y : X) ∈ Φ.blocks j}
    have cardS : #S = l := by
      simp only [card_map, S]
      simp_rw [←Φ.balance x y (Subtype.coe_ne_coe.mpr hxy)]
      apply card_bij (fun j _ ↦ ↑j)
      · intro _ hj
        simp only [mem_filter, mem_univ, true_and] at hj ⊢
        exact hj
      · intro _ _ _ _ hj
        exact Subtype.eq hj
      · intros
        simp_all only [mem_filter, mem_univ, true_and,
          exists_prop, Subtype.exists, exists_eq_right]
    simp_rw [←cardS, S]
    congr
    ext i
    constructor <;> intro hi
    · simp only [mem_map, mem_filter, mem_univ, true_and,
        Subtype.exists, exists_and_left, and_exists_self]
      simp only [mem_map, mem_attach, true_and, Subtype.exists,
        mem_sdiff, mem_filter, mem_univ, S] at hi
      obtain ⟨⟨a, ha, rfl⟩, ⟨b, hb, rfl⟩⟩ := hi
      use i.val, by simp [ha, hb]
      rfl
    · simp only [mem_map, mem_attach, true_and, Subtype.exists,
        mem_sdiff, mem_filter, mem_univ]
      simp only [mem_map, mem_filter, mem_univ, true_and,
        Subtype.exists, exists_and_left, and_exists_self, S] at hi
      obtain ⟨a, ha, rfl⟩ := hi
      constructor <;> rw [Subtype.impEmbedding_apply_coe]
      · use x.val, ⟨ha.1, x.property⟩
        rfl
      · use y.val, ⟨ha.2, y.property⟩
        rfl

end CombinatorialDesign
