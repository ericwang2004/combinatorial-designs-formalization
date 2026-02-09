import CombinatorialDesign.SymmetricBIBD
import Mathlib.Tactic.Linarith

open CombinatorialDesign
namespace CombinatorialDesign

variable {ι ι₁ ι₂ X : Type*} [Fintype X] [DecidableEq X]
  [Fintype ι] [DecidableEq ι] [Fintype ι₁] [DecidableEq ι₁] [Fintype ι₂] [DecidableEq ι₂]
  {k l₁ l₂ l r₁ r₂ t : ℕ}
open Finset

------------------------------
------ Sum Constriction ------
------------------------------
def Design.sum (Φ₁ : Design ι₁ X) (Φ₂ : Design ι₂ X) : Design (ι₁ ⊕ ι₂) X where
  blocks := Sum.elim Φ₁.blocks Φ₂.blocks

def BlockDesign.sum (Φ₁ : BlockDesign ι₁ X k) (Φ₂ : BlockDesign ι₂ X k) : BlockDesign (ι₁ ⊕ ι₂) X k where
  toDesign := Design.sum Φ₁.toDesign Φ₂.toDesign
  uniform u := by
    cases u with
    | inl => simpa using Φ₁.uniform _
    | inr => simpa using Φ₂.uniform _

def RegularDesign.sum (Φ₁ : RegularDesign ι₁ X r₁) (Φ₂ : RegularDesign ι₂ X r₂) :
    RegularDesign (ι₁ ⊕ ι₂) X (r₁ + r₂) where
  toDesign := Design.sum Φ₁.toDesign Φ₂.toDesign
  regularity x := by
    simp_rw [←Φ₁.regularity x, ←Φ₂.regularity x, ←card_disjSum]
    congr 1
    ext u
    simp only [Design.sum, mem_disjSum, mem_filter, mem_univ, true_and]
    cases u <;> simp

def BalancedDesign.sum (Φ₁ : BalancedDesign ι₁ X t l₁) (Φ₂ : BalancedDesign ι₂ X t l₂) :
    BalancedDesign (ι₁ ⊕ ι₂) X t (l₁ + l₂) where
  toDesign := Design.sum Φ₁.toDesign Φ₂.toDesign
  balance s hs := by
    simp_rw [←Φ₁.balance s hs, ←Φ₂.balance s hs, ←card_disjSum]
    congr 1
    ext u
    simp only [Design.sum, mem_disjSum, mem_filter, mem_univ, true_and]
    cases u <;> simp

def IncompleteDesign.sum (Φ₁ : IncompleteDesign ι₁ X k) (Φ₂ : IncompleteDesign ι₂ X k) :
    IncompleteDesign (ι₁ ⊕ ι₂) X k where
  toBlockDesign := BlockDesign.sum Φ₁.toBlockDesign Φ₂.toBlockDesign
  incomplete := Φ₁.incomplete

def RPBD.sum (Φ₁ : RPBD ι₁ X l₁ r₁) (Φ₂ : RPBD ι₂ X l₂ r₂) :
    RPBD (ι₁ ⊕ ι₂) X (l₁ + l₂) (r₁ + r₂) where
  toRegularDesign := RegularDesign.sum Φ₁.toRegularDesign Φ₂.toRegularDesign
  balance := (BalancedDesign.sum Φ₁.toBalancedDesign Φ₂.toBalancedDesign).balance

def TDesign.sum (Φ₁ : TDesign ι₁ X k t l₁) (Φ₂ : TDesign ι₂ X k t l₂) :
    TDesign (ι₁ ⊕ ι₂) X k t (l₁ + l₂) where
  toIncompleteDesign := IncompleteDesign.sum Φ₁.toIncompleteDesign Φ₂.toIncompleteDesign
  balance := (BalancedDesign.sum Φ₁.toBalancedDesign Φ₂.toBalancedDesign).balance
  t_le_k := Φ₁.t_le_k

def BIBD.sum (Φ₁ : BIBD ι₁ X k l₁) (Φ₂ : BIBD ι₂ X k l₂) :
    BIBD (ι₁ ⊕ ι₂) X k (l₁ + l₂) := TDesign.sum Φ₁ Φ₂

-------------------------------------
------ Complement Constriction ------
-------------------------------------
def Design.complement (Φ : Design ι X) : Design ι X where
  blocks := (Φ.blocks ·)ᶜ

def BlockDesign.complement (Φ : BlockDesign ι X k) :
    BlockDesign ι X (Fintype.card X - k) where
  toDesign := Design.complement Φ.toDesign
  uniform i := by
    have h := Φ.uniform i
    simpa [← h] using card_compl (Φ.blocks i)

def RegularDesign.complement (Φ : RegularDesign ι X r₁) :
    RegularDesign ι X (Fintype.card ι - r₁) where
  blocks := (Φ.blocks ·)ᶜ
  regularity x := by
    simp only [Pi.compl_apply, mem_compl, ← Φ.regularity x]
    rw [← card_compl {i | x ∈ Φ.blocks i}]
    congr
    ext i
    simp

def BIBD.complement [Inhabited X] (Φ : BIBD ι X k l) (hyp : (Fintype.card X) - k ≥ 2) :
    BIBD ι X ((Fintype.card X) - k) ((Fintype.card ι) - (2 * rep Φ - l)) where
  blocks := (Φ.blocks ·)ᶜ
  incomplete := Nat.sub_lt (v_pos_of_bibd Φ) (k_pos_of_bibd Φ)
  t_le_k := hyp
  uniform i := by
    have h := Φ.uniform i
    simpa [← h] using card_compl (Φ.blocks i)
  balance s hs := by
    simp only [Pi.compl_apply]
    obtain ⟨x, y, hxy, rfl⟩ := card_eq_two.mp hs
    simp only [subset_iff, mem_insert, mem_singleton, forall_eq_or_imp, forall_eq,
      mem_compl]
    have hrep := rep_eq_rep_elem Φ
    have hbal := Φ.balance {x, y} (card_pair hxy)
    simp only [subset_iff, mem_insert, mem_singleton, forall_eq_or_imp, forall_eq] at hbal
    let A : Finset ι := univ.filter (x ∈ Φ.blocks ·)
    let B : Finset ι := univ.filter (y ∈ Φ.blocks ·)
    have hA : #A = rep Φ := hrep x
    have hB : #B = rep Φ := hrep y
    have hAB : #(A ∩ B) = l := by
      simp only [A, B, ←filter_and, hbal]
    have hunion : #(A ∪ B) = 2 * rep Φ - l := by
      have := card_union_add_card_inter A B
      rw [hA, hB, hAB] at this
      omega
    have hgoal : #{i | x ∉ Φ.blocks i ∧ y ∉ Φ.blocks i} = #(A ∪ B)ᶜ := by
      congr 1
      ext i; simp only [A, B, mem_compl, mem_union, mem_filter, mem_univ, true_and, not_or]
    rw [hgoal, card_compl, hunion]


def derived [Inhabited X] (Φ : BIBD X X k l) (i₀ : X) (hl : 2 ≤ l) :
    BIBD {i // i ≠ i₀} {x // x ∈ Φ.blocks i₀} l (l - 1) where
  blocks i := map (Subtype.impEmbedding _ _ inter_subset_right) (Φ.blocks i ∩ Φ.blocks i₀).attach
  t_le_k := hl
  incomplete := by
    rw [Fintype.card_coe, Φ.uniform]
    exact l_lt_k_of_symmBIBD Φ
  uniform i := by
    simp only [card_map, card_attach]
    exact card_inter_block_eq_l _ i.property
  balance s hs := by
    obtain ⟨x, y, hxy, rfl⟩ := card_eq_two.mp hs
    let S₀ : Finset X := {i | (x : X) ∈ Φ.blocks i ∧ (y : X) ∈ Φ.blocks i}
    have hi₀S₀ : i₀ ∈ S₀ := by simp only [S₀, mem_filter, mem_univ, true_and, x.property, y.property]
    have hS₀ : #S₀ = l := by
      have := Φ.balance {(x : X), (y : X)} (card_pair (Subtype.coe_ne_coe.mpr hxy))
      simp only [subset_iff, mem_insert, mem_singleton, forall_eq_or_imp, forall_eq] at this ⊢
      exact this
    have key : #{i : {i // i ≠ i₀} | (x : X) ∈ Φ.blocks i ∧ (y : X) ∈ Φ.blocks i} = l - 1 := by
      have : #{i : {i // i ≠ i₀} | (x : X) ∈ Φ.blocks i ∧ (y : X) ∈ Φ.blocks i} = #(S₀.erase i₀) := by
        apply card_bij (fun i _ => i.val)
        · intro i hi; simp only [mem_filter, mem_univ, true_and] at hi
          simp only [mem_erase, ne_eq, i.property, not_false_eq_true, S₀, mem_filter, mem_univ, hi, and_self]
        · intro i _ j _ hij; exact Subtype.ext hij
        · intro b hb; simp only [S₀, mem_erase, mem_filter, mem_univ, true_and] at hb
          exact ⟨⟨b, hb.1⟩, by simp [hb.2], rfl⟩
      rw [this, card_erase_of_mem hi₀S₀, hS₀]
    rw [←key]
    apply congrArg
    ext i
    simp only [mem_map, mem_attach, true_and, Subtype.exists, mem_inter, mem_filter, mem_univ,
      subset_iff, mem_insert, mem_singleton, forall_eq_or_imp, forall_eq]
    constructor
    · intro ⟨⟨a, ⟨ha1, ha2⟩, ha3⟩, ⟨b, ⟨hb1, hb2⟩, hb3⟩⟩
      have ha3' : a = x.val := congrArg Subtype.val ha3
      have hb3' : b = y.val := congrArg Subtype.val hb3
      exact ⟨by rw [←ha3']; exact ha1, by rw [←hb3']; exact hb1⟩
    · intro ⟨hx, hy⟩
      constructor
      · exact ⟨x.val, ⟨hx, x.property⟩, Subtype.ext rfl⟩
      · exact ⟨y.val, ⟨hy, y.property⟩, Subtype.ext rfl⟩

def residual [Inhabited X] (Φ : BIBD X X k l) (i₀ : X) (hkl : 2 ≤ k - l) :
    BIBD {i // i ≠ i₀} {x // x ∉ Φ.blocks i₀} (k - l) l where
  blocks i := map
    (Subtype.impEmbedding _ _ (fun _ hx ↦ mem_sdiff.mp hx |>.2))
    (Φ.blocks i \ Φ.blocks i₀).attach
  t_le_k := hkl
  incomplete := by
    rw [Fintype.card_subtype_compl, Fintype.card_coe, Φ.uniform]
    have hkl' : l + 2 ≤ k := by
      rw [←Nat.le_sub_iff_add_le']
      · exact hkl
      · exact l_le_k_of_symmBIBD Φ
    exact k_sub_l_lt_v_minus_k_of_symmBIBD Φ hkl'
  uniform i := by
    have : Inhabited X := ⟨i₀⟩
    simp only [card_map, card_attach]
    rw [←sdiff_inter_self_left, card_sdiff_of_subset inter_subset_left,
      Φ.uniform, card_inter_block_eq_l]
    exact i.property
  balance s hs := by
    obtain ⟨x, y, hxy, rfl⟩ := card_eq_two.mp hs
    let S₀ : Finset X := {i | (x : X) ∈ Φ.blocks i ∧ (y : X) ∈ Φ.blocks i}
    have hi₀S₀ : i₀ ∉ S₀ := by
      simp only [S₀, mem_filter, mem_univ, true_and]
      intro ⟨hx, _⟩; exact x.property hx
    have hS₀ : #S₀ = l := by
      have := Φ.balance {(x : X), (y : X)} (card_pair (Subtype.coe_ne_coe.mpr hxy))
      simp only [subset_iff, mem_insert, mem_singleton, forall_eq_or_imp, forall_eq] at this ⊢
      exact this
    have key : #{i : {i // i ≠ i₀} | (x : X) ∈ Φ.blocks i ∧ (y : X) ∈ Φ.blocks i} = l := by
      have : #{i : {i // i ≠ i₀} | (x : X) ∈ Φ.blocks i ∧ (y : X) ∈ Φ.blocks i} = #S₀ := by
        apply card_bij (fun i _ => i.val)
        · intro i hi; simp only [mem_filter, mem_univ, true_and] at hi
          simp only [S₀, mem_filter, mem_univ, hi, and_self]
        · intro i _ j _ hij; exact Subtype.ext hij
        · intro b hb; simp only [S₀, mem_filter, mem_univ, true_and] at hb
          have hb' : b ≠ i₀ := fun h => hi₀S₀ (by simp only [S₀, mem_filter, mem_univ, true_and]; subst h; exact hb)
          exact ⟨⟨b, hb'⟩, by simp [hb], rfl⟩
      rw [this, hS₀]
    simp_rw [←key]
    apply congrArg
    ext i
    simp only [mem_map, mem_attach, true_and, Subtype.exists, mem_sdiff, mem_filter, mem_univ,
      subset_iff, mem_insert, mem_singleton, forall_eq_or_imp, forall_eq]
    constructor
    · intro ⟨⟨a, ⟨ha1, ha2⟩, ha3⟩, ⟨b, ⟨hb1, hb2⟩, hb3⟩⟩
      have ha3' : a = x.val := congrArg Subtype.val ha3
      have hb3' : b = y.val := congrArg Subtype.val hb3
      exact ⟨by rw [←ha3']; exact ha1, by rw [←hb3']; exact hb1⟩
    · intro ⟨hx, hy⟩
      constructor
      · exact ⟨x.val, ⟨hx, x.property⟩, Subtype.ext rfl⟩
      · exact ⟨y.val, ⟨hy, y.property⟩, Subtype.ext rfl⟩

variable {G : Type*} [Fintype G] [DecidableEq G] [AddCommGroup G]

def fromDifferenceSet (D : differenceSet ι G l) :
    BIBD G G (Fintype.card ι) l where
  blocks g := {g + x | x ∈ image D.elems univ}
  t_le_k := D.hvk.2
  incomplete := D.hvk.1
  uniform _ := by
    simp only [mem_image, mem_univ, true_and,
      exists_exists_eq_and, univ_filter_exists]
    apply card_image_of_injective
    intro _ _ hij
    simp only [add_right_inj] at hij
    exact D.elems_unique hij
  balance s hs := by
    obtain ⟨x, y, hxy, rfl⟩ := card_eq_two.mp hs
    simp only [subset_iff, mem_insert, mem_singleton, forall_eq_or_imp, forall_eq,
      mem_image, mem_univ, true_and, exists_exists_eq_and, univ_filter_exists]
    simp_rw [←D.balance (x - y) (sub_ne_zero_of_ne hxy)]
    symm
    apply card_bij (fun ⟨i, j⟩ _ => x - D.elems i)
    · intro ⟨i, j⟩ hij
      simp only [mem_filter, mem_univ, true_and] at hij ⊢
      refine ⟨⟨i, sub_add_cancel x _⟩, ⟨j, ?_⟩⟩
      have : D.elems j = D.elems i - (x - y) := by rw [←hij]; abel
      rw [this]; abel
    · intro ⟨i₁, j₁⟩ ha₁ ⟨i₂, j₂⟩ ha₂ heq
      simp only at heq
      have hi : D.elems i₁ = D.elems i₂ := sub_right_injective heq
      simp only [Prod.mk.injEq, D.elems_unique hi, true_and]
      simp only [mem_filter, mem_univ, true_and] at ha₁ ha₂
      apply D.elems_unique
      have h1 : D.elems j₁ = D.elems i₁ - (x - y) := by rw [←ha₁]; abel
      have h2 : D.elems j₂ = D.elems i₂ - (x - y) := by rw [←ha₂]; abel
      rw [h1, h2, hi]
    · intro g hg
      simp only [mem_filter, mem_univ, true_and] at hg
      obtain ⟨⟨i, hi⟩, ⟨j, hj⟩⟩ := hg
      use ⟨i, j⟩
      simp only [mem_filter, mem_univ, true_and, exists_prop]
      refine ⟨?_, ?_⟩
      · rw [←hi, ←hj]; abel
      · rw [←hi]; abel

omit [DecidableEq ι] in
theorem blocks_distinct_of_fromDifferenceSet (D : differenceSet ι G l) :
    ∀ i j, i ≠ j →
    (fromDifferenceSet D).blocks i ≠ (fromDifferenceSet D).blocks j := by
  intro i j hij hblocks
  have _ : Inhabited G := ⟨i⟩
  have hl := card_inter_block_eq_l (fromDifferenceSet D) hij
  rw [hblocks, inter_self, (fromDifferenceSet _).uniform j] at hl
  nth_rewrite 2 [←lt_self_iff_false l, ←hl]
  exact l_lt_k_of_symmBIBD (fromDifferenceSet D)

end CombinatorialDesign
