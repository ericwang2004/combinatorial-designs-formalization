import Mathlib.Data.Set.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Card

open Finset

namespace BalancedIncompleteBlockDesign

structure Design (X : Type*) [Fintype X] (b : ℕ) where
  mk ::
  blocks : Fin b → Finset X

/-- Balanced Block Design -/
structure BBD (X : Type*) [Fintype X] [DecidableEq X] (v b l : ℕ) extends Design X b where
  mk ::
  hX : Fintype.card X = v
  balance : ∀ x y, x ≠ y → #{i | x ∈ blocks i ∧ y ∈ blocks i} = l

/-- Regular Pairwise Balanced Design -/
structure RPBD (X : Type*) [Fintype X] [DecidableEq X] (v b l r : ℕ) extends BBD X v b l where
  mk ::
  regularity : ∀ x, #{i | x ∈ blocks i} = r

/-- Balanced Incomplete Block Design -/
structure BIBD (X : Type*) [Fintype X] [DecidableEq X]
    (v b k l : ℕ) extends BBD X v b l where
  mk ::
  hvk : v > k ∧ k ≥ 2
  hA : ∀ i : Fin b, #(blocks i) = k

variable {X : Type*} [Fintype X] [DecidableEq X] {v b k l : ℕ} (Φ : BIBD X v b k l)

def rep_elem (x : X) := #{i | x ∈ Φ.blocks i}

theorem card_dependent {α : Type*} [Fintype α] {β : Type*} [Fintype β]
    (P : α → Prop) [DecidablePred P]
    (Q : α → β → Prop) [∀ x, DecidablePred (Q x)]
    {k : ℕ} (hk : ∀ x, P x → #{y | Q x y} = k) :
    #{(x, y) | P x ∧ Q x y} = k * #{x | P x} := by
  let g x (hx : P x) : { y // Q x y } ≃ Fin k := by
    rw [←hk x hx]
    apply Fintype.equivFinOfCardEq
    apply Fintype.card_of_subtype
    intro y
    simp only [mem_filter, mem_univ, true_and]
  let J : Finset (Fin k × α) := Finset.product univ {x | P x}
  have sizeJ : #J = k * #{x | P x} := by calc
    _ = _ := by apply Finset.card_product
    _ = _ := by rw [card_fin k]
  rw [←sizeJ]
  apply card_bij (fun (x, y) hxy ↦ by
    simp only [mem_filter, mem_univ, true_and] at hxy
    exact (g x hxy.1 ⟨y, hxy.2⟩, x)
  )
  · intro ⟨x, y⟩ hxy
    simp only [mem_filter, mem_univ, true_and] at hxy
    exact mem_product.mpr ⟨by apply mem_univ,
      by simp only [mem_filter, mem_univ, true_and]; exact hxy.1⟩
  · intro ⟨x₁, y₁⟩ hxy₁ ⟨x₂, y₂⟩ hxy₂
    simp only [mem_filter, mem_univ, true_and] at hxy₁ hxy₂
    simp only [Prod.mk.injEq, and_imp]
    exact fun hg xeq ↦
      ⟨xeq, by subst xeq; simp_all only [EmbeddingLike.apply_eq_iff_eq, Subtype.mk.injEq]⟩
  · intro ⟨i, x⟩ hJ
    have hx : P x := (mem_filter.mp (mem_product.mp hJ).2).2
    use (x, (g x hx).symm i)
    simp only [Subtype.coe_eta, Equiv.apply_symm_apply, mem_filter, mem_univ, true_and, exists_prop,
      and_true]
    exact ⟨hx, ((g x hx).symm i).property⟩

theorem card_of_swap {α : Type*} [Fintype α] {β : Type*} [Fintype β]
    {P : α → β → Prop} [∀ x, DecidablePred (P x)]
    {Q : β → α → Prop} [∀ y, DecidablePred (Q y)]
    (hPQ : ∀ x y, P x y ↔ Q y x) :
    #{(x, y) | P x y} = #{(y, x) | Q y x} := by
  apply card_bij (fun (x, y) _ ↦ (y, x))
  · intro ⟨x, y⟩ hxy
    simp only [mem_filter, mem_univ, true_and] at hxy ⊢
    exact (hPQ _ _).1 hxy
  · intro ⟨x₁, y₁⟩ hxy₁ ⟨x₂, y₂⟩ hxy₂
    simp only [mem_filter, mem_univ, true_and] at hxy₁ hxy₂
    simp only [Prod.mk.injEq, and_imp]
    exact fun hy hx ↦ ⟨hx, hy⟩
  · intro ⟨x, y⟩ hxy
    simp only [mem_filter, mem_univ, true_and] at hxy
    use ⟨y, x⟩
    simp only [mem_filter, mem_univ, true_and, exists_prop, and_true]
    exact (hPQ _ _).2 hxy

theorem rep_constant : ∀ x, (k - 1) * rep_elem Φ x = l * (v - 1) := by
  intro x
  let P₁ : X → Prop := fun y ↦ x ≠ y
  let Q₁ : X → Fin b → Prop := fun y i ↦ x ∈ Φ.blocks i ∧ y ∈ Φ.blocks i
  have aux₁ : ∀ y, P₁ y → #{i | Q₁ y i} = l := Φ.balance x
  have count₁ := card_dependent P₁ Q₁ aux₁
  let P₂ : Fin b → Prop := fun i ↦ x ∈ Φ.blocks i
  let Q₂ : Fin b → X → Prop := fun i y ↦ x ≠ y ∧ y ∈ Φ.blocks i
  have : ∀ i, filter (fun y ↦ Q₂ i y) univ = (Φ.blocks i).erase x := by
    intro i; ext y
    constructor
    · intro hy
      simp only [mem_filter, mem_univ, true_and] at hy
      exact mem_erase.mpr ⟨Ne.symm hy.1, hy.2⟩
    · intro hy
      simp only [mem_filter, mem_univ, true_and]
      rw [mem_erase] at hy
      exact ⟨Ne.symm hy.1, hy.2⟩
  have aux₂ : ∀ i, P₂ i → #{y | Q₂ i y} = k - 1 := by
    intro i hi
    rw [this, card_erase_of_mem hi, Φ.hA i]
  have count₂ := card_dependent P₂ Q₂ aux₂
  have : #(filter P₁ univ) = v - 1 := by
    rw [filter_ne _ _, ←Φ.hX]
    simp only [mem_univ, card_erase_of_mem, card_univ]
  have swap_condition : ∀ y i, P₁ y ∧ Q₁ y i ↔ P₂ i ∧ Q₂ i y := by tauto
  rwa [card_of_swap swap_condition, count₂, this] at count₁

noncomputable def rep [Inhabited X] (Φ : BIBD X v b k l) : ℕ := by
  let x : X := Classical.choice instNonemptyOfInhabited
  exact rep_elem Φ x

theorem rep_property [Inhabited X] (Φ : BIBD X v b k l) : (k - 1) * rep Φ =  l * (v - 1) := by
  rw [rep, rep_constant]

theorem rep_eq_rep_elem [Inhabited X] : ∀ x, rep_elem Φ x = rep Φ := by
  intro x
  have h := rep_constant Φ x
  rw [←rep_property Φ] at h
  exact Nat.eq_of_mul_eq_mul_left (Nat.zero_lt_sub_of_lt Φ.hvk.2) h

theorem rep_elem_eq_rep_elem : ∀ x y, rep_elem Φ x = rep_elem Φ y := by
  intro x y
  have h := rep_constant Φ x
  rw [←rep_constant Φ y] at h
  exact Nat.eq_of_mul_eq_mul_left (Nat.zero_lt_sub_of_lt Φ.hvk.2) h

theorem blocks_constant : ∀ x, k * b = rep_elem Φ x * v := by
  intro x
  let P₁ : X → Prop := fun _ ↦ True
  let Q₁ : X → Fin b → Prop := fun x i ↦ x ∈ Φ.blocks i
  have aux₁ : ∀ y, P₁ y → #{i | Q₁ y i} = rep_elem Φ x :=
    fun y _ ↦ by rw [rep_elem_eq_rep_elem]; rfl
  have count₁ := card_dependent P₁ Q₁ aux₁
  let P₂ : Fin b → Prop := fun _ ↦ True
  let Q₂ : Fin b → X → Prop := fun i x ↦ x ∈ Φ.blocks i
  have aux₂ : ∀ i, P₂ i → #{y | Q₂ i y} = k :=
    fun i _ ↦ by simp only [filter_univ_mem, Q₂]; exact Φ.hA i
  have count₂ := card_dependent P₂ Q₂ aux₂
  have swap_condition : ∀ y i, P₁ y ∧ Q₁ y i ↔ P₂ i ∧ Q₂ i y := by tauto
  rw [card_of_swap swap_condition, count₂] at count₁
  have : #(filter P₂ univ) = b := by rw [filter_True, card_univ, Fintype.card_fin]
  rw [this] at count₁
  have : #(filter P₁ univ) = v := by simp only [filter_True, filter_univ_mem, P₁]; exact Φ.hX
  rwa [this] at count₁

/-- Useful coercions --/
def BBD_to_Design : (BBD X v b l) → (Design X b) := BBD.toDesign
def RPBD_to_BBD : (r : ℕ) → (RPBD X v b l r) → (BBD X v b l) := (fun _ => RPBD.toBBD)
def RPBD_to_Design : (r : ℕ) → (RPBD X v b l r) → (Design X b) :=
  (fun r => BBD_to_Design ∘ (RPBD_to_BBD r))
def BIBD_to_BBD : (BIBD X v b k l) → (BBD X v b l) := BIBD.toBBD
def BIBD_to_Design : (BIBD X v b k l) → (Design X b) := BBD.toDesign ∘ BIBD.toBBD
def BIBD_to_RPBD :
    [Inhabited X] → (Φ : BIBD X v b k l) → (RPBD X v b l (rep Φ)) := by
  intro P Φ
  constructor
  . exact (rep_eq_rep_elem Φ)

end BalancedIncompleteBlockDesign
