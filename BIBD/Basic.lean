import Mathlib.Data.Set.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Card

open Finset

structure Design (X : Type*) where
  mk ::
  b : ℕ
  blocks : Fin b → Finset X

structure BIBD (X : Type*) [Fintype X] [DecidableEq X] extends Design X where
  mk ::
  v : ℕ
  k : ℕ
  l : ℕ
  r : ℕ
  hvk : v > k ∧ k ≥ 2
  hX : Fintype.card X = v
  hA : ∀ i : Fin b, #(blocks i) = k
  balance : ∀ x y : X, x ≠ y → #{i | x ∈ blocks i ∧ y ∈ blocks i} = l

variable {X : Type*} [Fintype X] [DecidableEq X] {Φ : BIBD X}

def rep (Φ : BIBD X) (x : X) := #{i | x ∈ Φ.blocks i}

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
  apply Finset.card_bij (fun (x, y) hxy ↦ by
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

theorem rep_constant : ∀ x : X, (Φ.k - 1) * rep Φ x = Φ.l * (Φ.v - 1) := by
  intro x
  let P₁ : X → Prop := fun y ↦ x ≠ y
  let Q₁ : X → Fin Φ.b → Prop := fun y i ↦ x ∈ Φ.blocks i ∧ y ∈ Φ.blocks i
  have aux₁ : ∀ y, P₁ y → #{i | Q₁ y i} = Φ.l := Φ.balance x
  have count₁ := card_dependent P₁ Q₁ aux₁
  let P₂ : Fin Φ.b → Prop := fun i ↦ x ∈ Φ.blocks i
  let Q₂ : Fin Φ.b → X → Prop := fun i y ↦ x ≠ y ∧ y ∈ Φ.blocks i
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
  have aux₂ : ∀ i, P₂ i → #{y | Q₂ i y} = Φ.k - 1 := by
    intro i hi
    rw [this, ←Φ.hA i, card_erase_of_mem hi]
  have count₂ := card_dependent P₂ Q₂ aux₂
  have card_swap : #(filter (fun (y, i) ↦ P₁ y ∧ Q₁ y i) univ)
      = #(filter (fun (i, y) ↦ P₂ i ∧ Q₂ i y) univ) := by
    apply Finset.card_bij (fun (i, y) _ ↦ (y, i))
    · intro ⟨y, i⟩ hyi
      simp only [mem_filter, mem_univ, true_and] at hyi ⊢
      exact and_left_comm.mp hyi
    · intro ⟨y₁, i₁⟩ hyi₁ ⟨y₂, i₂⟩ hyi₂
      simp only [mem_filter, mem_univ, true_and] at hyi₁ hyi₂
      simp only [Prod.mk.injEq, and_imp]
      exact fun hi hy ↦ ⟨hy, hi⟩
    · intro ⟨i, y⟩ hiy
      simp only [mem_filter, mem_univ, true_and] at hiy
      use (y, i)
      simp only [mem_filter, mem_univ, true_and, exists_prop, and_true]
      exact and_left_comm.mp hiy
  have : #(filter P₁ univ) = Φ.v - 1 := by
    rw [filter_ne _ _, ←Φ.hX]
    simp only [mem_univ, card_erase_of_mem, card_univ]
  rwa [card_swap, count₂, this] at count₁
