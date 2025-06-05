import Mathlib.Data.Set.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Multiset.Basic

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

variable {X : Type*} [Fintype X] [DecidableEq X] {Φ : BIBD X} [Fintype (X × Fin Φ.b)] [Fintype (Fin Φ.b × X)]

def rep (Φ : BIBD X) (x : X) := #{i | x ∈ Φ.blocks i}

#check Finset.equivFin
theorem card_dependent {α : Type*} [Fintype α] {β : Type*} [Fintype β] [Fintype (α × β)]
    (P : α → Prop) [DecidablePred P]
    (Q : α → β → Prop) [∀ x, DecidablePred (Q x)]
    {k : ℕ} (hk : ∀ x, P x → #{y | Q x y} = k) :
    #{(x, y) | P x ∧ Q x y} = k * #{x | P x} := by
  sorry

theorem rep_constant : ∀ x : X, (Φ.k - 1) * rep Φ x = Φ.l * (Φ.v - 1) := by
  intro x
  let I : Finset (X × Fin Φ.b) := {(y, i) : X × Fin Φ.b | x ≠ y ∧ x ∈ Φ.blocks i ∧ y ∈ Φ.blocks i}
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
