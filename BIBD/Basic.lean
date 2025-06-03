import Mathlib.Data.Set.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Multiset.Basic

universe u

structure Design (X : Type u) where
  mk ::
  blocks : Multiset (Finset X)

structure BIBD (X : Type u) [Fintype X] [DecidableEq X] extends Design X where
  mk ::
  v : ℕ
  k : ℕ
  l : ℕ
  r : ℕ
  hvk : v > k ∧ k ≥ 2
  hr : r * (k - 1) = l * (v - 1)
  hX : Fintype.card X = v
  hA : ∀ B ∈ blocks, Finset.card B = k
  balance : ∀ x y : X, x ≠ y →
    Multiset.countP (fun B ↦ x ∈ B ∧ y ∈ B) blocks = l

variable {X : Type u} [Fintype X] [DecidableEq X] [Fintype (Finset X)] [Fintype (X × Finset X)]

theorem card_dependent {α : Type u} [Fintype α] [DecidableEq α] [Fintype (α × Finset X)] {Φ : BIBD X}
    (P : α → Prop) [DecidablePred P]
    (Q : α → Finset X → Prop) [∀ x, DecidablePred (Q x)]
    (k : ℕ) (hk : ∀ y, P y → Multiset.countP (fun A ↦ Q y A) Φ.blocks = k) :
    Finset.card {(y, A) | P y ∧ Q y A} = k * Finset.card {y | P y} := by
  sorry

theorem card_dependent' {α : Type u} [Fintype α] [DecidableEq α] [Fintype (α × Finset X)] {Φ : BIBD X}
    (P : Finset X → Prop) [DecidablePred P]
    (Q : α → Finset X → Prop) [∀ x, DecidablePred (Q x)]
    (k : ℕ) (hk : ∀ A, P A → Finset.card {y | Q y A} = k) :
    Finset.card {(y, A) | P A ∧ Q y A} = (Multiset.countP P Φ.blocks) * k := by
  sorry

def rep (Φ : BIBD X) (x : X) :=
  Multiset.countP (fun B ↦ x ∈ B) Φ.blocks

theorem rep_constant (Φ : BIBD X) :
    ∀ x : X, rep Φ x = Φ.r := by
  intro x
  let I := {(y, A) | (x ≠ y) ∧ A ∈ Φ.blocks ∧ x ∈ A ∧ y ∈ A}
  let P : X → Prop := fun y ↦ x ≠ y
  let Q : X → Finset X → Prop := fun y A ↦ A ∈ Φ.blocks ∧ x ∈ A ∧ y ∈ A
  have defI : I = (Finset.filter (fun x : X × Finset X => P x.1 ∧ Q x.1 x.2) Finset.univ) := by
    simp_all only [ne_eq, Finset.coe_filter, Finset.mem_univ, true_and, I, P, Q]
  have aux : ∀ y, P y → Multiset.countP (fun A ↦ Q y A) Φ.blocks = Φ.l := by
    intro y hxy
    rw [←Φ.balance x y hxy]
    simp_all only [ne_eq, true_and, I, P, Q]
  have ne_univ_setminus : (Finset.filter P Finset.univ) = Finset.univ.erase x := by
    ext y
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase, ne_comm, ne_eq, and_true]
  have size_P : Finset.card {y | P y} = Φ.v - 1 := by
    rw [ne_univ_setminus, ←Φ.hX, ←Finset.card_univ]
    simp only [Finset.mem_univ, Finset.card_erase_of_mem, Finset.card_univ]
  have count₁ := card_dependent P Q Φ.l aux
  rw [size_P] at count₁
  simp only at count₁
  let P' : Finset X → Prop := fun A ↦ A ∈ Φ.blocks ∧ x ∈ A
  let Q' : X → Finset X → Prop := fun y A ↦ x ≠ y ∧ y ∈ A
  --have defI' : I = {(y, A) | P' A ∧ Q' y A} := by aesop
  have : ∀ A, (Finset.filter (fun y => Q' y A) Finset.univ) = A.erase x := by
    aesop -- TODO: get rid of this
  have aux' : ∀ A, P' A → Finset.card {y | Q' y A} = Φ.k - 1 := by
    intro A hA
    rw [this A, ←Φ.hA A (hA.1)]
    simp_all only [Finset.coe_filter, Finset.mem_univ, Finset.card_erase_of_mem, Finset.card_univ, I,
      P, Q, Q', P']
  have count₂ := card_dependent' (Φ := Φ) P' Q' (Φ.k - 1) aux'
  have count_P' : Multiset.countP P' Φ.blocks = rep Φ x := by
    simp_all only [ne_eq, Finset.coe_filter, Finset.mem_univ, true_and, Finset.card_erase_of_mem, Finset.card_univ,
      and_imp, I, P, Q, Q', P']
    rfl
  rw [count_P'] at count₂
  simp only at count₂
  have compare_counts : (Finset.filter (fun x : X × Finset X ↦ P x.1 ∧ Q x.1 x.2) Finset.univ)
      = (Finset.filter (fun x => P' x.2 ∧ Q' x.1 x.2) Finset.univ) := by
    aesop -- TODO: get rid of this
  rw [compare_counts, count₂, ←Φ.hr] at count₁
  exact Nat.eq_of_mul_eq_mul_right (Nat.zero_lt_sub_of_lt Φ.hvk.2) count₁
