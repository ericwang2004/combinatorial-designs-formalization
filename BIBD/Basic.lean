import Mathlib.Data.Set.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Multiset.Basic

universe u

open Multiset Finset Fintype

structure Design (X : Type u) where
  mk ::
  blocks : Multiset (Finset X)

structure BIBD (X : Type u) [Fintype X] [DecidableEq X] extends Design X where
  mk ::
  v : ℕ
  k : ℕ
  l : ℕ
  hvk : v > k ∧ k ≥ 2
  hX : card X = v
  hA : ∀ B ∈ blocks, Finset.card B = k
  balance : ∀ x y : X, x ≠ y →
    Multiset.countP (fun B ↦ x ∈ B ∧ y ∈ B) blocks = l

variable {X : Type u} [Fintype X] [DecidableEq X]

def pointOccurrences (Φ : BIBD X) (x : X) :=
  countP (fun B ↦ x ∈ B) Φ.blocks

theorem pointOccurrences_constant (Φ : BIBD X) :
    ∃ r, ∀ x : X, pointOccurrences Φ x = r := by
  sorry
