import Mathlib.Data.Fintype.Prod

open Finset
namespace CombinatorialDesign

variable (X) [Fintype X] (v b k l r : ℕ)

structure Design where
  blocks : Fin b → Finset X

variable [DecidableEq X]

/-- Balanced Block Design -/
structure BBD extends Design X b where
  hX : Fintype.card X = v
  balance : ∀ x y, x ≠ y → #{i | x ∈ blocks i ∧ y ∈ blocks i} = l

/-- Regular Pairwise Balanced Design -/
structure RPBD extends BBD X v b l where
  regularity : ∀ x, #{i | x ∈ blocks i} = r

structure nontrivialRPBD extends RPBD X v b l r where
  nontrivial : ∃ i, 0 < #(blocks i) ∧ #(blocks i) < v

/-- Balanced Incomplete Block Design -/
structure BIBD extends BBD X v b l where
  hvk : v > k ∧ k ≥ 2
  hA : ∀ i, #(blocks i) = k

end CombinatorialDesign
