import Mathlib.Data.Fintype.Prod

open Finset
namespace CombinatorialDesign

variable (X) [Fintype X] (v b k l r : ℕ)

structure Design where
  blocks : Fin b → Finset X

def reindexDesign {X Y b b'} (e : X ≃ Y) (hb : b = b') (Φ : Design X b) : Design Y b' where
  blocks i := by
    have g : Fin b' ≃ Fin b := by subst hb; rfl
    exact g i |> Φ.blocks |> Finset.map e.toEmbedding

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

/-- Balanced Incomplete Block Design
  `BIBD X v b k l` is a design on `X`, where `v` is the size of `X`, `b` is the number of blocks,
  `k` is the size of each block, and `l` is the balance number: for any two distinct `x y : X`,
  there are exactly `l` blocks which contain both `x` and `y`.
 -/
structure BIBD extends BBD X v b l where
  hvk : k < v ∧ 2 ≤ k
  hA : ∀ i, #(blocks i) = k

end CombinatorialDesign
