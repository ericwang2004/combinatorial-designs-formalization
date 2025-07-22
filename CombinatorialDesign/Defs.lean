import Mathlib.Data.Fintype.Prod

open Finset
namespace CombinatorialDesign

variable (ι X : Type*) [Fintype ι] [Fintype X] (k l r : ℕ)

structure Design where
  blocks : ι → Finset X

def reindexDesign {X Y ι ι' : Type*} (e : X ≃ Y) (hι : ι' ≃ ι) (Φ : Design ι X) : Design ι' Y where
  blocks i := hι i |> Φ.blocks |> Finset.map e.toEmbedding

variable [DecidableEq X]

/-- Balanced Block Design -/
structure BBD extends Design ι X where
  balance : ∀ x y, x ≠ y → #{i | x ∈ blocks i ∧ y ∈ blocks i} = l

/-- Regular Pairwise Balanced Design -/
structure RPBD extends BBD ι X l where
  regularity : ∀ x, #{i | x ∈ blocks i} = r

structure nontrivialRPBD extends RPBD ι X l r where
  nontrivial : ∃ i, 0 < #(blocks i) ∧ #(blocks i) < Fintype.card X

/-- Balanced Incomplete Block Design
  `BIBD ι X k l` is a design on a fintype `X` with `#ι` many blocks ,
  `k` is the size of each block, and `l` is the balance number:
  for any two distinct `x y : X`, there are exactly `l` blocks which
  contain both `x` and `y`.
 -/
structure BIBD extends BBD ι X l where
  hvk : k < Fintype.card X ∧ 2 ≤ k
  hA : ∀ i, #(blocks i) = k

end CombinatorialDesign
