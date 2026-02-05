import Mathlib.Data.Fintype.Prod

open Finset
namespace CombinatorialDesign

variable (ι X G : Type*) [Fintype G] [DecidableEq G] [AddGroup G]
  [Fintype ι] [Fintype X] (t k l r : ℕ)

/-- Design: a collection of finite subsets of a given set X-/
structure Design where
  blocks : ι → Finset X

def reindexDesign {X Y ι ι' : Type*} (e : X ≃ Y) (hι : ι' ≃ ι)
    (Φ : Design ι X) : Design ι' Y where
  blocks i := hι i |> Φ.blocks |> Finset.map e.toEmbedding

variable [DecidableEq X]

/-- Block Design: all blocks have the same size k -/
structure BlockDesign extends Design ι X where
  uniform : ∀ i, #(blocks i) = k

/-- Regular Design: each point appears in exactly r blocks -/
structure RegularDesign extends Design ι X where
  regularity : ∀ x, #{i | x ∈ blocks i} = r

/-- t-wise Balanced Design: any t distinct points appear together in exactly λ blocks -/
structure BalancedDesign extends Design ι X where
  balance : ∀ s : Finset X, #s = t → #{i | s ⊆ blocks i} = l

/-- Pairwise Balanced Design: 2-wise balanced design -/
abbrev PBD := BalancedDesign ι X 2 l

/-- Incomplete Design: block size is strictly less than the number of points -/
structure IncompleteDesign extends BlockDesign ι X k where
  incomplete : k < Fintype.card X

/-- Regular Pairwise Balanced Design: both regular and 2-wise balanced -/
structure RPBD extends RegularDesign ι X r, BalancedDesign ι X 2 l where

structure nontrivialRPBD extends RPBD ι X l r where
  nontrivial : ∃ i, 0 < #(blocks i) ∧ #(blocks i) < Fintype.card X

/-- T-Design: t-wise Balanced incomplete design with t ≤ k -/
structure TDesign extends IncompleteDesign ι X k, BalancedDesign ι X t l where
  t_le_k : t ≤ k

/-- Balanced Incomplete Block Design: 2-Design -/
abbrev BIBD := TDesign ι X 2 k l

structure differenceSet where
  elems : ι → G
  elems_unique : Function.Injective elems
  hvk : Fintype.card ι < Fintype.card G ∧ 2 ≤ Fintype.card ι
  balance : ∀ x : G, x ≠ 0 → #{(i, j) : ι × ι | elems i - elems j = x} = l

end CombinatorialDesign
