import Mathlib.Data.Fintype.Prod

/-!
# Combinatorial Design Hierarchy

This file defines the basic structures of combinatorial design theory, building up
from a simple design to t-designs and BIBDs.

## Main Definitions

* `Design ι X` - A pair (X, A) where X is a finite set of points and A is a collection of
  subsets (blocks) of X, indexed by ι
* `TDesign ι X t k l` - A t-(v, k, λ) design: a design on v points where each block has
  exactly k points, k < v, and every set of t points appears together in exactly λ blocks
* `BIBD ι X k l` - A balanced incomplete block design is a 2-(v, k, λ) design

## References

* Stinson, Combinatorial Designs, Constructions and Analysis
-/

open Finset
namespace CombinatorialDesign

variable (ι X G : Type*) [Fintype G] [DecidableEq G] [AddGroup G]
  [Fintype ι] [Fintype X] (t k l r : ℕ)

/-- A design is a collection of finite subsets (blocks) of a set X, indexed by ι -/
structure Design where
  blocks : ι → Finset X

/-- Reindex a design by applying equivalences on points and block indices -/
def reindexDesign {X Y ι ι' : Type*} (e : X ≃ Y) (hι : ι' ≃ ι)
    (Φ : Design ι X) : Design ι' Y where
  blocks i := hι i |> Φ.blocks |> Finset.map e.toEmbedding

variable [DecidableEq X]

/-- A block design is a design where all blocks have the same size k -/
structure BlockDesign extends Design ι X where
  uniform : ∀ i, #(blocks i) = k

/-- A regular design is a design where each point appears in exactly r blocks -/
structure RegularDesign extends Design ι X where
  regularity : ∀ x, #{i | x ∈ blocks i} = r

/-- A t-wise balanced design is a design where any t points appear together in exactly λ blocks -/
structure BalancedDesign extends Design ι X where
  balance : ∀ s : Finset X, #s = t → #{i | s ⊆ blocks i} = l

/-- A pairwise balanced design: a 2-wise balanced design -/
abbrev PBD := BalancedDesign ι X 2 l

/-- An incomplete design is a block design with block size strictly less than the number of points -/
structure IncompleteDesign extends BlockDesign ι X k where
  incomplete : k < Fintype.card X

/-- A regular pairwise balanced design: both regular and 2-wise balanced -/
structure RPBD extends RegularDesign ι X r, BalancedDesign ι X 2 l where

/-- A nontrivial RPBD: an RPBD with at least one block of size strictly between 0 and |X| -/
structure nontrivialRPBD extends RPBD ι X l r where
  nontrivial : ∃ i, 0 < #(blocks i) ∧ #(blocks i) < Fintype.card X

/-- A t-design is a t-wise balanced incomplete block design with t ≤ k -/
structure TDesign extends IncompleteDesign ι X k, BalancedDesign ι X t l where
  t_le_k : t ≤ k

/-- A balanced incomplete block design (BIBD): a 2-design -/
abbrev BIBD := TDesign ι X 2 k l

/-- Reindex a BIBD by applying equivalences on points and block indices -/
def reindexBIBD {ι ι' X Y : Type*} {k l : ℕ}
    [Fintype ι] [Fintype X] [DecidableEq X]
    [Fintype ι'] [Fintype Y] [DecidableEq Y]
    (e : X ≃ Y) (hι : ι' ≃ ι)
    (Φ : BIBD ι X k l) : BIBD ι' Y k l where
  blocks := (reindexDesign e hι Φ.toDesign).blocks
  uniform i := by simp_rw [←Φ.uniform (hι i), reindexDesign, card_map]
  incomplete := by
    rw [Fintype.card_congr (id e.symm)]
    exact Φ.incomplete
  balance s hs := by
    have aux := Φ.balance (map (id e.symm).toEmbedding s) (by rw [←hs]; apply card_map)
    simp_rw [←aux]
    apply card_bij (fun i hi ↦ hι i)
    · intro i hi
      simp only [mem_filter, mem_univ, true_and, id_eq] at hi ⊢
      intro x hx
      simp only [mem_map_equiv, Equiv.symm_symm] at hx
      have := hi hx
      simp only [reindexDesign, mem_map_equiv, Equiv.symm_apply_apply] at this
      exact this
    · intro _ _ _ _ hi
      exact (EmbeddingLike.apply_eq_iff_eq hι).mp hi
    intro i hi
    use hι.invFun i
    use (by
      simp only [id_eq, mem_filter, mem_univ, true_and, reindexDesign,
        Equiv.invFun_as_coe, Equiv.apply_symm_apply] at hi ⊢
      intro x hx
      rw [mem_map_equiv]
      apply hi
      simp only [mem_map_equiv, Equiv.symm_symm, Equiv.apply_symm_apply]
      exact hx
    )
    exact (Equiv.apply_eq_iff_eq_symm_apply hι).mpr rfl
  t_le_k := Φ.t_le_k

/-! ## Difference Sets

A difference set is a subset of a group where every nonzero group element can be represented
as a difference of elements from the set in exactly λ ways.
-/

/-- A (v, k, λ)-difference set in a group G -/
structure differenceSet where
  elems : ι → G
  elems_unique : Function.Injective elems
  hvk : Fintype.card ι < Fintype.card G ∧ 2 ≤ Fintype.card ι
  balance : ∀ x : G, x ≠ 0 → #{(i, j) : ι × ι | elems i - elems j = x} = l

end CombinatorialDesign
