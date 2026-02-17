import Mathlib.Data.Fintype.Prod

/-!

# The Combinatorial Design Hierarchy

This files states the basic definitions of combinatorial design theory.
The most commonly used ones are the following:

Def. A *design* Φ is a pair (X, A) where X is a finite set (of *points*)
and A is a collection of subsets (*blocks*) of X.

Def. Let 2 ≤ k < v. A *balanced incomplete block design* (BIBD)
is a design (X, A) where
  * #X = v
  * Each block contains exactly k points
  * Every pair of distinct points are contained in λ blocks

-/

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

structure differenceSet where
  elems : ι → G
  elems_unique : Function.Injective elems
  hvk : Fintype.card ι < Fintype.card G ∧ 2 ≤ Fintype.card ι
  balance : ∀ x : G, x ≠ 0 → #{(i, j) : ι × ι | elems i - elems j = x} = l

end CombinatorialDesign
