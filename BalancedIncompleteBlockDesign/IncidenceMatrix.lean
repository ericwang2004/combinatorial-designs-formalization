import BalancedIncompleteBlockDesign.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic.Ring

open BalancedIncompleteBlockDesign Matrix Finset Fintype
namespace BalancedIncompleteBlockDesign

variable {X : Type*} [Fintype X] [DecidableEq X] {v b k l : ℕ} (Φ : BIBD X v b k l)
variable {R : Type*} [Ring R]

def toIncMat (Φ : BIBD X v b k l) : Matrix X (Fin b) R :=
  of (fun x i ↦ if x ∈ Φ.blocks i then 1 else 0)

def allOnes (m n : Type*) [Fintype m] [Fintype n] (α : Type*) [One α] : Matrix m n α :=
  of (fun _ _ ↦ 1)

def bibdCondition (k l r : ℕ) (M : Matrix X (Fin b) R) : Prop :=
  (allOnes (Fin 1) X R) * M = k • (allOnes (Fin 1) (Fin b) R) ∧
  M * Mᵀ = l • (allOnes X X R) + ((r : R) - l) • 1

theorem bibdCondition_of_bibd : ∀ x,
    bibdCondition (R := R) k l (rep Φ x) (toIncMat Φ) := by
  intro i
  constructor
  · ext i j
    simp only [toIncMat, allOnes, mul_apply, of_apply, smul_apply, one_mul,
      Finset.sum_ite_mem, univ_inter, sum_const, nsmul_eq_mul, mul_one, Φ.hA]
  ext x y
  simp only [toIncMat, allOnes, one_apply, mul_apply, add_apply, transpose_apply, of_apply,
    smul_apply, mul_ite, mul_one, mul_zero]
  by_cases hxy : x = y
  · subst hxy
    simp only [nsmul_eq_mul, mul_one, reduceIte, smul_eq_mul, add_sub_cancel]
    rw [sum_congr _ (fun i ↦ if x ∈ Φ.blocks i then 1 else 0) (fun _ ↦ by simp_all only [reduceIte]),
      sum_boole, ←rep, rep_eq_rep _ i x]
  · simp only [nsmul_eq_mul, mul_one, smul_eq_mul, mul_ite, mul_zero, hxy, reduceIte, add_zero]
    rw [sum_congr _ (fun i ↦ if y ∈ Φ.blocks i ∧ x ∈ Φ.blocks i then 1 else 0)
      (fun _ ↦ Eq.symm (ite_and _ _ _ _)), sum_boole, Φ.balance _ _ (Ne.symm hxy)]

theorem bibd_of_bibdCondition (k l r : ℕ) {M : Matrix X (Fin b) R} (hM : bibdCondition k l r M) :
    ∃ Ψ : BIBD X v b k l, M = toIncMat Ψ := by
  sorry

end BalancedIncompleteBlockDesign
