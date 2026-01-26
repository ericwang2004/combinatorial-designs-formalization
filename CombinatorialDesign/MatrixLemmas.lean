import Mathlib.Data.Matrix.Rank
import Mathlib.Data.Finset.Basic

import Mathlib.NumberTheory.SumFourSquares
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.SchurComplement

open Matrix Finset

def allOnes (m n α : Type*) [One α] : Matrix m n α :=
  of (fun _ _ ↦ 1)

def isZeroOne {m n α : Type*} [One α] [Zero α] (M : Matrix m n α) : Prop :=
  ∀ i j, M i j = 0 ∨ M i j = 1

/-- ### Matrix Determinant Lemma -/
theorem det_one_add_column_mul_row {α n : Type*} [CommRing α] [Fintype n] [DecidableEq n]
    (u : Matrix n (Fin 1) α) (v : Matrix (Fin 1) n α) : det (1 + u * v) = 1 + (v * u) 0 0 := by
  let u' : n → α := fun i => u i 0
  let v' : n → α := fun j => v 0 j
  have hu : u = replicateCol (Fin 1) u' := by
    ext i j
    fin_cases j
    simp [u', replicateCol]
  have hv : v = replicateRow (Fin 1) v' := by
    ext i j
    fin_cases i
    simp [v', replicateRow]
  simp only [hv, hu, det_one_add_replicateCol_mul_replicateRow, replicateRow_mul_replicateCol_apply]

theorem det_ones_add_diagonal {α : Type*} (n : Type*) [Field α] [Fintype n] [DecidableEq n]
    (a b : α) (hb : b ≠ 0) :
    det (a • allOnes n n α + b • 1) = b ^ Fintype.card n * (1 + a / b * Fintype.card n) := by
  let u := allOnes n (Fin 1) α
  let v := allOnes (Fin 1) n α
  have expr : a • allOnes n n α + b • 1 = b • (1 + ((a / b) • u) * v) := by
    ext
    simp only [add_apply, smul_apply, smul_eq_mul, smul_mul, one_apply, allOnes, of_apply,
      mul_apply, mul_one, mul_zero, univ_unique, sum_singleton, u, v]
    rw [mul_add, mul_ite, mul_one, mul_zero, add_comm, mul_div_cancel₀ _ hb]
  have v_mul_u : v * u = Fintype.card n • allOnes (Fin 1) (Fin 1) α := by
    ext
    simp only [mul_apply, allOnes, v, u, mul_one, sum_const, card_univ,
      nsmul_eq_mul, smul_apply, of_apply]
  have det_expr := (det_one_add_column_mul_row ((a / b) • u) v)
  simp only [smul_mul, Matrix.mul_smul, smul_apply, smul_eq_mul,
    v_mul_u, allOnes, smul_eq_mul, mul_one, of_apply, ] at det_expr
  simp only [nsmul_eq_mul, mul_one] at det_expr
  calc
    det (a • allOnes n n α + b • 1) = det (b • (1 + (a / b) • (u * v))) := by rw [expr, smul_mul, smul_add]
    _ = b ^ Fintype.card n * det (1 + (a / b) • (u * v)) := by rw [det_smul]
    _ = b ^ Fintype.card n * (1 + a / b * Fintype.card n) := by rw [det_expr]

theorem rank_ones_add_diagonal {n α : Type*} [Field α] [Fintype n] [DecidableEq n]
    (a b : α) (hb : b ≠ 0) (hab : 1 + a / b * Fintype.card n ≠ 0) :
    rank (a • allOnes n n α + b • 1) = Fintype.card n := by
  apply rank_of_isUnit
  rw [isUnit_iff_isUnit_det, det_ones_add_diagonal n a b hb, isUnit_iff_ne_zero]
  exact mul_ne_zero (pow_ne_zero _ hb) hab

theorem isUnit_of_full_rank {n α : Type*} [Fintype n] [DecidableEq n] [Field α]
    {A : Matrix n n α} (h : A.rank = Fintype.card n) : IsUnit A := by
  rw [←linearIndependent_rows_iff_isUnit, linearIndependent_iff_card_eq_finrank_span,
    ←h, rank_eq_finrank_span_row]
  rfl

theorem eq_of_full_rank_mul_eq {n m o α : Type*} [Fintype n] [Fintype m] [DecidableEq m] [Fintype o]
    [Field α] {A : Matrix n m α} {B₁ B₂ : Matrix m o α} (f : n ≃ m)
    (rankA : rank A = Fintype.card m) (h : A * B₁ = A * B₂) : B₁ = B₂ := by
  let A' := reindex f (Equiv.refl _) A
  have h' : A' * B₁ = A' * B₂ := by
    ext i' j
    rw [←Matrix.ext_iff] at h
    specialize h (f.symm i') j
    rwa [mul_apply] at h
  have rankA' : rank A' = Fintype.card m := by rw [←rankA]; apply rank_reindex
  obtain ⟨⟨_, A₁, _, hA₁⟩, rfl⟩ := isUnit_of_full_rank rankA'
  calc
    B₁ = A₁ * A' * B₁ := by rw [hA₁, Matrix.one_mul]
    _ = B₂ := by rw [Matrix.mul_assoc, h', ←Matrix.mul_assoc, hA₁, Matrix.one_mul]
