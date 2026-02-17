import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Data.Finset.Basic
import Mathlib.NumberTheory.SumFourSquares

/-!

This file proves some lemmas about matrices that are helpful
for proving Fisher's inequality. Most notably, we prove the
following theorem:

Thm. Let 𝔽 be a field and a, b ∈ 𝔽 with b ≠ 0. Then
  det (aJ + bI) = bⁿ(1 + an/b),
where I, J ∈ 𝔽^(n × n) are the identity and all-ones matrices.

-/

open Matrix Finset

def allOnes (m n α : Type*) [One α] : Matrix m n α :=
  of (fun _ _ ↦ 1)

def isZeroOne {m n α : Type*} [One α] [Zero α] (M : Matrix m n α) : Prop :=
  ∀ i j, M i j = 0 ∨ M i j = 1

theorem det_ones_add_diagonal {α : Type*} (n : Type*) [Field α] [Fintype n] [DecidableEq n]
    (a b : α) (hb : b ≠ 0) :
    det (a • allOnes n n α + b • 1) = b ^ Fintype.card n * (1 + a / b * Fintype.card n) := by
  have key : a • allOnes n n α + b • 1 =
      b • (1 + replicateCol (Fin 1) (fun _ : n => a / b) * replicateRow (Fin 1) (1 : n → α)) := by
    ext i j
    simp only [add_apply, smul_apply, smul_eq_mul, one_apply, allOnes, of_apply,
      mul_apply, replicateCol_apply, replicateRow_apply, mul_one, univ_unique, sum_singleton,
      mul_add, mul_ite, mul_zero, Pi.one_apply]
    field_simp
    ring
  rw [key, det_smul, det_one_add_replicateCol_mul_replicateRow, one_dotProduct,
    sum_const, card_univ, nsmul_eq_mul]
  ring

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
