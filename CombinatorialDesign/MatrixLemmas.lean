import Mathlib.Data.Matrix.Rank
import Mathlib.Data.Finset.Basic

open Matrix Finset

def allOnes (m n α) [One α] : Matrix m n α :=
  of (fun _ _ ↦ 1)

def isZeroOne {m n} {α} [One α] [Zero α] (M : Matrix m n α) : Prop :=
  ∀ i j, M i j = 0 ∨ M i j = 1

/-- ### Matrix Determinant Lemma -/
theorem det_one_add_column_mul_row {α n} [CommRing α] [Fintype n] [DecidableEq n]
    (u : Matrix n (Fin 1) α) (v : Matrix (Fin 1) n α) : det (1 + u * v) = 1 + (v * u) 0 0 := by
  let A := fromBlocks (1 : Matrix n n α) 0 v (1 : Matrix (Fin 1) (Fin 1) α)
  let B := fromBlocks (1 + u * v) u 0 (1 : Matrix (Fin 1) (Fin 1) α)
  let C := fromBlocks (1 : Matrix n n α) 0 (-v) (1 : Matrix (Fin 1) (Fin 1) α)
  let D := fromBlocks (1 : Matrix n n α) u 0 (1 + v * u)
  have detA : det A = 1 := by
    simp only [A, det_fromBlocks_zero₁₂, det_one, mul_one]
  have detB : det B = det (1 + u * v) := by
    simp only [B, det_fromBlocks_zero₂₁, det_unique, one_apply_eq, mul_one]
  have detC : det C = 1 := by
    simp only [C, det_fromBlocks_zero₁₂, det_one, det_unique, one_apply_eq, mul_one]
  have detD : det D = 1 + (v * u) 0 0 := by
    simp only [det_fromBlocks_zero₂₁, det_one, det_unique, Fin.default_eq_zero, Fin.isValue,
      add_apply, one_apply_eq, one_mul, D]
  have hABCD : A * B * C = D := by
    simp only [A, B, C, D, fromBlocks_multiply, one_mul, Matrix.mul_zero, add_zero,
      mul_one, Matrix.one_mul, Matrix.mul_one, Matrix.mul_neg, add_neg_cancel_right,
      zero_add, fromBlocks_inj, true_and]
    constructor
    · rw [Matrix.mul_add, Matrix.mul_one, Matrix.add_mul, neg_add, Matrix.one_mul, add_comm v,
        add_assoc, add_comm _ (-v), ←add_assoc v, add_neg_cancel, zero_add, ←Matrix.mul_assoc,
        add_neg_cancel]
    · rw [add_comm]
  calc
    det (1 + u * v) = det A * det B * det C := by rw [detA, detB, detC, one_mul, mul_one]
    _ = det (A * B * C) := by simp only [det_mul]
    _ = det D := by rw [hABCD]
    _ = 1 + (v * u) 0 0 := by rw [detD]

theorem det_ones_add_diagonal {α} (n) [Field α] [Fintype n] [DecidableEq n] (a b : α) (hb : b ≠ 0) :
    det (a • allOnes n n α + b • 1) = b ^ Fintype.card n * (1 + a / b * Fintype.card n) := by
  let u := allOnes n (Fin 1) α
  let v := allOnes (Fin 1) n α
  have expr : a • allOnes n n α + b • 1 = b • (1 + ((a / b) • u) * v) := by
    ext
    simp only [add_apply, smul_apply, smul_eq_mul, smul_mul, one_apply, allOnes, of_apply,
      mul_apply, mul_one, mul_ite, mul_zero, univ_unique, Fin.default_eq_zero, Fin.isValue,
      sum_singleton, u, v]
    rw [mul_add, mul_ite, mul_one, mul_zero, add_comm, mul_div_cancel₀ _ hb]
  have v_mul_u : v * u = Fintype.card n • allOnes (Fin 1) (Fin 1) α := by
    ext
    simp only [mul_apply, allOnes, v, u, mul_one, sum_const, card_univ,
      nsmul_eq_mul, smul_apply, of_apply]
  have det_expr := (det_one_add_column_mul_row ((a / b) • u) v)
  simp only [smul_mul, Fin.isValue, Matrix.mul_smul, smul_apply, smul_eq_mul,
    v_mul_u, allOnes, smul_eq_mul, mul_one, of_apply, ] at det_expr
  simp only [nsmul_eq_mul, mul_one] at det_expr
  calc
    det (a • allOnes n n α + b • 1) = det (b • (1 + (a / b) • (u * v))) := by rw [expr, smul_mul, smul_add]
    _ = b ^ Fintype.card n * det (1 + (a / b) • (u * v)) := by rw [det_smul]
    _ = b ^ Fintype.card n * (1 + a / b * Fintype.card n) := by rw [det_expr]

theorem rank_ones_add_diagonal {α n} [Field α] [Fintype n] [DecidableEq n]
    (a b : α) (hb : b ≠ 0) (hab : 1 + a / b * Fintype.card n ≠ 0) :
    rank (a • allOnes n n α + b • 1) = Fintype.card n := by
  apply rank_of_isUnit
  rw [isUnit_iff_isUnit_det, det_ones_add_diagonal n a b hb, isUnit_iff_ne_zero]
  exact mul_ne_zero (pow_ne_zero _ hb) hab

theorem isUnit_of_full_rank {n α} [Fintype n] [DecidableEq n] [Field α]
    {A : Matrix n n α} (h : A.rank = Fintype.card n) : IsUnit A := by
  rw [←linearIndependent_rows_iff_isUnit, linearIndependent_iff_card_eq_finrank_span,
    ←h, rank_eq_finrank_span_row]
  rfl

theorem eq_of_full_rank_mul_eq {n m o α} [Fintype n] [Fintype m] [DecidableEq m] [Fintype o]
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

structure MatCongr {m n α} [Fintype m] [DecidableEq m] [CommRing α]
    (N : Matrix n n α) (M : Matrix m m α) extends n ≃ m where
  A : Matrix m m α
  inv : Invertible A
  cong : N.submatrix invFun invFun = A * M * Aᵀ

infixl:25 " ∼ₘ " => MatCongr

namespace MatCongr

variable {l m n α : Type*} [Fintype l] [DecidableEq l] [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
  [CommRing α] {M : Matrix l l α} {N : Matrix m m α} {P : Matrix n n α}

@[symm] protected def symm (c : M ∼ₘ N) : N ∼ₘ M :=
  have := c.inv
  have := c.cong
  {
    toEquiv := c.toEquiv.symm
    A := (⅟c.A).submatrix c.toFun c.toFun
    inv := submatrixEquivInvertible _ c.toEquiv c.toEquiv
    cong := sorry
  }

@[refl] protected def refl (M : Matrix n n α) : M ∼ₘ M where
  toEquiv := Equiv.refl n
  A := 1
  inv := invertibleOne
  cong := by rw [transpose_one, one_mul, mul_one]; rfl

@[trans] protected def trans (c₁ : M ∼ₘ N) (c₂ : N ∼ₘ P) : M ∼ₘ P where
  toEquiv := Equiv.trans c₁.toEquiv c₂.toEquiv
  A := sorry
  inv := sorry
  cong := sorry

def matDirectSum {l m n o} (A : Matrix l m α) (B : Matrix n o α) := fromBlocks A 0 0 B

infixl:30 " ⊕ₘ " => matDirectSum

def oplus_assoc : M ⊕ₘ N ⊕ₘ P ∼ₘ M ⊕ₘ (N ⊕ₘ P) :=
  sorry

def congrOneOfFourDiv (hn : 4 ∣ Fintype.card n)
    (m : ℤ) (mpos : m > 0) : m • (1 : Matrix n n α) ∼ₘ (1 : Matrix n n α) := by
  sorry

/-- ## Witt cancellation lemma
 - from BW Jones: `The Arithmetic Theory Of Quadratic Forms`, chapter 1
-/
def oplus_left_cancel [Field α] [CharZero α] {A B : Matrix n n α} {C : Matrix m m α}
    (hA : A = Aᵀ) (hB : B = Bᵀ) (hC : C = Cᵀ) (h : C ⊕ₘ A ∼ₘ C ⊕ₘ B) : A ∼ₘ B :=
  sorry

end MatCongr
