import BalancedIncompleteBlockDesign.IncidenceMatrix
import Mathlib.Data.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
--import Mathlib.Data.Real.Basic

open BalancedIncompleteBlockDesign Matrix Finset
variable {X : Type*} [Fintype X] [DecidableEq X] {v b l r : ℕ}

namespace BalancedIncompleteBlockDesign

theorem det_one_add_column_mul_row {α n : Type*} [CommRing α] [Fintype n] [DecidableEq n]
    (u : Matrix n (Fin 1) α) (v : Matrix (Fin 1) n α) :
    det (1 + u * v) = 1 + (v * u) 0 0 := by
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
    · ext i j
      have i_eq_zero := Fin.fin_one_eq_zero i
      subst i_eq_zero
      simp only [add_apply, mul_apply, neg_apply, zero_apply, Fin.isValue, univ_unique,
        Fin.default_eq_zero, sum_singleton, one_apply_eq]
      rw [Mathlib.Tactic.RingNF.add_neg, sub_eq_zero, add_mul, one_mul, Finset.sum_mul]
      simp_rw [mul_add, ←mul_assoc]
      rw [Finset.sum_add_distrib, add_comm]
      congr
      rw [Fintype.sum_eq_single j]
      · simp only [one_apply, reduceIte, mul_one]
      · intro b hb
        simp only [one_apply, mul_ite, mul_one, mul_zero, ite_eq_right_iff]
        exact fun hb' ↦ False.elim (hb hb')
    · rw [add_comm]
  calc
    det (1 + u * v) = det A * det B * det C := by rw [detA, detB, detC, one_mul, mul_one]
    _ = det (A * B * C) := by simp only [det_mul]
    _ = det D := by rw [hABCD]
    _ = 1 + (v * u) 0 0 := by rw [detD]

theorem rank_ones_add_diagonal {α n : Type*} [Field α]
    [Fintype n] [DecidableEq n] (a b : α) (hb : b ≠ 0) (hab : 1 + a / b * Fintype.card n ≠ 0) :
    rank (a • allOnes n n α + b • 1) = Fintype.card n := by
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
  have := calc
    det (a • allOnes n n α + b • 1) = det (b • (1 + (a / b) • (u * v))) := by rw [expr, smul_mul, smul_add]
    _ = b ^ Fintype.card n * det (1 + (a / b) • (u * v)) := by rw [det_smul]
    _ = b ^ Fintype.card n * (1 + a / b * Fintype.card n) := by rw [det_expr]
    _ ≠ 0 := mul_ne_zero (pow_ne_zero _ hb) hab
  apply rank_of_isUnit
  rwa [isUnit_iff_isUnit_det, isUnit_iff_ne_zero]

theorem r_gt_l_of_nontrivialrpbd (Φ : nontrivialRPBD X v b l r) : r > l := by
  rcases Φ.nontrivial with ⟨i, hi₀, hi₁⟩
  rcases card_pos.mp hi₀ with ⟨x, hx⟩
  have := calc
    #((Φ.blocks i)ᶜ) = v - #(Φ.blocks i) := by rw [card_compl, Φ.hX]
    _ > 0 := Nat.zero_lt_sub_of_lt hi₁
  rcases card_pos.mp this with ⟨y, hy⟩
  have hxy : x ≠ y := by rintro ⟨_, _⟩; exact (mem_compl.mp hy) hx
  simp only [←Φ.regularity x, ←Φ.balance _ _ hxy]
  apply card_lt_card
  constructor
  · intro j
    simp only [mem_filter, mem_univ, true_and, and_imp]
    tauto
  · rw [not_subset]
    use i
    simp only [mem_filter, mem_univ, true_and]
    exact ⟨hx, fun hyp ↦ (mem_compl.mp hy) hyp.2⟩

theorem b_ge_v_of_nontrivialrpbd {α : Type*} [LinearOrderedField α]
    (Φ : nontrivialRPBD X v b l r) :
    b ≥ v := by
  let M := toIncMat α Φ.toDesign
  have l_le_r := Nat.le_of_succ_le (r_gt_l_of_nontrivialrpbd Φ)
  have key : M * Mᵀ = l • (allOnes _ _ _) + (r - l) • 1 := by
    rw [(rpbdCondition_of_rpbd (α := α) Φ.toRPBD).2, ←Nat.cast_sub,
      Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul]
    exact l_le_r
  have aux := rank_ones_add_diagonal (α := α) (n := X) l (r - l)
    (sub_ne_zero.mpr (ne_of_gt (Nat.cast_lt.mpr (r_gt_l_of_nontrivialrpbd Φ))))
    (mul_nonneg
      (div_nonneg (Nat.cast_nonneg l) (l_le_r |> Nat.cast_le.mpr |> sub_nonneg.mpr))
      (Nat.cast_nonneg' (Fintype.card X))
      |> (add_pos_of_pos_of_nonneg zero_lt_one) |> ne_of_gt)
  calc
    b ≥ rank M := by
      have := rank_le_card_width M
      rwa [Fintype.card_fin b] at this
    _ ≥ rank (M * Mᵀ) := rank_mul_le_left _ _
    _ = v := by
      rw [key, ←Φ.hX, ←aux]; congr
      · rw [Nat.cast_smul_eq_nsmul]
      · rw [←Nat.cast_sub l_le_r, Nat.cast_smul_eq_nsmul]

end BalancedIncompleteBlockDesign
