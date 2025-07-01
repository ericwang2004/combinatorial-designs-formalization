import CombinatorialDesign.FisherInequality
import Mathlib.Data.Matrix.Rank

open CombinatorialDesign Matrix Finset
namespace CombinatorialDesign

variable {X} [Fintype X] [DecidableEq X] [Inhabited X] {v k l : ℕ} (Φ : BIBD X v v k l)

theorem eq_of_full_rank_mul_eq {n m o α : Type*} [Fintype n] [Fintype m] [DecidableEq m] [Fintype o]
    [CommRing α] {A : Matrix n m α} {B₁ B₂ : Matrix m o α} (f : n ≃ m)
    (rankA : rank A = Fintype.card m) (h : A * B₁ = A * B₂) : B₁ = B₂ := by
  let A' := reindex f (Equiv.refl _) A
  have h' : A' * B₁ = A' * B₂ := by
    ext i' j
    rw [←Matrix.ext_iff] at h
    specialize h (f.symm i') j
    rwa [mul_apply] at h
  have rankA' : rank A' = Fintype.card m := by rw [←rankA]; apply rank_reindex
  -- need theorem that says if a matrix has full rank then it is invertible
  sorry

theorem card_inter_block_eq_l {α : Type*} [Field α] [LinearOrder α] [IsStrictOrderedRing α]
    {i j : Fin v} (inej : i ≠ j) : #(Φ.blocks i ∩ Φ.blocks j) = l := by
  let M := toIncMat α Φ.toDesign
  have rankM : rank M = v :=
    rank_eq_v_of_symmNontrivialRPBD α (BIBD_to_nontrivialRPBD Φ (v_pos_of_bibd Φ))
  have MtM i j : (Mᵀ * M) i j = #(Φ.blocks i ∩ Φ.blocks j) := by
    simp only [mul_apply, transpose_apply, M, toIncMat, of_apply, mul_ite, mul_one, mul_zero,
      sum_ite_mem, univ_inter, sum_const, nsmul_eq_mul, Nat.cast_inj, inter_comm]
  have MMt : M * Mᵀ = (l : α) • allOnes X X α + ((rep Φ : α) - l) • 1 :=
    (rpbdCondition_of_rpbd (α := α) (BIBD_to_RPBD Φ)).2
  have MMtM : M * (Mᵀ * M) = M * (of (if · = · then k else l) : Matrix (Fin v) (Fin v) α) := by
    rw [←Matrix.mul_assoc, MMt, Matrix.add_mul, Matrix.smul_mul, Matrix.smul_mul, Matrix.one_mul]
    ext
    simp only [allOnes, mul_apply, add_apply, smul_apply, of_apply, one_mul, smul_eq_mul, mul_ite]
    rw [col_sum_incmat, sum_ite, sum_eq_single _ (by
      simp only [mem_filter, mem_univ]; tauto) (by simp only [mem_filter, mem_univ]; tauto),
      filter_ne', sum_erase_eq_sub (mem_univ _), ←sum_mul, row_sum_incmat,
      (b_eq_v_iff_rep_eq_k Φ (v_pos_of_bibd Φ)).mp rfl]
    group
  have := ext_iff.mpr (eq_of_full_rank_mul_eq (Fintype.equivFinOfCardEq Φ.hX) (by
    rw [Fintype.card_fin, rankM]) MMtM) i j
  simp_all only [MtM, of_apply, inej, ite_false, Nat.cast_inj]

def bibdOfSymmNontrivialRPBD {α : Type*} [Field α] [LinearOrder α] [IsStrictOrderedRing α]
    {r : ℕ} (Ψ : nontrivialRPBD X v v l r) : BIBD X v v (1 + l * (v - 1) / r) l where
  toBBD := Ψ.toBBD
  hvk := sorry
  hA i := by
    let M := toIncMat α Ψ.toDesign
    have rankM : rank M = v := rank_eq_v_of_symmNontrivialRPBD α Ψ
    have Mt1 i : (Mᵀ * allOnes X (Fin 1) α) i 0 = #(Ψ.blocks i) := by
      simp only [M, toIncMat, allOnes, mul_apply, of_apply, transpose_apply, mul_one, sum_ite_mem,
        univ_inter, sum_const, nsmul_one]
    have MMt : M * Mᵀ = (l : α) • allOnes X X α + ((r : α) - (l : α)) • 1 :=
      (rpbdCondition_of_rpbd (α := α) Ψ.toRPBD).2
    have : (r : α) ≠ 0 := Nat.cast_ne_zero.mpr <| Nat.ne_zero_of_lt <| r_pos_of_nontrivialRPBD Ψ
    have MMt1 : M * (Mᵀ * allOnes _ (Fin 1) _) =
        M * ((1 : α) + ((l : α) * ((v : α) - 1) / (r : α))) • allOnes _ _ _ := by
      rw [←Matrix.mul_assoc, MMt, Matrix.mul_smul, rpbd_incmat_allOnes]
      ext i j
      simp only [allOnes, smul_apply, of_apply, add_apply, mul_apply, one_apply, mul_one,
        smul_eq_mul, mul_ite, mul_zero]
      rw [sum_add_distrib, sum_const, card_univ, Ψ.hX, sum_eq_single i (by
        intros; simp only [ite_eq_right_iff]; tauto) (by simp only [mem_univ]; tauto),
        nsmul_eq_mul]
      simp only [reduceIte]
      ring_nf; field_simp
    have := ext_iff.mpr (eq_of_full_rank_mul_eq (Fintype.equivFinOfCardEq Φ.hX) (by
      rw [Fintype.card_fin, rankM]) MMt1) i 0
    simp only [Mt1] at this
    rw [←Nat.cast_inj (R := α), this]
    simp only [allOnes, Fin.isValue, smul_apply, of_apply, smul_eq_mul, mul_one,
      Nat.cast_add, Nat.cast_one, add_right_inj]
    sorry

end CombinatorialDesign
