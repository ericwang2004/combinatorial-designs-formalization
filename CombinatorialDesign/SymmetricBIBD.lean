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

theorem inter_block_eq_l {α : Type*} [Field α] [LinearOrder α] [IsStrictOrderedRing α]
    {i j : Fin v} (inej : i ≠ j) : #(Φ.blocks i ∩ Φ.blocks j) = l := by
  let M := toIncMat α Φ.toDesign
  have hv : 0 < v := lt_of_le_of_lt Φ.hvk.2 Φ.hvk.1 |> lt_trans zero_lt_two
  have rankM : rank M = v := rank_eq_v_of_symmNontrivialRPBD α (BIBD_to_nontrivialRPBD Φ hv)
  have MtM i j : (Mᵀ * M) i j = #(Φ.blocks i ∩ Φ.blocks j) := by
    simp only [mul_apply, transpose_apply, M, toIncMat, of_apply, mul_ite, mul_one, mul_zero,
      sum_ite_mem, univ_inter, sum_const, nsmul_eq_mul, Nat.cast_inj, inter_comm]
  have ⟨_, hM⟩ := rpbdCondition_of_rpbd (α := α) (BIBD_to_RPBD Φ)
  have MMt : M * Mᵀ = (l : α) • allOnes X X α + ((rep Φ : α) - l) • 1 :=
    (rpbdCondition_of_rpbd (α := α) (BIBD_to_RPBD Φ)).2
  let S : Matrix (Fin v) (Fin v) α := of (fun i j ↦ if i = j then k else l)
  have MMtM : M * (Mᵀ * M) = M * S := by
    sorry
  have hS := ext_iff.mpr (eq_of_full_rank_mul_eq (Fintype.equivFinOfCardEq Φ.hX) (by
    rw [Fintype.card_fin, rankM]) MMtM) i j
  simp_all only [MtM, S, of_apply, inej, ite_false, Nat.cast_inj]

end CombinatorialDesign
