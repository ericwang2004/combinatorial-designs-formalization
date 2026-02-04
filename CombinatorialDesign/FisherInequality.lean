import CombinatorialDesign.IncidenceMatrix
import CombinatorialDesign.MatrixLemmas

open CombinatorialDesign Matrix Finset
variable {ι X : Type*} [Fintype X] [Fintype ι] [DecidableEq X] [DecidableEq ι] {l r : ℕ}

namespace CombinatorialDesign

omit [DecidableEq ι]
theorem l_lt_r_of_nontrivialRPBD (Φ : nontrivialRPBD ι X l r) : l < r := by
  obtain ⟨i, hi₀, hi₁⟩ := Φ.nontrivial
  obtain ⟨x, hx⟩ := card_pos.mp hi₀
  obtain ⟨y, hy⟩ := card_pos.mp (card_compl (Φ.blocks i) ▸ Nat.zero_lt_sub_of_lt hi₁)
  have hxy : x ≠ y := fun h ↦ (mem_compl.mp hy) (h ▸ hx)
  calc l = #{j | {x, y} ⊆ Φ.blocks j} := (Φ.toRPBD.balance {x, y} (card_pair hxy)).symm
    _ < #{j | x ∈ Φ.blocks j} := card_lt_card ⟨fun j hj ↦ by
        simp only [mem_filter, mem_univ, true_and, insert_subset_iff] at hj ⊢; exact hj.1,
        not_subset.mpr ⟨i, by simp only [mem_filter, mem_univ, true_and]; exact hx, by
        simp only [mem_filter, mem_univ, true_and, insert_subset_iff, singleton_subset_iff, not_and]
        exact fun _ hy' ↦ (mem_compl.mp hy) hy'⟩⟩
    _ = r := Φ.regularity x

/-- ### Fisher's Inequality -/
private theorem b_ge_rank_ge_v_of_nontrivialRPBD (α : Type*) [Field α]
    [LinearOrder α] [IsStrictOrderedRing α]
    (Φ : nontrivialRPBD ι X l r) : let M := toIncMat α Φ.toDesign
    (Fintype.card ι) ≥ rank M ∧ rank M ≥ (Fintype.card X) := by
  let M := toIncMat α Φ.toDesign
  have l_lt_r := l_lt_r_of_nontrivialRPBD Φ
  have l_le_r := Nat.le_of_succ_le l_lt_r
  have key : M * Mᵀ = l • (allOnes _ _ _) + (r - l) • 1 := by
    rw [(rpbdCondition_of_rpbd (α := α) Φ.toRPBD).2, ←Nat.cast_sub,
      Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul]
    exact l_le_r
  have aux := rank_ones_add_diagonal (l : α) (r - l)
    (Nat.cast_lt.mpr l_lt_r |> ne_of_gt |> sub_ne_zero.mpr)
    (mul_nonneg
      (l_le_r |> Nat.cast_le.mpr |> sub_nonneg.mpr |> div_nonneg (l |> Nat.cast_nonneg))
      (Fintype.card X |> Nat.cast_nonneg') |> (add_pos_of_pos_of_nonneg zero_lt_one) |> ne_of_gt)
  constructor
  · have := rank_le_card_width M
    rwa [Fintype.card] at this
  · refine ge_trans (rank_mul_le_left M Mᵀ) (ge_of_eq ?_)
    rw [key, ←aux]; congr
    · rw [Nat.cast_smul_eq_nsmul]
    · rw [←Nat.cast_sub l_le_r, Nat.cast_smul_eq_nsmul]

theorem rank_eq_v_of_symmNontrivialRPBD (α : Type*) [Field α]
    [LinearOrder α] [IsStrictOrderedRing α]
    (Φ : nontrivialRPBD X X l r) : rank (toIncMat α Φ.toDesign) = (Fintype.card X) := by
  have ⟨h₁, h₂⟩ := b_ge_rank_ge_v_of_nontrivialRPBD α Φ
  exact le_antisymm h₁ h₂

end CombinatorialDesign
