import CombinatorialDesign.IncidenceMatrix
import CombinatorialDesign.MatrixLemmas

open CombinatorialDesign Matrix Finset
variable {ι X : Type*} [Fintype X] [Fintype ι] [DecidableEq X] [DecidableEq ι] {l r : ℕ}

namespace CombinatorialDesign

omit [DecidableEq ι]
theorem l_lt_r_of_nontrivialRPBD (Φ : nontrivialRPBD ι X l r) : l < r := by
  rcases Φ.nontrivial with ⟨i, hi₀, hi₁⟩
  rcases card_pos.mp hi₀ with ⟨x, hx⟩
  have := calc
    #((Φ.blocks i)ᶜ) = (Fintype.card X) - #(Φ.blocks i) := by rw [card_compl]
    _ > 0 := Nat.zero_lt_sub_of_lt hi₁
  rcases card_pos.mp this with ⟨y, hy⟩
  have hxy : x ≠ y := by rintro ⟨_, _⟩; exact (mem_compl.mp hy) hx
  simp only [←Φ.regularity x, ←balance_RPBD (Φ.toRPBD) _ _ hxy]
  apply card_lt_card
  constructor
  · intro j
    simp only [mem_filter, mem_univ, true_and, and_imp]
    tauto
  · rw [not_subset]
    use i
    simp only [mem_filter, mem_univ, true_and]
    exact ⟨hx, fun hyp ↦ (mem_compl.mp hy) hyp.2⟩

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
