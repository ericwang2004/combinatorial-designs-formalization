import CombinatorialDesign.FisherInequality
import Mathlib.Data.Matrix.Rank
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Real.Irrational

open CombinatorialDesign Matrix Finset
namespace CombinatorialDesign

variable {X} [Fintype X] [DecidableEq X] {v k l : ℕ} (Φ : BIBD X v v k l)

theorem eq_of_full_rank_mul_eq {n m o α} [Fintype n] [Fintype m] [DecidableEq m] [Fintype o]
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

theorem card_inter_block_eq_l
    [Inhabited X] {i j : Fin v} (inej : i ≠ j) : #(Φ.blocks i ∩ Φ.blocks j) = l := by
  let M := toIncMat ℚ Φ.toDesign
  have rankM : rank M = v :=
    rank_eq_v_of_symmNontrivialRPBD ℚ (BIBD_to_nontrivialRPBD Φ (v_pos_of_bibd Φ))
  have MtM i j : (Mᵀ * M) i j = #(Φ.blocks i ∩ Φ.blocks j) := by
    simp only [mul_apply, transpose_apply, M, toIncMat, of_apply, mul_ite, mul_one, mul_zero,
      sum_ite_mem, univ_inter, sum_const, nsmul_eq_mul, Nat.cast_inj, inter_comm]
  have MMt : M * Mᵀ = (l : ℚ) • allOnes X X _ + ((rep Φ : ℚ) - l) • 1 :=
    (rpbdCondition_of_rpbd (α := ℚ) (BIBD_to_RPBD Φ)).2
  have MMtM : M * (Mᵀ * M) = M * (of (if · = · then k else l) : Matrix (Fin v) (Fin v) ℚ) := by
    rw [←Matrix.mul_assoc, MMt, Matrix.add_mul, Matrix.smul_mul, Matrix.smul_mul, Matrix.one_mul]
    ext
    simp only [allOnes, mul_apply, add_apply, smul_apply, of_apply, one_mul, smul_eq_mul, mul_ite]
    rw [col_sum_incmat, sum_ite, sum_eq_single _ (by
      simp only [mem_filter, mem_univ]; tauto) (by simp only [mem_filter, mem_univ]; tauto),
      filter_ne', sum_erase_eq_sub (mem_univ _), ←sum_mul, row_sum_incmat,
      (b_eq_v_iff_rep_eq_k Φ).mp rfl]
    group
  have := ext_iff.mpr (eq_of_full_rank_mul_eq (Fintype.equivFinOfCardEq Φ.hX) (by
    rw [Fintype.card_fin, rankM]) MMtM) i j
  simp_all only [MtM, of_apply, inej, ite_false, Nat.cast_inj]

theorem bibd_of_symmNontrivialRPBD  {r : ℕ} (Ψ : nontrivialRPBD X v v l r) :
    ∀ i, #(Ψ.blocks i) * r = r + l * (v - 1) := by
  intro i
  let M := toIncMat ℚ Ψ.toDesign
  have rankM : rank M = v := rank_eq_v_of_symmNontrivialRPBD ℚ Ψ
  have Mt1 j : (Mᵀ * allOnes X (Fin 1) ℚ) j 0 = #(Ψ.blocks j) := by
    simp only [M, toIncMat, allOnes, mul_apply, of_apply, transpose_apply, mul_one, sum_ite_mem,
      univ_inter, sum_const, nsmul_one]
  have MMt : M * Mᵀ = (l : ℚ) • allOnes X X ℚ + ((r : ℚ) - (l : ℚ)) • 1 :=
    (rpbdCondition_of_rpbd (α := ℚ) Ψ.toRPBD).2
  have hr : (r : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr <| Nat.ne_zero_of_lt <| r_pos_of_nontrivialRPBD Ψ
  have MMt1 : M * (Mᵀ * allOnes _ (Fin 1) _) =
      M * ((1 : ℚ) + ((l : ℚ) * ((v : ℚ) - 1) / (r : ℚ))) • allOnes _ _ _ := by
    rw [←Matrix.mul_assoc, MMt, Matrix.mul_smul, rpbd_incmat_allOnes]
    ext
    simp only [allOnes, smul_apply, of_apply, add_apply, mul_apply, one_apply, mul_one,
      smul_eq_mul, mul_ite, mul_zero]
    rw [sum_add_distrib, sum_const, card_univ, Ψ.hX, sum_eq_single _ (by
      intro; simp only [ite_eq_right_iff]; tauto) (by simp only [mem_univ]; tauto),
      nsmul_eq_mul]
    simp only [reduceIte]
    ring_nf; field_simp
  have := ext_iff.mpr (eq_of_full_rank_mul_eq (Fintype.equivFinOfCardEq Ψ.hX) (by
    rw [Fintype.card_fin, rankM]) MMt1) i 0
  simp only [Mt1] at this
  simp only [allOnes, Fin.isValue, smul_apply, of_apply, smul_eq_mul, mul_one] at this
  rw [←mul_left_inj' hr] at this
  field_simp at this
  rwa [←Nat.cast_one, ←Nat.cast_sub (v_pos_of_nontrivialRPBD Ψ), ←Nat.cast_mul,
    ←Nat.cast_mul, ←Nat.cast_add, Nat.cast_inj] at this

theorem r_div_of_symmNontrivialRPBD {r : ℕ} (Ψ : nontrivialRPBD X v v l r) :
    r ∣ l * (v - 1) := by
  suffices h : r ∣ r + l * (v - 1) from Nat.dvd_add_self_left.mp h
  let i : Fin v := ⟨0, v_pos_of_nontrivialRPBD Ψ⟩
  use #(Ψ.blocks i)
  rw [←bibd_of_symmNontrivialRPBD Ψ, mul_comm]

private theorem vlr {v l r : ℕ} (h : r ∣ l * (v - 1)) :
    (1 + l * (v - 1) / r) * r = r + l * (v - 1) := by
  rw [add_mul, one_mul, Nat.div_mul_cancel h]

def symmNontrivialRPBD_to_symmBIBD {r : ℕ} (hl : l > 0) (Ψ : nontrivialRPBD X v v l r) :
    BIBD X v v (1 + l * (v - 1) / r) l where
  toBBD := Ψ.toBBD
  hvk := by
    have rpos := r_pos_of_nontrivialRPBD Ψ
    have rdiv := r_div_of_symmNontrivialRPBD Ψ
    have hv : v - 1 > 0 := v_ge_two_of_nontrivialRPBD Ψ |> Nat.zero_lt_sub_of_lt
    constructor
    · rw [←Nat.mul_lt_mul_right rpos, vlr rdiv]
      calc
        _ < _ := by
          rw [add_lt_add_iff_left, Nat.mul_lt_mul_right hv]; exact l_lt_r_of_nontrivialRPBD Ψ
        _ = _ := by
          nth_rewrite 1 [←mul_one r]
          rw [←mul_add, v_ge_one_of_nontrivialRPBD Ψ |> Nat.add_sub_of_le , mul_comm]
    · rw [←Nat.mul_le_mul_right_iff rpos, vlr rdiv, two_mul, add_le_add_iff_left]
      exact Nat.le_of_dvd (Nat.mul_pos hl hv) rdiv
  hA _ := by
    rw [←r_pos_of_nontrivialRPBD Ψ |> Nat.ne_zero_iff_zero_lt.mpr |> Nat.mul_left_inj,
      r_div_of_symmNontrivialRPBD Ψ |> vlr, bibd_of_symmNontrivialRPBD]

theorem int_det_of_int_matrix {n} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) (hA : ∃ (A₀ : Matrix n n ℤ), A = A₀.map (↑)) :
    ∃ z : ℤ, z = det A := by
  obtain ⟨A₀, rfl⟩ := hA
  exact ⟨det A₀, Int.cast_det _⟩

theorem perfect_square_of_even_symmBIBD [Inhabited X] (hv : Even v) (Φ : BIBD X v v k l) :
    IsSquare (k - l) := by
  cases eq_or_ne (k - l) 0 with
  | inl h => rw [h]; exact IsSquare.zero
  | inr h =>
  let M := toIncMat ℝ Φ.toDesign
  let Mr := reindex (Equiv.refl _) (Fintype.equivFinOfCardEq Φ.hX |> Equiv.symm) M
  have repk := (b_eq_v_iff_rep_eq_k Φ).mp rfl
  have repl := BIBD_to_nontrivialRPBD Φ (v_pos_of_bibd Φ) |> l_lt_r_of_nontrivialRPBD
  have repl' := Nat.le_of_succ_le repl
  have vge1 : v ≥ 1 := v_pos_of_bibd Φ
  have kge1 : k ≥ 1 := k_pos_of_bibd Φ
  have kl := le_of_le_of_eq repl' repk
  have kl_cast_ne {α} [AddGroupWithOne α] [CharZero α] : (k : α) - l ≠ 0 :=
    fun hyp ↦ by norm_cast at hyp
  have lv1_cast : (l : ℝ) * (v - 1) = k * (k - 1) := by
    have := eq_of_symmBIBD Φ; norm_cast
  have kl_cast_ge {α} [Ring α] [CharZero α] [LinearOrder α] [IsStrictOrderedRing α]
      : 0 ≤ (k : α) - l := by
    norm_cast; exact (Nat.le_sub_iff_add_le' kl).mpr kl
  have MMt : M * Mᵀ = (l : ℝ) • allOnes X X _ + ((rep Φ : ℝ) - l) • 1 :=
    (rpbdCondition_of_rpbd (α := ℝ) (BIBD_to_RPBD Φ)).2
  have detMMt : det (M * Mᵀ) = k^2 * (k - l)^(v - 1) := by
    rw [MMt, det_ones_add_diagonal, Φ.hX, repk]
    · calc
        ((k : ℝ) - l) ^ v * (1 + l / (k - l) * v) = (k - l) ^ v * (((k - l) + l * v) / (k - l)) := by
          congr; rw [div_mul_eq_mul_div, ←div_self kl_cast_ne, div_add_div_same]
        _ = (k - l) ^ v * ((k + l * (v - 1)) / (k - l)) := by congr 2; group
        _ = (k - l) ^ v * (k ^ 2 / (k - l)) := by
          congr; rw [lv1_cast]; group
        _ = k ^ 2 * ((k - l) ^ v / (k - l) ^ 1) := by group
        _ = k ^ 2 * (k - l) ^ (v - 1) := by
          congr; rw [Field.div_eq_mul_inv, ←pow_sub₀ _ kl_cast_ne vge1]
    · rw [repk]; exact kl_cast_ne
  have det_eq : det (M * Mᵀ) = det (Mr * Mrᵀ) := by aesop
  rw [detMMt, det_mul, det_transpose, ←pow_two] at det_eq
  have det_int : ∃ a : ℤ, a = Mr.det := by
    apply int_det_of_int_matrix
    use reindex (Equiv.refl _) (Fintype.equivFinOfCardEq Φ.hX |> Equiv.symm) (toIncMat ℤ Φ.toDesign)
    ext
    simp only [Mr, M, toIncMat, reindex_apply, Equiv.refl_symm, Equiv.coe_refl, Equiv.symm_symm,
      submatrix_apply, id_eq, of_apply, map_apply, Int.cast_ite, Int.cast_one, Int.cast_zero]
  obtain ⟨a, ha⟩ := det_int
  rw [←ha] at det_eq
  have := congrArg Real.sqrt det_eq
  simp only [Nat.cast_nonneg, pow_nonneg, Real.sqrt_mul, Real.sqrt_sq, Real.sqrt_sq_eq_abs] at this
  have := EuclideanDomain.eq_div_of_mul_eq_right (k_pos_of_bibd Φ |> ne_of_gt |> (Nat.cast_ne_zero (R := ℝ)).mpr ) this
  have notirr : ¬Irrational √((↑k - ↑l) ^ (v - 1)) := by
    simp only [Irrational, Set.mem_range, not_exists, not_forall, Decidable.not_not]
    use |a| / k
    simp only [Int.cast_abs, Rat.cast_div, Rat.cast_abs, Rat.cast_intCast, Rat.cast_natCast]
    exact this.symm
  have square : IsSquare ((↑k - ↑l) ^ (v + 1) : ℚ) := by
    suffices IsSquare ((↑k - ↑l) ^ (v - 1) : ℚ) by
      have := IsSquare.mul this (IsSquare.sq (↑k - ↑l : ℚ))
      rwa [←pow_add, ← Nat.sub_add_comm vge1, Nat.add_succ_sub_one] at this
    by_contra ct
    rw [←irrational_sqrt_ratCast_iff_of_nonneg (by apply pow_nonneg kl_cast_ge)] at ct
    simp only [Rat.cast_pow, Rat.cast_sub, Rat.cast_natCast] at ct
    exact notirr ct
  obtain ⟨v', rfl⟩ := hv
  have := Even.isSquare_pow (Even.add_self v') ((k : ℚ) - l) |> IsSquare.div square
  rw [Field.div_eq_mul_inv, ←pow_sub₀ _ kl_cast_ne (Nat.le_add_right _ _),
    add_tsub_cancel_left, pow_one, ←Nat.cast_sub kl] at this
  exact Rat.isSquare_natCast_iff.mp this

end CombinatorialDesign
