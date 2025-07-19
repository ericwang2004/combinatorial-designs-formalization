import CombinatorialDesign.FisherInequality
import CombinatorialDesign.MatrixCongruence
import CombinatorialDesign.SymmetricBIBD
import Mathlib.Data.Real.Basic

open CombinatorialDesign Matrix Finset MatCongr
namespace CombinatorialDesign

variable {ι X} [Fintype X] [Fintype ι] [DecidableEq X] [DecidableEq ι] {v k l : ℕ} (Φ : BIBD X X k l)

theorem l_le_k_of_symmBIBD [Inhabited X] (Φ : BIBD X X k l) : l ≤ k := by
  let i : X := default
  cases Classical.em (∃ j, i ≠ j) with
  | inl exists_j =>
    obtain ⟨j, hij⟩ := exists_j
    simp_rw [←Φ.hA i, ←card_inter_block_eq_l Φ hij]
    exact card_le_card inter_subset_left
  | inr forall_j =>
    push_neg at forall_j
    have cardX : Fintype.card X = 1 :=
      Fintype.card_eq_one_iff.mpr ⟨i, fun _ ↦ forall_j _ |>.symm⟩
    have k0 : k = 0 := by rw [←Nat.lt_one_iff, ←cardX]; exact Φ.hvk.1
    subst k0
    exact Nat.not_succ_le_zero _ Φ.hvk.2 |> False.elim

noncomputable def brcKey [Inhabited X] (Φ : BIBD X X k l)
    (hrep : rep Φ = k) (hl : l ≠ 0) (hkl : k ≠ l) :
    ((k : ℚ) - l) • (1 : Matrix X X ℚ) ⊕ₘ (-((k : ℚ) - l) / (l : ℚ)) •
    (1 : Matrix (Fin 1) (Fin 1) ℚ) ∼ₘ
    (1 : Matrix X X ℚ) ⊕ₘ (-(l : ℚ) • (1 : Matrix (Fin 1) (Fin 1) ℚ)) :=
  let A := toIncMat ℚ Φ.toDesign
  have AAt : A * Aᵀ = (l : ℚ) • allOnes X X _ + ((rep Φ : ℚ) - l) • 1 :=
    (rpbdCondition_of_rpbd (α := ℚ) (BIBD_to_RPBD Φ)).2
  let A' := fromBlocks A (allOnes X (Fin 1) ℚ) (allOnes (Fin 1) X ℚ) (of (fun _ ↦ k/l))
  let E := ((k : ℚ) - l) • (1 : Matrix X X ℚ) ⊕ₘ (-((k : ℚ) - l) / (l : ℚ)) •
    (1 : Matrix (Fin 1) (Fin 1) ℚ)
  let D := (1 : Matrix X X ℚ) ⊕ₘ (-(l : ℚ) • (1 : Matrix (Fin 1) (Fin 1) ℚ))
  have hA' : E = A' * D * A'ᵀ := by
    simp only [A', D, E, matDirectSum, fromBlocks_multiply, fromBlocks_transpose,
      mul_one, Matrix.mul_zero, add_zero, neg_smul, Matrix.mul_neg, Matrix.mul_smul,
      Matrix.mul_one, zero_add, Matrix.neg_mul, smul_mul, mul_neg, Algebra.mul_smul_comm, smul_of,
      neg_of, neg_sub, fromBlocks_inj, AAt, allOnes]
    constructor
    · ext; simp [mul_apply, hrep]
    constructor
    · ext; simp [mul_apply, A, row_sum_incmat, hrep, mul_div_cancel₀, hl]
    constructor
    · ext; simp [mul_apply, A, row_sum_incmat, hrep, mul_div_cancel₀, hl]
    ext i j
    have : (1 : Matrix (Fin 1) (Fin 1) ℚ) i j = 1 := by
      rw [one_apply, if_pos]; ext; simp only [Fin.val_eq_zero]
    simp [mul_apply, mul_div_cancel₀, hl, this]
    field_simp
    rw [←Rat.sub_eq_add_neg, eq_sub_iff_add_eq, sub_add, ←neg_inj,
      neg_sub, sub_eq_iff_eq_add', ←neg_inj, neg_sub, neg_add, neg_neg,
      neg_add_eq_sub, ←mul_sub_one]
    nth_rewrite 2 [←one_mul l]
    rw [Nat.cast_mul, ←mul_sub_right_distrib, mul_comm _ (l : ℚ), ←Nat.cast_one]
    have : 1 ≤ k := k_pos_of_bibd Φ
    have : 1 ≤ Fintype.card X := NeZero.one_le
    norm_cast
    exact eq_of_symmBIBD Φ |>.symm
  {
    A := A'
    inv := by
      have detD : det D ≠ 0 := by
        simp [D, det_oplus, hl]
      have detE : det E ≠ 0 := by
        simp [E, det_oplus, hl, sub_eq_zero, hkl, hkl.symm]
      have detA' : det A' ≠ 0 := by
        intro h
        exact detE (by calc
          det E = det (A' * D * A'ᵀ) := by rw [hA']
          _ = det A' * det D * det A'ᵀ := by rw [det_mul, det_mul]
          _ = 0 := by rw [h, zero_mul, zero_mul]
        )
      exact Ne.isUnit detA' |> invertibleOfIsUnitDet _
    cong := hA'
  }

theorem bruck_ryser_chowla_odd [Inhabited X] {u : ℕ}
    (hv : Fintype.card X = 2 * u + 1) (Φ : BIBD X X k l) :
    ∃ x y z : ℤ, (x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0) ∧ x^2 = (k - l) * y^2 + (-1)^u * l * z^2 := by
  cases eq_or_ne l 0 with
  | inl hl => use 0, 0, 1; simp [hl]
  | inr hl =>
  cases eq_or_ne k l with
  | inl hkl => use 0, 1, 0; simp [hkl]
  | inr hkl =>
  set v := Fintype.card X with v_def
  let A := toIncMat ℚ Φ.toDesign
  have hrep : rep Φ = k := by
    have := mul_eq_mul_right_iff.mp <| kb_eq_repv Φ
    simp only [Fintype.card_ne_zero, or_false] at this
    exact this.symm
  have l_le_k := l_le_k_of_symmBIBD Φ
  have AAt : A * Aᵀ = (l : ℚ) • allOnes X X _ + ((rep Φ : ℚ) - l) • 1 :=
    (rpbdCondition_of_rpbd (α := ℚ) (BIBD_to_RPBD Φ)).2
  have hkl' : 0 < Int.ofNat (k - l) := by
    rw [Int.ofNat_eq_coe, Nat.cast_pos']
    exact Nat.lt_of_le_of_ne l_le_k hkl.symm |> Nat.zero_lt_sub_of_lt
  cases Nat.even_or_odd u with
  | inl hu =>
    set v' := v - 1 with v'_def
    have hv' : 4 ∣ v' := by
      have aux : v' = 2 * u := by
        simp_all only [add_tsub_cancel_right]
      obtain ⟨u', hu'⟩ := hu
      use u'
      rw [aux, hu', ←two_mul, ←mul_assoc]; rfl
    have e : X ≃ Fin v' ⊕ Fin 1 := by
      refine Equiv.trans (Fintype.equivFinOfCardEq ?_) finSumFinEquiv.symm
      rw [v'_def, ←v_def]
      simp_all only [add_tsub_cancel_right]
    have aux₁ : 1 ⊕ₘ 1 = reindexAlgEquiv ℚ ℚ e 1 := by
      simp only [matDirectSum]; aesop
    have aux₂ : ((k : ℚ) - l) • 1 ⊕ₘ ((k : ℚ) - l) • 1 =
        reindexAlgEquiv ℚ ℚ e (((k : ℚ) - l) • 1) := by
      rw [map_rat_smul, ←smul_oplus, aux₁]
    have key : (1 : Matrix (Fin v') (Fin v') ℚ) ⊕ₘ (1 : Matrix (Fin 1) (Fin 1) ℚ) ⊕ₘ
        (-(l : ℚ) • (1 : Matrix (Fin 1) (Fin 1) ℚ)) ∼ₘ
        ((k : ℚ) - l) • 1 ⊕ₘ ((k : ℚ) - l) • 1 ⊕ₘ (-((k : ℚ) - (l : ℚ)) / (l : ℚ)) • 1 := by
      rw [aux₁, aux₂]
      exact brcKey Φ hrep hl hkl |>.symm |> matCongrOplusReindexOfMatCongr _
    have aux₃ : ((k : ℚ) - l) • (1 : Matrix (Fin v') (Fin v') ℚ) ∼ₘ 1 := by
      rw [←Nat.cast_sub l_le_k]
      exact matCongrOneOfFourDiv
        (by rw [Fintype.card_fin]; exact hv') hkl'
    have := MatCongr.trans (matCongrAssocOfMatCongr key)
      (matCongrOplusRightOfMatCongr _ aux₃) |>
      oplusLeftCancel transpose_one.symm (by
        simp [transpose_oplus]) (by simp [transpose_oplus])
    -- have toReal := MatCongr.trans (matCongrAssocOfMatCongr key)
    --   (matCongrOplusRightOfMatCongr _ aux₃) |>
    --   matCongrOfRatCast ℝ
    -- simp only [ratCast_oplus, RingHom.map_one, ratCast_smul] at toReal
    -- have toRealCancel := toReal |> oplusLeftCancel transpose_one.symm (by
    --     simp [transpose_oplus]) (by simp [transpose_oplus])
    nth_rewrite 1 [←one_smul ℚ (1 : Matrix (Fin 1) (Fin 1) ℚ)] at this
    obtain ⟨x, z, hxz⟩ := (matCongr_two_by_two_condition this) 1 0
    simp only [one_mul, neg_mul, one_pow, mul_one, neg_sub, ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true, zero_pow, mul_zero, add_zero] at hxz
    set d : ℚ := (x.den * z.den) ^ 2 with d_def
    have hxz' := congrArg (HMul.hMul d) (add_eq_of_eq_add_neg hxz.symm).symm
    have hd₁ : d * x ^ 2 = (x.num * z.den) ^ 2 := by
      rw [d_def, mul_pow, mul_pow]; nth_rewrite 2 [←Rat.num_div_den x]
      field_simp; group
    have hd₂ : z ^ 2 * d = (x.den * z.num) ^ 2 := by
      rw [d_def, mul_pow, mul_pow]; nth_rewrite 1 [←Rat.num_div_den z]
      field_simp; group
    rw [hd₁, mul_add, mul_comm d, mul_comm d, mul_assoc, hd₂, d_def] at hxz'
    norm_cast at hxz'
    use x.num * z.den, x.den * z.den, x.den * z.num
    constructor
    · simp
    · rw [Even.neg_one_pow hu, one_mul, hxz']
      norm_cast
  | inr hu =>
    have cardX : 4 ∣ Fintype.card (X ⊕ Fin 1) := by
      obtain ⟨u', hu'⟩ := hu
      use u' + 1
      rw [Fintype.card_sum, Fintype.card_fin, ←v_def, hv, hu']
      omega
    have aux : (((k : ℚ) - l) • (1 : Matrix X X ℚ) ⊕ₘ
        (((k : ℚ) - l) • (1 : Matrix (Fin 1) (Fin 1) ℚ) ⊕ₘ
        (-((k : ℚ) - (l : ℚ)) / (l : ℚ)) • (1 : Matrix (Fin 1) (Fin 1) ℚ))) ∼ₘ
        1 ⊕ₘ (1 ⊕ₘ (-((k : ℚ) - (l : ℚ)) / (l : ℚ)) • 1) := by
      apply matCongrAssocOfMatCongr
      apply matCongrOplusRightOfMatCongr
      rw [←smul_oplus, one_oplus_one, ←Nat.cast_sub l_le_k]
      apply matCongrOneOfFourDiv cardX hkl'
    have key := oplusLeftCancel transpose_one.symm (by
      simp [transpose_oplus]) (by
      simp [transpose_oplus]) <|
        trans (brcKey Φ hrep hl hkl |>.symm |>
        oplusInsertMatCongr
        (((k : ℚ) - l) • (1 : Matrix (Fin 1) (Fin 1) ℚ))) aux
    nth_rewrite 3 [←one_smul ℚ (1 : Matrix (Fin 1) (Fin 1) ℚ)] at key
    obtain ⟨y, z, hyz⟩ := (matCongr_two_by_two_condition key) 1 0
    simp only [neg_mul, one_pow, mul_one, neg_sub, ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true, zero_pow, mul_zero, add_zero] at hyz
    set d : ℚ := (y.den * z.den) ^ 2 with d_def
    have hyz' := congrArg (HMul.hMul d) hyz.symm
    have hd₁ : y ^ 2 * d = (y.num * z.den) ^ 2 := by
      rw [d_def, mul_pow, mul_pow]; nth_rewrite 1 [←Rat.num_div_den y]
      field_simp; group
    have hd₂ : z ^ 2 * d = (y.den * z.num) ^ 2 := by
      rw [d_def, mul_pow, mul_pow]; nth_rewrite 1 [←Rat.num_div_den z]
      field_simp; group
    rw [mul_one, mul_add, mul_comm d, mul_comm d, neg_mul, mul_assoc,
      mul_assoc, hd₁, hd₂, d_def] at hyz'
    norm_cast at hyz'
    use y.den * z.den, y.num * z.den, y.den * z.num
    constructor
    · simp
    · rw [Odd.neg_one_pow hu, neg_mul, one_mul, ←Nat.cast_sub l_le_k,
        neg_mul, ←hyz']
      rfl

end CombinatorialDesign
