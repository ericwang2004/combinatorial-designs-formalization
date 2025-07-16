import CombinatorialDesign.FisherInequality
import CombinatorialDesign.MatrixLemmas

open CombinatorialDesign Matrix Finset
namespace CombinatorialDesign

variable {ι X} [Fintype X] [Fintype ι] [DecidableEq X] [DecidableEq ι] {v k l : ℕ} (Φ : BIBD X X k l)

theorem card_inter_block_eq_l
    [Inhabited X] {i j : X} (inej : i ≠ j) : #(Φ.blocks i ∩ Φ.blocks j) = l := by
  let M := toIncMat ℚ Φ.toDesign
  have rankM : rank M = (Fintype.card X) :=
    rank_eq_v_of_symmNontrivialRPBD ℚ (BIBD_to_nontrivialRPBD Φ (by exact i))
  have MtM i j : (Mᵀ * M) i j = #(Φ.blocks i ∩ Φ.blocks j) := by
    simp only [mul_apply, transpose_apply, M, toIncMat, of_apply, mul_ite, mul_one, mul_zero,
      sum_ite_mem, univ_inter, sum_const, nsmul_eq_mul, Nat.cast_inj, inter_comm]
  have MMt : M * Mᵀ = (l : ℚ) • allOnes X X _ + ((rep Φ : ℚ) - l) • 1 :=
    (rpbdCondition_of_rpbd (α := ℚ) (BIBD_to_RPBD Φ)).2
  have MMtM : M * (Mᵀ * M) = M * (of (if · = · then k else l) : Matrix X X ℚ) := by
    rw [← Matrix.mul_assoc, MMt, Matrix.add_mul, Matrix.smul_mul, Matrix.smul_mul, Matrix.one_mul]
    ext
    simp only [allOnes, mul_apply, add_apply, smul_apply, of_apply, one_mul, smul_eq_mul, mul_ite]
    rw [col_sum_incmat, sum_ite, sum_eq_single _ (by
      simp only [mem_filter, mem_univ]; tauto) (by simp only [mem_filter, mem_univ]; tauto),
      filter_ne', sum_erase_eq_sub (mem_univ _), ←sum_mul, row_sum_incmat,
      (b_eq_v_iff_rep_eq_k Φ).mp rfl]
    group
  have := ext_iff.mpr (eq_of_full_rank_mul_eq (Equiv.refl X) rankM MMtM) i j
  simp_all only [MtM, of_apply, inej, ite_false, Nat.cast_inj]

theorem l_le_k_of_symmBIBD [Inhabited X] (Φ : BIBD X X k l) : l ≤ k := by
  sorry

theorem bibd_of_symmNontrivialRPBD  {r : ℕ} (Ψ : nontrivialRPBD X X l r) :
    ∀ i, #(Ψ.blocks i) * r = r + l * ((Fintype.card X) - 1) := by
  intro i
  let M := toIncMat ℚ Ψ.toDesign
  have rankM : rank M = (Fintype.card X) := rank_eq_v_of_symmNontrivialRPBD ℚ Ψ
  have Mt1 j : (Mᵀ * allOnes X (Fin 1) ℚ) j 0 = #(Ψ.blocks j) := by
    simp only [M, toIncMat, allOnes, mul_apply, of_apply, transpose_apply, mul_one, sum_ite_mem,
      univ_inter, sum_const, nsmul_one]
  have MMt : M * Mᵀ = (l : ℚ) • allOnes X X ℚ + ((r : ℚ) - (l : ℚ)) • 1 :=
    (rpbdCondition_of_rpbd (α := ℚ) Ψ.toRPBD).2
  have hr : (r : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr <| Nat.ne_zero_of_lt <| r_pos_of_nontrivialRPBD Ψ
  have MMt1 : M * (Mᵀ * allOnes X (Fin 1) ℚ) =
      M * ((1 : ℚ) + ((l : ℚ) * (((Fintype.card X) : ℚ) - 1) / (r : ℚ))) • allOnes _ _ _ := by
    rw [←Matrix.mul_assoc, MMt, Matrix.mul_smul, rpbd_incmat_allOnes]
    ext
    simp only [allOnes, smul_apply, of_apply, add_apply, mul_apply, one_apply, mul_one,
      smul_eq_mul, mul_ite, mul_zero]
    rw [sum_add_distrib, sum_const, card_univ, sum_eq_single _ (by
      intro; simp only [ite_eq_right_iff]; tauto) (by simp only [mem_univ]; tauto),
      nsmul_eq_mul]
    simp only [reduceIte]
    ring_nf; field_simp
  have := ext_iff.mpr (eq_of_full_rank_mul_eq (Equiv.refl X) rankM MMt1) i 0
  simp only [Mt1] at this
  simp only [allOnes, Fin.isValue, smul_apply, of_apply, smul_eq_mul, mul_one] at this
  rw [←mul_left_inj' hr] at this
  field_simp at this
  rwa [←Nat.cast_one, ←Nat.cast_sub (v_pos_of_nontrivialRPBD Ψ), ←Nat.cast_mul,
    ←Nat.cast_mul, ←Nat.cast_add, Nat.cast_inj] at this

theorem r_div_of_symmNontrivialRPBD {r : ℕ} (Ψ : nontrivialRPBD X X l r) :
    r ∣ l * ((Fintype.card X) - 1) := by
  suffices h : r ∣ r + l * ((Fintype.card X) - 1) from Nat.dvd_add_self_left.mp h
  let i : X := (Fintype.card_pos_iff.1 (v_pos_of_nontrivialRPBD Ψ)).some
  use #(Ψ.blocks i)
  rw [←bibd_of_symmNontrivialRPBD Ψ, mul_comm]

omit [DecidableEq X] in
private theorem vlr {l r : ℕ} (h : r ∣ l * ((Fintype.card X) - 1)) :
    (1 + l * ((Fintype.card X) - 1) / r) * r = r + l * ((Fintype.card X) - 1) := by
  rw [add_mul, one_mul, Nat.div_mul_cancel h]

def symmNontrivialRPBD_to_symmBIBD {r : ℕ} (hl : l > 0) (Ψ : nontrivialRPBD X X l r) :
    BIBD X X (1 + l * ((Fintype.card X) - 1) / r) l where
  toBBD := Ψ.toBBD
  hvk := by
    have rpos := r_pos_of_nontrivialRPBD Ψ
    have rdiv := r_div_of_symmNontrivialRPBD Ψ
    have hv : (Fintype.card X) - 1 > 0 := v_ge_two_of_nontrivialRPBD Ψ |> Nat.zero_lt_sub_of_lt
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

theorem perfect_square_of_even_symmBIBD [Inhabited X]
    (hv : Even (Fintype.card X)) (Φ : BIBD X X k l) : IsSquare (k - l) := by
  set v := Fintype.card X
  cases eq_or_ne (k - l) 0 with
  | inl h => rw [h]; exact IsSquare.zero
  | inr h =>
  set M := toIncMat ℚ Φ.toDesign
  have repk := (b_eq_v_iff_rep_eq_k Φ).mp rfl
  have repl := BIBD_to_nontrivialRPBD Φ
    (Fintype.card_pos_iff.1 (v_pos_of_bibd Φ)).some |> l_lt_r_of_nontrivialRPBD
  have vge1 : v ≥ 1 := v_pos_of_bibd Φ
  have kge1 : k ≥ 1 := k_pos_of_bibd Φ
  have kl := le_of_le_of_eq (Nat.le_of_succ_le repl) repk
  have kl_cast_ne : (k : ℚ) - l ≠ 0 :=
    fun hyp ↦ by norm_cast at hyp
  have lv1_cast : (l : ℚ) * (v - 1) = k * (k - 1) := by
    have := eq_of_symmBIBD Φ; norm_cast
  have MMt : M * Mᵀ = (l : ℚ) • allOnes X X _ + ((rep Φ : ℚ) - l) • 1 :=
    (rpbdCondition_of_rpbd (α := ℚ) (BIBD_to_RPBD Φ)).2
  have detMMt : det (M * Mᵀ) = k * k * (k - l) ^ (v - 1) := by
    rw [MMt, det_ones_add_diagonal, repk]
    · calc
        ((k : ℚ) - l) ^ v * (1 + l / (k - l) * v) = (k - l) ^ v * (((k - l) + l * v) / (k - l)) := by
          congr; rw [div_mul_eq_mul_div, ←div_self kl_cast_ne, div_add_div_same]
        _ = (k - l) ^ v * ((k + l * (v - 1)) / (k - l)) := by congr 2; group
        _ = (k - l) ^ v * (k ^ 2 / (k - l)) := by
          congr; rw [lv1_cast]; group
        _ = k * k * ((k - l) ^ v / (k - l) ^ 1) := by group
        _ = k * k * (k - l) ^ (v - 1) := by
          congr; rw [Field.div_eq_mul_inv, ←pow_sub₀ _ kl_cast_ne vge1]
    · rw [repk]; exact kl_cast_ne
  rw [det_mul, det_transpose] at detMMt
  have square : IsSquare (((k : ℚ) - l) ^ (v - 1)) := by
    use det M / k
    field_simp [detMMt]
  have := IsSquare.div (Even.isSquare_pow hv ((k : ℚ) - l)) square
  rwa [Field.div_eq_mul_inv, ←pow_sub₀ _ kl_cast_ne (Nat.sub_le _ _),
    Nat.sub_sub_self vge1, pow_one, ←Nat.cast_sub kl, Rat.isSquare_natCast_iff] at this

theorem sos_of_odd_symmBIBD [Inhabited X] {u : ℕ}
    (hv : Fintype.card X = 2 * u + 1) (Φ : BIBD X X k l) :
    ∃ x y z : ℤ, (x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0) ∧ x * x = (k - l) * y * y + (-1)^u * l * z * z := by
  cases eq_or_ne l 0 with
  | inl hl => use 0, 0, 1; simp [hl]
  | inr hl =>
  cases eq_or_ne k l with
  | inl hkl => use 0, 1, 0; simp [hkl]
  | inr hkl =>
  set v := Fintype.card X
  let A := toIncMat ℚ Φ.toDesign
  have hrep : rep Φ = k := by
    have := mul_eq_mul_right_iff.mp <| kb_eq_repv Φ
    simp only [Fintype.card_ne_zero, or_false] at this
    exact this.symm
  have AAt : A * Aᵀ = (l : ℚ) • allOnes X X _ + ((rep Φ : ℚ) - l) • 1 :=
    (rpbdCondition_of_rpbd (α := ℚ) (BIBD_to_RPBD Φ)).2
  cases Nat.even_or_odd u with
  | inl hu =>
    set v' := v - 1
    let A' := fromBlocks A (allOnes X (Fin 1) ℚ) (allOnes (Fin 1) X ℚ) (of (fun _ ↦ k/l))
    let D := (1 : Matrix X X ℚ) ⊕ₘ (-(l : ℚ) • (1 : Matrix (Fin 1) (Fin 1) ℚ))
    let E := ((k : ℚ) - l) • (1 : Matrix X X ℚ) ⊕ₘ (-((k : ℚ) - l) / (l : ℚ)) •
      (1 : Matrix (Fin 1) (Fin 1) ℚ)
    have hA' : A' * D * A'ᵀ = E := by
      simp only [A', D, E, MatCongr.matDirectSum, fromBlocks_multiply, fromBlocks_transpose,
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
      -- follows from eq_of_symmBIBD Φ
      sorry
    have detD : det D ≠ 0 := by simp [D, MatCongr.det_oplus, hl]
    have detE : det E ≠ 0 := by
      simp [E, MatCongr.det_oplus, hl, sub_eq_zero, hkl, hkl.symm]
    have detA : det A' ≠ 0 := by
      intro h
      exact detE (by calc
        det E = det (A' * D * A'ᵀ) := by rw [hA']
        _ = det A' * det D * det A'ᵀ := by rw [det_mul, det_mul]
        _ = 0 := by rw [h, zero_mul, zero_mul]
      )
    have invA' : Invertible A' := Ne.isUnit detA |> invertibleOfIsUnitDet _
    have hv' : 4 ∣ Fintype.card (Fin v') := by sorry
    have finadd : Fin v' ⊕ Fin 1 ≃ X :=
      have : Fintype.card X = v' + 1 := by
          simp_all only [add_tsub_cancel_right, v, v']
      Equiv.trans finSumFinEquiv (Fintype.equivFinOfCardEq this).symm
    have := calc
      (1 : Matrix (Fin v') (Fin v') ℚ) ⊕ₘ ((1 : Matrix (Fin 1) (Fin 1) ℚ) ⊕ₘ
          (-(l : ℚ) • (1 : Matrix (Fin 1) (Fin 1) ℚ))) ∼ₘ
          (1 : Matrix X X ℚ) ⊕ₘ (-(l : ℚ) • (1 : Matrix (Fin 1) (Fin 1) ℚ)) := by
        refine MatCongr.trans MatCongr.oplus_assoc.symm ?_
        refine MatCongr.oplus_congr (MatCongr.oplus_one ?_) (by rfl)
        exact finadd
      _ ∼ₘ ((k : ℚ) - l) • (1 : Matrix X X ℚ) ⊕ₘ
          (-((k : ℚ) - (l : ℚ)) / (l : ℚ)) • (1 : Matrix (Fin 1) (Fin 1) ℚ) := by
        symm
        constructor
        case A => exact A'
        case inv => exact invA'
        case toEquiv => exact Equiv.refl _
        exact hA'.symm
      _ ∼ₘ ((k : ℚ) - l) • (1 : Matrix (Fin v') (Fin v') ℚ) ⊕ₘ
          ((k : ℚ) - l) • (1 : Matrix (Fin 1) (Fin 1) ℚ) ⊕ₘ
          (-((k : ℚ) - (l : ℚ)) / (l : ℚ)) • (1 : Matrix (Fin 1) (Fin 1) ℚ) := by
        refine MatCongr.oplus_congr ?_ (by rfl)
        symm
        refine MatCongr.trans MatCongr.smul_oplus ?_
        apply MatCongr.smul_oplus_congr
        apply MatCongr.oplus_one finadd
      _ ∼ₘ (1 : Matrix (Fin v') (Fin v') ℚ) ⊕ₘ (((k : ℚ) - l) • (1 : Matrix (Fin 1) (Fin 1) ℚ)) ⊕ₘ
          (-((k : ℚ) - (l : ℚ)) / (l : ℚ)) • (1 : Matrix (Fin 1) (Fin 1) ℚ) := by
        repeat refine MatCongr.oplus_congr ?_ (by rfl)
        symm
        refine MatCongr.trans (MatCongr.matCongrOneOfFourDiv hv' (k - l) ?_).symm ?_
        · simp only [Nat.cast_lt, Int.sub_pos]
          exact Nat.lt_of_le_of_ne (l_le_k_of_symmBIBD Φ) hkl.symm
        simp only [Int.cast_sub, Int.cast_natCast]
        rfl
      _ ∼ₘ (1 : Matrix (Fin v') (Fin v') ℚ) ⊕ₘ ((((k : ℚ) - l) • (1 : Matrix (Fin 1) (Fin 1) ℚ)) ⊕ₘ
          (-((k : ℚ) - (l : ℚ)) / (l : ℚ)) • (1 : Matrix (Fin 1) (Fin 1) ℚ)) := by
        exact MatCongr.oplus_assoc
    have ⟨_, B, _, cong⟩ := MatCongr.oplus_left_cancel (by
      apply MatCongr.oplus_symmetric transpose_one.symm
      rw [transpose_smul, transpose_one]) (by
      apply MatCongr.oplus_symmetric
      all_goals rw [transpose_smul, transpose_one]) transpose_one.symm this
    have cong := Matrix.ext_iff.mpr cong
    simp only [MatCongr.matDirectSum, mul_apply] at cong
    sorry
  | inr hv' => sorry

end CombinatorialDesign
