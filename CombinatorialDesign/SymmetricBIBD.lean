import CombinatorialDesign.FisherInequality
import CombinatorialDesign.MatrixLemmas
import CombinatorialDesign.MatrixCongruence

open CombinatorialDesign Matrix Finset MatCongr
namespace CombinatorialDesign

variable {ι X : Type*} [Fintype X] [Fintype ι] [DecidableEq X] [DecidableEq ι] {v k l : ℕ} (Φ : BIBD X X k l)

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

theorem bruck_ryser_chowla_even [Inhabited X]
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

theorem l_lt_k_of_symmBIBD [Inhabited X] (Φ : BIBD X X k l) : l < k := by
  induction' l with l _
  · exact k_pos_of_bibd Φ
  have aux : k - 1 < Fintype.card X - 1 :=
    Nat.sub_lt_sub_right (k_pos_of_bibd Φ) Φ.hvk.1
  exact Nat.lt_of_mul_lt_mul_right (calc
    (l + 1) * (k - 1) < (l + 1) * (Fintype.card X - 1) :=
      Nat.zero_lt_succ l |> Nat.mul_lt_mul_of_pos_left aux
    _ = k * (k - 1) := eq_of_symmBIBD Φ)

theorem l_le_k_of_symmBIBD [Inhabited X] (Φ : BIBD X X k l) : l ≤ k :=
  l_lt_k_of_symmBIBD Φ |> Nat.le_of_succ_le

theorem k_sub_l_lt_v_minus_k_of_symmBIBD [Inhabited X] (Φ : BIBD X X k l)
    (hyp : l + 2 ≤ k) : k - l < Fintype.card X - k := by
  have lk_nat : l + 1 ≤ k := l_lt_k_of_symmBIBD Φ
  have _ := l_le_k_of_symmBIBD Φ
  suffices (k : ℤ) - l < Fintype.card X - k by
    have _ := Nat.le_of_succ_le Φ.hvk.1
    norm_cast at this
  by_contra h
  have k1 : 1 ≤ k := k_pos_of_bibd Φ
  have v1 : 1 ≤ Fintype.card X := NeZero.one_le
  rw [not_lt, tsub_le_iff_right] at h
  have aux := calc
    (k : ℤ) * (k - 1) = l * (Fintype.card X - 1) := by
      have := (eq_of_symmBIBD Φ).symm
      norm_cast
    _ ≤ l * (k - l + k - 1) := by
      exact Int.mul_le_mul (le_refl _) (Int.sub_le_sub_right h _)
        (Int.sub_nonneg.mpr (Int.toNat_le.mp (by exact v1)))
        (Int.natCast_nonneg l)
  rw [←tsub_nonpos] at aux
  have : (k : ℤ) * (k - 1) - l * (k - l + k - 1) =
    (k - l) * (k - l - 1) := by ring
  rw [this] at aux
  have kl1 : 0 ≤ (k : ℤ) - l - 1 := by
    rw [sub_sub, le_sub_iff_add_le, zero_add]
    norm_cast
  have kl : 0 ≤ (k : ℤ) - l :=
    l_le_k_of_symmBIBD Φ |> Int.ofNat_le.mpr |> Int.sub_nonneg_of_le
  have aux₀ : ((k : ℤ) - l) * (k - l - 1) = 0 :=
    Int.le_antisymm aux (Int.mul_nonneg kl kl1)
  rw [mul_eq_zero] at aux₀
  cases aux₀ with
  | inl aux₀ =>
    rw [Int.sub_eq_zero, Nat.cast_inj] at aux₀
    rw [aux₀, add_le_iff_nonpos_right] at hyp
    exact Nat.not_succ_le_zero 1 hyp
  | inr aux₀ =>
    have : k = l + 1 := by
      rw [sub_sub, Int.sub_eq_zero] at aux₀
      norm_cast at aux₀
    rw [this, add_le_add_iff_left] at hyp
    simp only [Nat.not_ofNat_le_one] at hyp

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
