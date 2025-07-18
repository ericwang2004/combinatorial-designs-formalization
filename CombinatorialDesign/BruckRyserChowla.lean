import CombinatorialDesign.FisherInequality
import CombinatorialDesign.MatrixCongruence

open CombinatorialDesign Matrix Finset
namespace CombinatorialDesign

variable {ι X} [Fintype X] [Fintype ι] [DecidableEq X] [DecidableEq ι] {v k l : ℕ} (Φ : BIBD X X k l)

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
  {
    A := A'
    inv := by
      have detD : det D ≠ 0 := by
        simp [D, MatCongr.det_oplus, hl]
      have detE : det E ≠ 0 := by
        simp [E, MatCongr.det_oplus, hl, sub_eq_zero, hkl, hkl.symm]
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

theorem l_le_k_of_symmBIBD [Inhabited X] (Φ : BIBD X X k l) : l ≤ k := by
  sorry

theorem bruck_ryser_chowla_odd [Inhabited X] {u : ℕ}
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
  have l_le_k := l_le_k_of_symmBIBD Φ
  have AAt : A * Aᵀ = (l : ℚ) • allOnes X X _ + ((rep Φ : ℚ) - l) • 1 :=
    (rpbdCondition_of_rpbd (α := ℚ) (BIBD_to_RPBD Φ)).2
  cases Nat.even_or_odd u with
  | inl hu =>
    set v' := v - 1
    have hv' : 4 ∣ v' := by
      sorry
    let e : X ≃ Fin v' ⊕ Fin 1 := by
      sorry
    have aux₁ : 1 ⊕ₘ 1 = reindexAlgEquiv ℚ ℚ e 1 := by
      simp only [MatCongr.matDirectSum]; aesop
    have aux₂ : ((k : ℚ) - l) • 1 ⊕ₘ ((k : ℚ) - l) • 1 =
        reindexAlgEquiv ℚ ℚ e (((k : ℚ) - l) • 1) := by
      rw [map_rat_smul, ←MatCongr.smul_oplus, aux₁]
    have key : (1 : Matrix (Fin v') (Fin v') ℚ) ⊕ₘ (1 : Matrix (Fin 1) (Fin 1) ℚ) ⊕ₘ
        (-(l : ℚ) • (1 : Matrix (Fin 1) (Fin 1) ℚ)) ∼ₘ
        ((k : ℚ) - l) • 1 ⊕ₘ ((k : ℚ) - l) • 1 ⊕ₘ (-((k : ℚ) - (l : ℚ)) / (l : ℚ)) • 1 := by
      rw [aux₁, aux₂]
      exact brcKey Φ hrep hl hkl |>.symm |> MatCongr.matCongrOplusReindexOfMatCongr _
    have aux₃ : ((k : ℚ) - l) • (1 : Matrix (Fin v') (Fin v') ℚ) ∼ₘ 1 := by
      rw [←Nat.cast_sub l_le_k]
      apply MatCongr.matCongrOneOfFourDiv
      · rw [Fintype.card_fin]; exact hv'
      · rw [Int.ofNat_eq_coe, Nat.cast_pos']
        exact Nat.lt_of_le_of_ne l_le_k hkl.symm |> Nat.zero_lt_sub_of_lt
    have := MatCongr.trans (MatCongr.matCongrAssocOfMatCongr key)
      (MatCongr.matCongrOplusLeftOfMatCongr aux₃) |>
        MatCongr.oplusLeftCancel transpose_one.symm (by
        simp [MatCongr.transpose_oplus]) (by simp [MatCongr.transpose_oplus])

    sorry
  | inr hu =>
    sorry

end CombinatorialDesign
