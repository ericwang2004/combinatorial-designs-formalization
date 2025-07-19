import Mathlib.Data.Matrix.Rank
import Mathlib.Data.Finset.Basic
import Mathlib.NumberTheory.SumFourSquares
import Mathlib.LinearAlgebra.Matrix.Block

open Matrix Finset

structure MatCongr {n α : Type*} [Fintype n] [DecidableEq n] [CommRing α]
    (P N : Matrix n n α) where
  A : Matrix n n α
  inv : Invertible A
  cong : P = A * N * Aᵀ

infixl:55 " ∼ₘ " => MatCongr

namespace MatCongr

variable {n α : Type*} [Fintype n] [DecidableEq n] [Field α]
  {N' N P : Matrix n n α}

@[symm] protected def symm (c : P ∼ₘ N) : N ∼ₘ P :=
  have := c.inv
  {
    A := ⅟c.A
    inv := invertibleOfInvertibleTranspose _
    cong := by simp only [c.cong, transpose_invOf]; group; simp
  }

@[refl] protected def refl (N : Matrix n n α) : N ∼ₘ N where
  A := 1
  inv := invertibleOne
  cong := by rw [one_mul, transpose_one, mul_one]

@[trans] protected def trans (c₁ : N' ∼ₘ N) (c₂ : N ∼ₘ P) : N' ∼ₘ P where
    A := c₁.A * c₂.A
    inv := c₁.inv.mul c₂.inv
    cong := by simp only [c₁.cong, c₂.cong, transpose_mul]; group

instance : Trans (@MatCongr n α _ _ _) MatCongr MatCongr where
  trans := MatCongr.trans

variable {m : Type*} [Fintype m] [DecidableEq m]

def reindexMatCongr (e : n ≃ m) (c : N' ∼ₘ N) :
    reindexAlgEquiv α α e N' ∼ₘ reindexAlgEquiv α α e N :=
  have := c.inv
  {
    A := reindexAlgEquiv α α e c.A
    inv := Invertible.map _ _
    cong := by simp [c.cong]
  }

def matDirectSum (M : Matrix m m α) (N : Matrix n n α) :=
  fromBlocks M 0 0 N

infixl:60 " ⊕ₘ " => matDirectSum

variable {o : Type*} [Fintype o] [DecidableEq o]
  {M : Matrix m m α} {O : Matrix o o α}

def matDirectSumAssoc :
    reindexAlgEquiv α α (Equiv.sumAssoc _ _ _) (M ⊕ₘ N ⊕ₘ O) ∼ₘ
    M ⊕ₘ (N ⊕ₘ O) where
  A := 1
  inv := invertibleOne
  cong := by aesop

def matDirectSumAssoc' :
    reindexAlgEquiv α α (Equiv.sumAssoc _ _ _).symm (M ⊕ₘ (N ⊕ₘ O)) ∼ₘ
    M ⊕ₘ N ⊕ₘ O where
  A := 1
  inv := invertibleOne
  cong := by aesop

def matCongrAssocOfMatCongr {M' : Matrix m m α} {O' : Matrix o o α}
    (h : M ⊕ₘ N ⊕ₘ O ∼ₘ M' ⊕ₘ N' ⊕ₘ O') : M ⊕ₘ (N ⊕ₘ O) ∼ₘ M' ⊕ₘ (N' ⊕ₘ O') := by
  calc
    _ ∼ₘ reindexAlgEquiv α α (Equiv.sumAssoc _ _ _) (M ⊕ₘ N ⊕ₘ O) :=
      matDirectSumAssoc.symm
    _ ∼ₘ reindexAlgEquiv α α (Equiv.sumAssoc _ _ _) (M' ⊕ₘ N' ⊕ₘ O') :=
      reindexMatCongr (Equiv.sumAssoc _ _ _) h
    _ ∼ₘ M' ⊕ₘ (N' ⊕ₘ O') := matDirectSumAssoc


theorem det_oplus : det (M ⊕ₘ N) = det M * det N := by
  rw [matDirectSum, det_fromBlocks_zero₂₁]

def matCongrOplusReindexOfMatCongr {m' : Type*} [Fintype m'] [DecidableEq m']
    {M' : Matrix m m α} {N' : Matrix n n α} (e : m ≃ m') (h : M' ⊕ₘ N' ∼ₘ M ⊕ₘ N) :
    reindexAlgEquiv α α e M' ⊕ₘ N' ∼ₘ reindexAlgEquiv α α e M ⊕ₘ N :=
  let e' : m ⊕ n ≃ m' ⊕ n := e.sumCongr (Equiv.refl n)
  have := h.inv
  have aux (M₁ : Matrix m m α) (N₁ : Matrix n n α) :
      (reindexAlgEquiv α α e) M₁ ⊕ₘ N₁ = (reindexAlgEquiv α α e') (M₁ ⊕ₘ N₁) := by
    simp only [matDirectSum]; aesop
  {
    A := reindexAlgEquiv α α e' h.A
    inv := Invertible.map _ _
    cong := by
      simp only [aux M' N', aux M N, h.cong, reindexAlgEquiv_mul]
      rfl
  }

omit [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m] in
theorem smul_oplus {a : α} : a • (M ⊕ₘ N) = a • M ⊕ₘ a • N := by
  rw [matDirectSum]; aesop

omit [Fintype n] [Fintype m] in
theorem one_oplus_one : (1 : Matrix m m α) ⊕ₘ (1 : Matrix n n α) = 1 := by
  rw [matDirectSum, fromBlocks_one]

def matCongrSmulOfMatCongr {a : α} (h : N ∼ₘ P) : a • N ∼ₘ a • P where
  A := h.A
  inv := h.inv
  cong := by simp only [h.cong, mul_smul_comm, smul_mul_assoc]

omit [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m] in
theorem transpose_oplus : (M ⊕ₘ N)ᵀ = Mᵀ ⊕ₘ Nᵀ := by
  simp [matDirectSum, fromBlocks_transpose]

noncomputable def matCongrOplusRightOfMatCongr
    (M : Matrix m m α) (h : N ∼ₘ P) : N ⊕ₘ M ∼ₘ P ⊕ₘ M where
  A := h.A ⊕ₘ 1
  inv := by
    have := h.inv
    apply invertibleOfIsUnitDet
    rw [isUnit_iff_ne_zero, det_oplus]
    refine (mul_ne_zero_iff_right ?_).mpr ?_
    · rw [det_one]; exact one_ne_zero
    · apply det_ne_zero_of_left_inverse (B := ⅟h.A)
      rw [invOf_eq_nonsing_inv, inv_mul_of_invertible]
  cong := by
    simp [matDirectSum, fromBlocks_multiply, fromBlocks_transpose, h.cong]

theorem reindexAlgEquiv_oplus (M : Matrix m m α) (N : Matrix n n α) :
    reindexAlgEquiv α α (Equiv.sumComm _ _) (M ⊕ₘ N) = N ⊕ₘ M := by
  simp [matDirectSum]

theorem reindexAlgEquiv_oplus_oplus
    (M : Matrix m m α) (N : Matrix n n α) (O : Matrix o o α) :
    reindexAlgEquiv α α (Equiv.sumCongr (Equiv.refl _) (Equiv.sumComm _ _))
      (M ⊕ₘ (N ⊕ₘ O)) = (M ⊕ₘ (O ⊕ₘ N)) := by
  aesop

def matCongrCommOfMatCongr {M' : Matrix m m α} {N' : Matrix n n α}
    (h : M' ⊕ₘ N' ∼ₘ M ⊕ₘ N) : N' ⊕ₘ M' ∼ₘ N ⊕ₘ M := by
  rw [←reindexAlgEquiv_oplus M N, ←reindexAlgEquiv_oplus M' N']
  exact reindexMatCongr _ h

noncomputable def matCongrOplusLeftOfMatCongr
    (M : Matrix m m α) (h : N ∼ₘ P) : M ⊕ₘ N ∼ₘ M ⊕ₘ P :=
  matCongrOplusRightOfMatCongr M h |> matCongrCommOfMatCongr

noncomputable def oplusInsertMatCongr {M' : Matrix m m α} {N' : Matrix n n α}
    (O : Matrix o o α) (h : M' ⊕ₘ N' ∼ₘ M ⊕ₘ N) :
    M' ⊕ₘ (O ⊕ₘ N') ∼ₘ M ⊕ₘ (O ⊕ₘ N) := by
  have h' := matCongrOplusRightOfMatCongr O h |> matCongrAssocOfMatCongr
  let e : m ⊕ n ⊕ o ≃ m ⊕ o ⊕ n :=
    Equiv.sumCongr (Equiv.refl _) (Equiv.sumComm _ _)
  rw [←reindexAlgEquiv_oplus_oplus M' N' O, ←reindexAlgEquiv_oplus_oplus M N O]
  exact reindexMatCongr _ h'

def toQuadraticForm (M : Matrix m m α) : (m → α) → α :=
  fun x ↦ x ᵥ* M ⬝ᵥ x

theorem equiv_forms_of_matCongr' {M N : Matrix m m α} (h : M ∼ₘ N) :
    {toQuadraticForm M x | x} ⊆ {toQuadraticForm N x | x} := by
  rintro _ ⟨x, rfl⟩
  use h.Aᵀ *ᵥ x
  rw [toQuadraticForm, toQuadraticForm, mulVec_transpose, vecMul_vecMul,
    ←mulVec_transpose h.A, dotProduct_mulVec, vecMul_vecMul, ←h.cong]

theorem equiv_forms_of_matCongr {M N : Matrix m m α} (h : M ∼ₘ N) :
    {toQuadraticForm M x | x} = {toQuadraticForm N x | x} := by
  have h' := h.symm
  rw [Set.Subset.antisymm_iff]
  exact ⟨equiv_forms_of_matCongr' h, equiv_forms_of_matCongr' h'⟩

theorem toQuadraticForm_two_by_two {a b : α} (x : Fin 1 ⊕ Fin 1 → α):
    let M := a • (1 : Matrix (Fin 1) (Fin 1) α) ⊕ₘ b • (1 : Matrix (Fin 1) (Fin 1) α)
    toQuadraticForm M x = a * (x (Sum.inl 0))^2 + b * (x (Sum.inr 0))^2 := by
  simp [toQuadraticForm, matDirectSum, vecMul_fromBlocks, dotProduct, vecMul]
  group

theorem image_of_two_by_two (a b : α) :
    {toQuadraticForm (a • 1 ⊕ₘ b • 1 : Matrix (Fin 1 ⊕ Fin 1) _ _) x | x} =
    {z | ∃ x₁ x₂, z = a * x₁^2 + b * x₂^2} := by
  ext; exact ⟨
    fun ⟨x, hx⟩ ↦ ⟨x (Sum.inl 0), x (Sum.inr 0), by
      rw [←hx, toQuadraticForm_two_by_two]⟩,
    fun ⟨x₁, x₂, hx⟩ ↦ ⟨Sum.elim (fun _ ↦ x₁) (fun _ ↦ x₂), by
      rw [toQuadraticForm_two_by_two, hx]; rfl⟩
  ⟩

theorem matCongr_two_by_two_condition {a b c d : α}
    (h : a • (1 : Matrix (Fin 1) (Fin 1) α) ⊕ₘ
    b • (1 : Matrix (Fin 1) (Fin 1) α) ∼ₘ c • 1 ⊕ₘ d • 1) :
    ∀ w x, ∃ y z, a * y^2 + b * z^2 = c * w^2 + d * x^2 := by
  have aux := image_of_two_by_two a b
  rw [equiv_forms_of_matCongr h, image_of_two_by_two c d] at aux
  intro w x
  obtain ⟨_, _, h⟩ := aux.subset (by use w, x)
  exact ⟨_, _, h.symm⟩

noncomputable def matCongrOneOfFourDiv [CharZero α] (hn : 4 ∣ Fintype.card n)
    {m : ℤ} (mpos : 0 < m) : (m : α) • (1 : Matrix n n α) ∼ₘ (1 : Matrix n n α) := by
  have this : ∃ a b c d : ℕ, a^2 + b^2 + c^2 + d^2 = m.toNat :=
    Nat.sum_four_squares m.toNat
  set a := this.choose with ha
  set b:= this.choose_spec.choose with hb
  set c := this.choose_spec.choose_spec.choose with hc
  set d := this.choose_spec.choose_spec.choose_spec.choose with hd
  set hsum := this.choose_spec.choose_spec.choose_spec.choose_spec
  simp_rw [← ha, ← hb, ← hc, ← hd] at hsum
  zify at hsum
  simp only [Int.toNat_of_nonneg (le_of_lt mpos)] at hsum
  set A':=!![(a : α), (b : α), (c : α), (d : α);
     (b : α), -(a : α), (d : α), -(c : α);
     (c : α), -(d : α), -(a : α), (b : α);
     (d : α), (c : α), -(b : α), -(a : α)] with hA'
  have HA' : A' * A'ᵀ = (m : α) • 1 := by
    ext i j
    by_cases hij : i = j
    . subst hij
      fin_cases i
      <;> simp [Matrix.mul_apply, dotProduct, Fin.sum_univ_four, A', ← pow_two, ← hsum]
      <;> ring
    . fin_cases i
      <;> fin_cases j
      <;> first
        | cases hij rfl
        | simp [ Matrix.mul_apply, Matrix.one_apply, dotProduct,
                Fin.sum_univ_four, A', hij]; ring
  let k := Fintype.card n / 4
  let e₁ : n ≃ Fin (4 * k) := Fintype.equivFinOfCardEq (by rw [Nat.mul_div_cancel' hn])
  let e₂ : Fin (4 * k) ≃ Fin 4 × Fin k := finProdFinEquiv.symm
  let e : n ≃ Fin 4 × Fin k := Equiv.trans e₁ e₂
  set A := reindex e.symm e.symm (blockDiagonal (fun _ : Fin k ↦ A')) with h
  have HA : A * Aᵀ = (m : α) • (1 : Matrix n n α) := by
    simp only [A]
    rw [reindex_apply, transpose_submatrix, blockDiagonal_transpose, Equiv.symm_symm,
      submatrix_mul_equiv, ← @blockDiagonal_mul, HA']
    ext i j
    simp only [submatrix_apply, smul_apply, smul_eq_mul, smul_one_eq_diagonal,
      blockDiagonal_diagonal, diagonal_apply]
    by_cases p : i = j
    . subst p
      simp only [↓reduceIte, one_apply_eq, mul_one, A, A']
    . simp only [one_apply_ne p]
      have h_ne : (e i ≠ e j) := by
        simp [ne_eq, EmbeddingLike.apply_eq_iff_eq, p]
      simp only [h_ne, ↓reduceIte, mul_zero, A, A']
  have A_is_invertible : Invertible A := by
    refine A.invertibleOfRightInverse ?_ ?_
    · exact (m : α)⁻¹ • Aᵀ
    simp only [Algebra.mul_smul_comm, HA, A, A']
    refine inv_smul_smul₀ ?_ 1
    refine Int.cast_ne_zero.mpr  (Ne.symm (Int.ne_of_lt mpos))
  exact {
    A := A
    inv := A_is_invertible
    cong := by
      simp only [reindexAlgEquiv_refl, zsmul_eq_mul, mul_one, map_intCast, HA, A', A,
        Int.cast_smul_eq_zsmul, zsmul_eq_mul, mul_one]
      }

def oplusLeftCancel [CharZero α] (hM : M = Mᵀ) (hN : N = Nᵀ) (hP : P = Pᵀ)
    (h : M ⊕ₘ N ∼ₘ M ⊕ₘ P) : N ∼ₘ P :=
  sorry

end MatCongr
