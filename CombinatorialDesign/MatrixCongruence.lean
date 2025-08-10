import Mathlib.Data.Matrix.Rank
import Mathlib.Data.Finset.Basic
import Mathlib.NumberTheory.SumFourSquares
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.LinearAlgebra.Matrix.BilinearForm

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

def ratCastMatCongrOfMatCongr (α : Type*) [Field α] [CharZero α]
    {A B : Matrix m m ℚ} (h : A ∼ₘ B) :
    RingHom.mapMatrix (Rat.castHom α) A ∼ₘ
    RingHom.mapMatrix (Rat.castHom α) B where
  A := RingHom.mapMatrix (Rat.castHom α) h.A
  inv := by
    have := h.inv
    exact Invertible.map _ _
  cong := by
    have : ((Rat.castHom α).mapMatrix h.A)ᵀ =
      (Rat.castHom α).mapMatrix h.Aᵀ := rfl
    rw [this, ←RingHom.map_mul, ←RingHom.map_mul, ←h.cong]

theorem ratCast_one (α : Type*) [Field α] [CharZero α] :
    RingHom.mapMatrix (Rat.castHom α) (1 : Matrix m m ℚ) = 1 := by
  exact RingHom.map_one _

def matDirectSum (M : Matrix m m α) (N : Matrix n n α) :=
  fromBlocks M 0 0 N

infixl:60 " ⊕ₘ " => matDirectSum

variable {o : Type*} [Fintype o] [DecidableEq o]
  {M : Matrix m m α} {O : Matrix o o α}

theorem ratCast_smul [CharZero α] {a : ℚ} {A : Matrix m m ℚ} :
    RingHom.mapMatrix (Rat.castHom α) (a • A) =
    a • RingHom.mapMatrix (Rat.castHom α) A := by
  ext; simp [Rat.smul_def]

theorem ratCast_oplus (α : Type*) [Field α] [CharZero α]
    {A : Matrix m m ℚ} {B : Matrix n n ℚ} :
    RingHom.mapMatrix (Rat.castHom α) (A ⊕ₘ B) =
    RingHom.mapMatrix (Rat.castHom α) A ⊕ₘ
    RingHom.mapMatrix (Rat.castHom α) B := by
  rw [matDirectSum, matDirectSum]
  aesop

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

noncomputable def oplusLeftCancel_zero [CharZero α]
    (h : (0 : Matrix (Fin 0) (Fin 0) α) ⊕ₘ N ∼ₘ 0 ⊕ₘ P) : N ∼ₘ P := by
  obtain ⟨B, B', congB⟩ := h
  let e0 : Fin 0 ≃ Empty := by
    exact finZeroEquiv
  let e  : (Fin 0 ⊕ n) ≃ n := by
    exact Equiv.emptySum (Fin 0) n
  have cong' :
      reindexAlgEquiv α α e ((0 : Matrix (Fin 0) (Fin 0) α) ⊕ₘ N)
    = reindexAlgEquiv α α e B
      * reindexAlgEquiv α α e ((0 : Matrix (Fin 0) (Fin 0) α) ⊕ₘ P)
      * (reindexAlgEquiv α α e B)ᵀ := by
    simp only [reindexAlgEquiv_apply, reindex_apply, submatrix_mul_equiv, transpose_submatrix]
    exact congrFun (congrFun (congrArg submatrix congB) ⇑e.symm) ⇑e.symm
  have L : reindexAlgEquiv α α e ((0 : Matrix (Fin 0) (Fin 0) α) ⊕ₘ N) = N := by
    simp only [reindexAlgEquiv_apply, reindex_apply]
    rfl
  have R : reindexAlgEquiv α α e ((0 : Matrix (Fin 0) (Fin 0) α) ⊕ₘ P) = P := by
    simp only [reindexAlgEquiv_apply, reindex_apply]
    rfl
  let A : Matrix n n α := reindexAlgEquiv α α e B
  have hA : Invertible A := Invertible.map _ _
  have : N = A * P * Aᵀ := by simpa [L, R] using cong'
  exact {
    A := A
    inv := hA
    cong := this
  }

noncomputable def cancelLeft_1x1_any [CharZero α] (a : α)
    (hN : Invertible N) (hP : Invertible P)
    (h : (a • (1 : Matrix (Fin 1) (Fin 1) α)) ⊕ₘ N ∼ₘ (a • (1 : Matrix (Fin 1) (Fin 1) α)) ⊕ₘ P) :
    N ∼ₘ P := by
  obtain ⟨B,Binv,Bcongr⟩ := h
  let l  : Matrix (Fin 1) (Fin 1) α := submatrix B Sum.inl Sum.inl
  let xT : Matrix (Fin 1) n α       := submatrix B Sum.inl Sum.inr
  let y  : Matrix n (Fin 1) α       := submatrix B Sum.inr Sum.inl
  let z  : Matrix n n α             := submatrix B Sum.inr Sum.inr
  have B_blocks : B = fromBlocks l xT y z := by
    ext i j
    cases i <;> cases j
    all_goals
    simp [fromBlocks, l, xT, y, z, submatrix_apply]
  have h' : fromBlocks (a • (1 : Matrix (Fin 1) (Fin 1) α)) 0 0 N
          = fromBlocks l xT y z
            * fromBlocks (a • (1 : Matrix (Fin 1) (Fin 1) α)) 0 0 P
            * (fromBlocks l xT y z)ᵀ := by
    simpa [matDirectSum, B_blocks] using Bcongr
  have h'' : fromBlocks l xT y z * fromBlocks (a • (1 : Matrix (Fin 1) (Fin 1) α)) 0 0 P
          = fromBlocks (l * (a • 1)) (xT * P) (y * (a • (1 : Matrix (Fin 1) (Fin 1) α))) (z * P)
          := by
    simp [fromBlocks_multiply, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul]
  have BT : (fromBlocks l xT y z)ᵀ = fromBlocks lᵀ yᵀ xTᵀ zᵀ := by
    simp [fromBlocks_transpose]
  have hRHS :
      fromBlocks l xT y z
      * fromBlocks (a • (1 : Matrix (Fin 1) (Fin 1) α)) 0 0 P
      * (fromBlocks l xT y z)ᵀ
    = fromBlocks
        (l * (a • 1) * lᵀ + xT * P * xTᵀ)
        (l * (a • 1) * yᵀ + xT * P * zᵀ)
        (y * (a • (1 : Matrix (Fin 1) (Fin 1) α)) * lᵀ + z * P * xTᵀ)
        (y * (a • (1 : Matrix (Fin 1) (Fin 1) α)) * yᵀ + z * P * zᵀ) := by
    simp [Matrix.mul_assoc, BT, fromBlocks_multiply,
          Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
  have h_blocks :
      fromBlocks (a • (1 : Matrix (Fin 1) (Fin 1) α)) 0 0 N
    = fromBlocks
        (l * (a • 1) * lᵀ + xT * P * xTᵀ)
        (l * (a • 1) * yᵀ + xT * P * zᵀ)
        (y * (a • (1 : Matrix (Fin 1) (Fin 1) α)) * lᵀ + z * P * xTᵀ)
        (y * (a • (1 : Matrix (Fin 1) (Fin 1) α)) * yᵀ + z * P * zᵀ) := by
    simpa [hRHS] using h'
  have h11M : (a • (1 : Matrix (Fin 1) (Fin 1) α)) = l * (a • 1) * lᵀ + xT * P * xTᵀ := by
    simpa [fromBlocks] using
      congrArg (fun M => submatrix M Sum.inl Sum.inl) h_blocks
  have h12 : 0 = l * (a • 1) * yᵀ + xT * P * zᵀ := by
    simpa [fromBlocks] using
      congrArg (fun M => submatrix M Sum.inl Sum.inr) h_blocks
  have h21 : 0 = y * (a • (1 : Matrix (Fin 1) (Fin 1) α)) * lᵀ + z * P * xTᵀ := by
    simpa [fromBlocks] using
      congrArg (fun M => submatrix M Sum.inr Sum.inl) h_blocks
  have h22 : N = y * (a • (1 : Matrix (Fin 1) (Fin 1) α)) * yᵀ + z * P * zᵀ := by
    simpa [fromBlocks] using
      congrArg (fun M => submatrix M Sum.inr Sum.inr) h_blocks
  let a0 : α := l 0 0
  have h11 : (xT * P * xTᵀ) 0 0 = a * (1 - a0^2) := by
    have := congrArg (fun (M : Matrix (Fin 1) (Fin 1) α) => M 0 0) h11M
    simp only [Matrix.mul_apply, Fin.sum_univ_one, a0, pow_two,
      mul_comm, mul_left_comm, mul_assoc, sub_eq_add_neg] at this
    simp only [Fin.isValue, smul_apply, one_apply_eq, smul_eq_mul, mul_one,
      Algebra.smul_mul_assoc, one_mul, Algebra.mul_smul_comm, add_apply] at this
    rw [mul_apply] at this
    simp only [univ_unique, Fin.default_eq_zero, Fin.isValue, transpose_apply,
      sum_singleton] at this
    simp only [mul_one_sub, eq_sub_iff_add_eq, a0, sq, add_comm]
    exact this.symm
  have h12' : xT * P * zᵀ = - (a * a0) • yᵀ := by
    have this1 : xT * P * zᵀ = - (l * (a • 1) * yᵀ) := by
      simp only [Algebra.mul_smul_comm, mul_one, smul_mul] at h12 ⊢
      exact Eq.symm (neg_eq_of_add_eq_zero_right (id (Eq.symm h12)))
    have l_as_scalar : l = (a0) • (1 : Matrix (Fin 1) (Fin 1) α) := by
      ext i j
      fin_cases i; fin_cases j
      simp [a0]
    have this2: l * (a • 1) * yᵀ = (a0 * a) • yᵀ := by
      simp only [l_as_scalar, Matrix.mul_smul, Matrix.smul_mul, mul_comm,
        mul_left_comm, mul_assoc, mul_one, Matrix.one_mul]
      exact smul_smul a a0 yᵀ
    simp only [this2, mul_comm] at this1
    simp only [this1]
    exact Eq.symm (neg_smul (a * a0) yᵀ)
  have h21' : z * P * xTᵀ = - (a * a0) • y := by
    have this1 : z * P * xTᵀ = - (y * (a • (1 :Matrix (Fin 1) (Fin 1) α)) * lᵀ) := by
      simp only [Algebra.mul_smul_comm, mul_one, smul_mul] at h21 ⊢
      exact Eq.symm (neg_eq_of_add_eq_zero_right (id (Eq.symm h21)))
    have lT_as_scalar : lᵀ = (a0) • (1 : Matrix (Fin 1) (Fin 1) α) := by
      simp only [a0]
      ext i j
      fin_cases i; fin_cases j
      simp only [Fin.zero_eta, Fin.isValue, transpose_apply, smul_apply,
        one_apply_eq, smul_eq_mul, mul_one]
    have this2 : y * (a • (1 :Matrix (Fin 1) (Fin 1) α)) * lᵀ = (a * a0) • y := by
      rw [lT_as_scalar]
      simp only [Matrix.mul_smul, Matrix.mul_one]
      match_scalars
      ring_nf
    simp [this2] at this1
    simp only [this1, neg_smul, neg_inj, a0, lT_as_scalar, Fin.isValue,
      Matrix.mul_smul, Matrix.mul_one]
    exact smul_smul a (l 0 0) y
  have hc : ∃ c : α, - 2 * a0 * c + (1 - a0^2) * c^2 = (1 : α) := by
    by_cases hl_minus : (1 : α) - a0 ≠ 0
    . refine ⟨((1 : α) - a0)⁻¹, ?_⟩
      calc
        -2 * a0 * (1 - a0)⁻¹ + (1 - a0 ^ 2) * (1 - a0)⁻¹ ^ 2
        = -2 * a0 * (1 - a0)⁻¹ + ((1 + a0) * (1- a0)) * ((1 - a0)^ 2)⁻¹ := by
          field_simp
          left
          nth_rw 1 [(one_pow 2).symm, sq_sub_sq 1 a0]
      _ = -2 * a0 * (1 - a0)⁻¹ + (1 + a0) * (1 - a0)⁻¹ := by
          congr 1
          field_simp [hl_minus]
          ring_nf
      _ = (-2 * a0 + (1 + a0)) * (1 - a0)⁻¹ := by
          ring_nf
      _ = (1 - a0) * (1 - a0)⁻¹ := by
          ring_nf
      _ = 1 := by
          field_simp [hl_minus]
    . have hl_plus : (1 : α) + a0 ≠ 0 := by
        simp only [Fin.isValue, ne_eq, Decidable.not_not] at hl_minus
        by_contra hl_plus
        have hsum0 : (1 - a0) + (1 + a0) = 0 := by
          simp [hl_minus, hl_plus]
        simp only [Fin.isValue, sub_add_add_cancel] at hsum0
        have htwo : (2 : α) = 0 := by
          simp only [add_self_eq_zero, one_ne_zero] at hsum0
        have : (2 : α) ≠ 0 := by
          exact_mod_cast (by decide : (2 : ℕ) ≠ 0)
        exact this htwo
      refine ⟨-((1 : α) + a0)⁻¹, ?_⟩
      calc
        -2 * a0 * -(1 + a0)⁻¹ + (1 - a0 ^ 2) * (-(1 + a0)⁻¹) ^ 2
      _ = 2 * a0 * (1 + a0)⁻¹ + (1 - a0 ^ 2) * ((1 + a0)⁻¹) ^ 2 := by
          simp only [neg_mul, mul_neg, neg_neg, even_two, Even.neg_pow, inv_pow]
      _ = 2 * a0 * (1 + a0)⁻¹ + ((1 + a0) * (1 - a0)) * ((1 + a0)^ 2)⁻¹ := by
          field_simp
          left
          nth_rw 1 [(one_pow 2).symm, sq_sub_sq 1 a0]
      _ = 2 * a0 * (1 + a0)⁻¹ + (1 - a0) * (1 + a0)⁻¹ := by
          congr 1
          field_simp [hl_plus]
          ring_nf
      _ = (2 * a0 + (1 - a0)) * (1 + a0)⁻¹ := by
          ring_nf
      _ = (1 + a0) * (1 + a0)⁻¹ := by
          ring_nf
      _ = 1 := by
          field_simp [hl_plus]
  let c : α := Classical.choose hc
  have hpoly0 :
    - 2 * a0 * c + (1 - a0^2) * c^2 = (1 : α) := Classical.choose_spec hc
  let S : Matrix n n α := z + c • (y * xT)
  have bottom : N = S * P * Sᵀ := by
    have := calc
      S * P * Sᵀ
        = (z * P + c • (y * xT * P)) * (z + c • (y * xT))ᵀ  := by
          congr 1
          simp only [S, Matrix.add_mul]
          congr 1
          exact smul_mul c (y * xT) P
      _ = z * P * zᵀ + c • (z * P * xTᵀ) * yᵀ
            + c • y * (xT * P * zᵀ) + (c^2) • (y * (xT * P * xTᵀ) * yᵀ) := by
          simp only [Matrix.transpose_add, Matrix.add_mul, Matrix.mul_add, add_assoc]
          congr 1
          field_simp
          simp only [← add_assoc, add_comm (c • (y * xT * P * zᵀ))]
          rw [← Matrix.mul_assoc, add_assoc, add_assoc]
          congr 1
          rw [add_comm, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc xT]
          congr 1
          rw [← Matrix.mul_assoc, Matrix.mul_assoc y, Matrix.mul_assoc y, smul_smul, @sq]
      _ = z * P * zᵀ + c • (-(a * a0) • y) * yᵀ + c • y * (-(a * a0) • yᵀ)
            + (c^2) • (y * ((a * (1 - a0^2)) • (1 : Matrix (Fin 1) (Fin 1) α)) * yᵀ) := by
          rw [h21', h12', ← h11]
          congr
          ext i j
          fin_cases i
          fin_cases j
          simp only [Fin.zero_eta, Fin.isValue, smul_apply, one_apply_eq, smul_eq_mul, mul_one]
      _ = z * P * zᵀ + (c * (-(a * a0))) • (y * yᵀ) + (c * (-(a * a0))) • (y * yᵀ)
            + (a * (1 - a0 ^ 2) * c ^ 2) • (y * yᵀ) := by
          simp only [add_assoc, add_assoc]
          congr 1
          have eq1 : c • (-(a * a0) • y) * yᵀ = (c * (-(a * a0))) • (y * yᵀ) := by
            simp only [neg_smul, smul_neg, Matrix.neg_mul, smul_mul, mul_neg, neg_inj]
            exact smul_smul c (a * a0) (y * yᵀ)
          have eq2 : c • y * (-(a * a0) • yᵀ) = (c * (-(a * a0))) • (y * yᵀ) := by
            simp only [neg_smul, Matrix.mul_neg, Matrix.mul_smul, smul_mul, mul_neg, neg_inj]
            match_scalars
            ring_nf
          have eq3 : (c^2) • (y * ((a * (1 - a0^2)) • (1 : Matrix (Fin 1) (Fin 1) α)) * yᵀ)
              = (a * (1 - a0 ^ 2) * c ^ 2) • (y * yᵀ) := by
            simp only [Matrix.mul_smul, Matrix.mul_one, smul_mul]
            match_scalars
            ring_nf
          rw [eq1, eq2, eq3]
      _ = z * P * zᵀ + a • ((- 2 * a0 * c + (1 - a0^2) * c^2) • (y * yᵀ)) := by
          rw [add_assoc, add_assoc, ← add_smul, ← add_smul]
          congr 1
          match_scalars
          ring_nf
      _ = z * P * zᵀ + a • (y * yᵀ) := by
          rw [hpoly0, one_smul]
    rw [h22, Matrix.mul_smul, this, Matrix.mul_one, smul_mul, add_comm]
  have det_eq : Matrix.det N = (Matrix.det S)^2 * Matrix.det P := by
    simpa [Matrix.det_mul, Matrix.det_transpose, pow_two,
         mul_comm, mul_left_comm, mul_assoc] using congrArg Matrix.det bottom
  have hS : Invertible S := by
    refine S.invertibleOfIsUnitDet ?_
    refine Ne.isUnit ?_
    have N_nezero_det : N.det ≠ 0 := by
      simpa [isUnit_iff_ne_zero] using Matrix.isUnit_det_of_invertible N
    have P_nezero_det : P.det ≠ 0 := by
      simpa [isUnit_iff_ne_zero] using Matrix.isUnit_det_of_invertible P
    have h := (det_eq ▸ N_nezero_det)
    have := (mul_ne_zero_iff.mp h).1
    exact ne_zero_pow (Nat.zero_ne_add_one 1).symm this
  exact { A := S, inv := hS, cong := bottom }

noncomputable def oplusLeftCancel [CharZero α] (d : m → α) (d_ne_zero : ∀ i, d i ≠ 0)
    (hN : Invertible N) (hP : Invertible P)
    (h : Matrix.diagonal d ⊕ₘ N ∼ₘ Matrix.diagonal d ⊕ₘ P) : N ∼ₘ P := by
  suffices H :
    ∀ k ≤ Fintype.card m,
      ∀ (g : Fin k → α) (g_ne_zero : ∀ i, g i ≠ 0),
        (Matrix.diagonal g : Matrix (Fin k) (Fin k) α) ⊕ₘ N
          ∼ₘ (Matrix.diagonal g) ⊕ₘ P → N ∼ₘ P by
    let k := Fintype.card m
    have hk : k ≤ Fintype.card m := le_rfl
    let e : m ≃ Fin k := Fintype.equivFinOfCardEq rfl
    let g : Fin k → α := fun i => d (e.symm i)
    have h' : (Matrix.diagonal g : Matrix (Fin k) (Fin k) α) ⊕ₘ N
           ∼ₘ (Matrix.diagonal g) ⊕ₘ P := by
      have := matCongrOplusReindexOfMatCongr e h
      simp only [reindexAlgEquiv_apply, reindex_apply, submatrix_diagonal_equiv] at this
      exact this
    exact H k hk g (by exact fun i => d_ne_zero (e.symm i)) h'
  intro k hk
  induction' k with k ih
  . intro g g_ne_zero h
    have : diagonal g = 0 := by
      ext i j
      apply Fin.elim0
      exact i
    rw [this] at h
    exact oplusLeftCancel_zero h
  . intro g g_ne_zero h
    let e : Fin (k.succ) ≃ Sum (Fin 1) (Fin k) :=
      { toFun := Fin.cases (Sum.inl 0) (fun j => Sum.inr j)
        invFun := fun
          | Sum.inl _ => 0
          | Sum.inr j => Fin.succ j
        left_inv := by
          intro i; refine Fin.cases (by simp) (fun _ => by simp) i
        right_inv := by
          intro s
          cases s with
          | inl _ => simp only [Fin.isValue, Fin.cases_zero, Sum.inl.injEq]
                     (expose_names; exact Eq.symm (Fin.fin_one_eq_zero val))
          | inr j => simp}
    have h₁ := matCongrOplusReindexOfMatCongr (m' := Sum (Fin 1) (Fin k)) e h
    simp only [reindexAlgEquiv_apply, reindex_apply, submatrix_diagonal_equiv] at h₁
    have h₂ :
        (( (g 0) • (1 : Matrix (Fin 1) (Fin 1) α)) ⊕ₘ
            (Matrix.diagonal (fun i : Fin k => g i.succ) ⊕ₘ N))
          ∼ₘ
        (( (g 0) • (1 : Matrix (Fin 1) (Fin 1) α)) ⊕ₘ
            (Matrix.diagonal (fun i : Fin k => g i.succ) ⊕ₘ P)) := by
      have : diagonal (g ∘ e.symm) =
          (diagonal (fun _ : Fin 1 => g 0)) ⊕ₘ (diagonal (fun i : Fin k => g i.succ)) := by
        simp only [matDirectSum, fromBlocks_diagonal]
        refine diagonal_eq_diagonal_iff.mpr ?_
        intro i
        cases i with
        | inl x =>
            fin_cases x
            simp only [Nat.succ_eq_add_one, Fin.zero_eta, Fin.isValue, Function.comp_apply,
              Sum.elim_inl]
            rfl
        | inr i =>
            simp only [Nat.succ_eq_add_one, Function.comp_apply, Sum.elim_inr]
            rfl
      simpa using
        (matCongrAssocOfMatCongr
          (M := (g 0) • (1 : Matrix (Fin 1) (Fin 1) α))
          (N := Matrix.diagonal (fun i : Fin k => g i.succ))
          (O := N)
          (M' := (g 0) • (1 : Matrix (Fin 1) (Fin 1) α))
          (N' := Matrix.diagonal (fun i : Fin k => g i.succ))
          (O' := P)
          (by
            rw [smul_one_eq_diagonal, ← this]
            exact h₁))
    have inv1 : Invertible (Matrix.diagonal (fun i : Fin k => g i.succ) ⊕ₘ N) := by
      have hdiag : det (diagonal (fun i : Fin k => g i.succ)) ≠ 0 := by
        simp only [det_diagonal]
        exact prod_ne_zero_iff.mpr fun a a_1 => g_ne_zero a.succ
      have hNne : det N ≠ 0 := by
        simpa [isUnit_iff_ne_zero] using Matrix.isUnit_det_of_invertible N
      have hdet : det ((diagonal (fun i : Fin k => g i.succ)) ⊕ₘ N)
                = det (diagonal (fun i : Fin k => g i.succ)) * det N := by
        simp only [matDirectSum, det_fromBlocks_zero₂₁, det_diagonal]
      refine ((diagonal fun i : Fin k => g i.succ) ⊕ₘ N).invertibleOfIsUnitDet ?_
      refine Ne.isUnit ?_
      simpa [hdet] using mul_ne_zero hdiag hNne
    have inv2 : Invertible (Matrix.diagonal (fun i : Fin k => g i.succ) ⊕ₘ P) := by
      have hdiag : det (diagonal (fun i : Fin k => g i.succ)) ≠ 0 := by
        simp only [det_diagonal]
        exact prod_ne_zero_iff.mpr fun a a_1 => g_ne_zero a.succ
      have hNne : det P ≠ 0 := by
        simpa [isUnit_iff_ne_zero] using Matrix.isUnit_det_of_invertible P
      have hdet :
          det ((diagonal (fun i : Fin k => g i.succ)) ⊕ₘ P)
            = det (diagonal (fun i : Fin k => g i.succ)) * det P := by
        simp only [matDirectSum, det_fromBlocks_zero₂₁, det_diagonal]
      refine ((diagonal fun i : Fin k => g i.succ) ⊕ₘ P).invertibleOfIsUnitDet ?_
      refine Ne.isUnit ?_
      simpa [hdet] using mul_ne_zero hdiag hNne
    have h₃ :
        (Matrix.diagonal (fun i : Fin k => g i.succ) ⊕ₘ N)
          ∼ₘ
        (Matrix.diagonal (fun i : Fin k => g i.succ) ⊕ₘ P) :=
      cancelLeft_1x1_any (a := g 0) inv1 inv2 h₂
    apply ih (Nat.le_of_succ_le hk) (fun i => g i.succ) (fun i => g_ne_zero i.succ) h₃

end MatCongr
