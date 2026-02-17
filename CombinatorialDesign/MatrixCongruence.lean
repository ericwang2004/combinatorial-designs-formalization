import CombinatorialDesign.WittCancellation
import Mathlib.Data.Finset.Basic
import Mathlib.NumberTheory.SumFourSquares
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.LinearAlgebra.Matrix.BilinearForm

/-!

# Matrix congruence

This file develops the quadratic form theory that we need to
prove the Bruck-Ryser-Chowla theorem. (The BRC theorem itself
is not stated in this file.)

## Main definitions and theorems:
  * MatCongr -- matrix congruence
  * matDirectSum -- direct sum of matrices
  * matCongrOneOfFourDiv -- if n is a multiple of 4, then
    I ∼ mI for any positive integer m, where I is the n × n
    identity matrix
  * oplusLeftCancel -- Witt's cancellation lemma

Note that the lemmas needed for the Witt cancellation lemma,
which is a big result, are separately given in the file
`WittCancellation.lean`.

-/

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
  inv := have := h.inv; Invertible.map _ _
  cong := by
    have : ((Rat.castHom α).mapMatrix h.A)ᵀ = (Rat.castHom α).mapMatrix h.Aᵀ := rfl
    rw [this, ←RingHom.map_mul, ←RingHom.map_mul, ←h.cong]

theorem ratCast_one (α : Type*) [Field α] [CharZero α] :
    RingHom.mapMatrix (Rat.castHom α) (1 : Matrix m m ℚ) = 1 :=
  RingHom.map_one _

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

omit [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m] in
theorem isSymm_oplus {M : Matrix m m α} {N : Matrix n n α}
    (hM : M.IsSymm) (hN : N.IsSymm) : (M ⊕ₘ N).IsSymm :=
  IsSymm.fromBlocks hM transpose_zero hN

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
    haveI := h.inv
    haveI : Invertible (1 :Matrix m m α) := invertibleOne
    rw [matDirectSum]
    exact Matrix.fromBlocksZero₁₂Invertible h.A 0 1
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
      <;> simp [Matrix.mul_apply, Fin.sum_univ_four, A', ← pow_two, ← hsum]
      <;> ring
    . fin_cases i
      <;> fin_cases j
      <;> first
        | cases hij rfl
        | simp [ Matrix.mul_apply, Fin.sum_univ_four, A']; ring
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
      simp only [↓reduceIte, one_apply_eq, mul_one]
    . simp only [one_apply_ne p]
      have h_ne : (e i ≠ e j) := by
        simp [ne_eq, EmbeddingLike.apply_eq_iff_eq, p]
      simp only [h_ne, ↓reduceIte, mul_zero]
  have A_is_invertible : Invertible A := by
    refine invertibleOfRightInverse A ?_ ?_
    · exact (m : α)⁻¹ • Aᵀ
    simp only [Algebra.mul_smul_comm, HA]
    refine inv_smul_smul₀ ?_ 1
    refine Int.cast_ne_zero.mpr  (Ne.symm (Int.ne_of_lt mpos))
  exact {
    A := A
    inv := A_is_invertible
    cong := by simp only [HA, A', A, Int.cast_smul_eq_zsmul, zsmul_eq_mul, mul_one]
      }

def MatCongr_toIsometryEquiv
    {M N : Matrix m m α}
    (h : M ∼ₘ N) :
    M.toQuadraticMap'.IsometryEquiv N.toQuadraticMap' := by
  haveI := h.inv
  haveI : Invertible h.Aᵀ := h.A.invertibleTranspose
  let f : (m → α) ≃ₗ[α] (m → α) := {
    toFun := fun x => h.Aᵀ *ᵥ x
    map_add' := fun x y => mulVec_add h.Aᵀ x y
    map_smul' := fun c x => by simp [mulVec_smul]
    invFun := fun x => ⅟(h.Aᵀ) *ᵥ x
    left_inv := fun x => by
      simp only [mulVec_mulVec]
      rw [invOf_mul_self]; simp
    right_inv := fun x => by
      simp only [mulVec_mulVec]
      rw [mul_invOf_self]; simp  }
  refine ⟨f, ?_⟩
  intro x
  simp only [Matrix.toQuadraticMap', LinearMap.BilinMap.toQuadraticMap_apply,
    Matrix.toLinearMap₂'_apply']
  show (h.Aᵀ *ᵥ x) ⬝ᵥ N *ᵥ (h.Aᵀ *ᵥ x) = x ⬝ᵥ M *ᵥ x
  conv_lhs => arg 1; rw [mulVec_transpose]
  rw [dotProduct_mulVec, vecMul_vecMul, ← dotProduct_mulVec]
  simp only [mulVec_mulVec, ← h.cong]

theorem toQuadraticMap_two_by_two {a b : α} (x : Fin 1 ⊕ Fin 1 → α):
    let M := a • (1 : Matrix (Fin 1) (Fin 1) α) ⊕ₘ b • (1 : Matrix (Fin 1) (Fin 1) α)
    M.toQuadraticMap' x = a * (x (Sum.inl 0))^2 + b * (x (Sum.inr 0))^2 := by
  simp only [Matrix.toQuadraticMap', LinearMap.BilinMap.toQuadraticMap_apply,
    Matrix.toLinearMap₂'_apply']
  simp only [matDirectSum, fromBlocks, of_apply, dotProduct, mulVec, Fintype.sum_sum_type,
    Finset.univ_unique, Finset.sum_singleton]
  simp only [Sum.elim_inl, Sum.elim_inr, smul_apply, one_apply_eq, zero_apply,
    zero_mul, add_zero, zero_add]
  simp only [smul_eq_mul, Fin.default_eq_zero]
  ring

theorem range_of_two_by_two (a b : α) :
    Set.range (a • 1 ⊕ₘ b • 1 : Matrix (Fin 1 ⊕ Fin 1) _ _).toQuadraticMap' =
    {z | ∃ x₁ x₂, z = a * x₁^2 + b * x₂^2} := by
  ext z
  constructor
  · rintro ⟨x, rfl⟩
    use x (Sum.inl 0), x (Sum.inr 0)
    rw [toQuadraticMap_two_by_two]
  · rintro ⟨x₁, x₂, rfl⟩
    use Sum.elim (fun _ ↦ x₁) (fun _ ↦ x₂)
    rw [toQuadraticMap_two_by_two]
    simp [Sum.elim_inl, Sum.elim_inr]

theorem matCongr_two_by_two_condition {a b c d : α}
    (h : a • (1 : Matrix (Fin 1) (Fin 1) α) ⊕ₘ
    b • (1 : Matrix (Fin 1) (Fin 1) α) ∼ₘ
    c • (1 : Matrix (Fin 1) (Fin 1) α) ⊕ₘ d • (1 : Matrix (Fin 1) (Fin 1) α)) :
    ∀ w x, ∃ y z, a * y^2 + b * z^2 = c * w^2 + d * x^2 := by
  have e := MatCongr_toIsometryEquiv h
  have hrng :
      Set.range (a • 1 ⊕ₘ b • 1 : Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) α).toQuadraticMap' =
      Set.range (c • 1 ⊕ₘ d • 1 : Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) α).toQuadraticMap' := by
    ext v; constructor
    · rintro ⟨x, rfl⟩; exact ⟨e x, e.map_app x⟩
    · rintro ⟨x, rfl⟩; exact ⟨e.symm x, by simp⟩
  rw [range_of_two_by_two, range_of_two_by_two] at hrng
  intro w x
  obtain ⟨_, _, h⟩ := hrng.symm.subset (by use w, x)
  exact ⟨_, _, h.symm⟩

theorem matrix_ext_of_isSymm {n : Type*} [Fintype n] [DecidableEq n]
    {R : Type*} [Field R] [Invertible (2 : R)]
    {A B : Matrix n n R}
    (hA : A.IsSymm) (hB : B.IsSymm)
    (h : ∀ x : n → R, x ⬝ᵥ A *ᵥ x = x ⬝ᵥ B *ᵥ x) :
    A = B := by
  apply Matrix.toBilin'.injective
  apply LinearMap.BilinForm.ext_of_isSymm
  · rw [@LinearMap.BilinForm.isSymm_def]
    intro x y
    simp only [Matrix.toBilin'_apply]
    calc ∑ i, ∑ j, x i * A i j * y j
        = ∑ i, ∑ j, x i * A j i * y j := by
          congr 1; ext i; congr 1; ext j; rw [hA.apply i j]
      _ = ∑ j, ∑ i, y j * A j i * x i := by
          rw [Finset.sum_comm]; congr 1; ext j; congr 1; ext i; ring
  · rw [@LinearMap.BilinForm.isSymm_def]
    intro x y
    simp only [Matrix.toBilin'_apply]
    calc ∑ i, ∑ j, x i * B i j * y j
        = ∑ i, ∑ j, x i * B j i * y j := by
          congr 1; ext i; congr 1; ext j; rw [hB.apply i j]
      _ = ∑ j, ∑ i, y j * B j i * x i := by
          rw [Finset.sum_comm]; congr 1; ext j; congr 1; ext i; ring
  · intro x
    simp only [Matrix.toBilin'_apply']
    exact h x

def IsometryEquiv_toMatCongr [Invertible (2 : α)]
    {M N : Matrix m m α} (hM : M.IsSymm) (hN : N.IsSymm)
    (e : M.toQuadraticMap'.IsometryEquiv N.toQuadraticMap') :
    M ∼ₘ N := by
  let A := LinearMap.toMatrix' e.toLinearEquiv.toLinearMap
  let A_inv := LinearMap.toMatrix' e.toLinearEquiv.symm.toLinearMap
  have hAA_inv : A * A_inv = 1 := by
    rw [(LinearMap.toMatrix'_comp _ _).symm]
    simp_all only [LinearEquiv.comp_coe, LinearEquiv.symm_trans_self,
          LinearEquiv.refl_toLinearMap, LinearMap.toMatrix'_id]
  haveI : Invertible A := invertibleOfRightInverse A A_inv hAA_inv
  have h_iso : ∀ x, N.toQuadraticMap' (e.toLinearEquiv x) = M.toQuadraticMap' x := e.map_app
  have h_matrix_action : ∀ x, e.toLinearEquiv x = A *ᵥ x := by
    intro x
    rw [←Matrix.toLin'_apply, Matrix.toLin'_toMatrix']
    rfl
  have h_eq : Aᵀ * N * A - M = 0 := by
    have h_symm : (Aᵀ * N * A - M).IsSymm := by
      show (Aᵀ * N * A - M)ᵀ = Aᵀ * N * A - M
      rw [transpose_sub, transpose_mul, transpose_mul, transpose_transpose, hN, hM,
        ← mul_assoc]
    have h_quad : ∀ x, x ⬝ᵥ (Aᵀ * N * A - M) *ᵥ x = 0 := by
      intro x
      have h1 := h_iso x
      simp only [Matrix.toQuadraticMap', LinearMap.BilinMap.toQuadraticMap_apply,
        Matrix.toLinearMap₂'_apply'] at h1
      rw [h_matrix_action] at h1
      conv_lhs at h1 => arg 1; rw [show A *ᵥ x = x ᵥ* Aᵀ from by
        rw [← mulVec_transpose, transpose_transpose]]
      rw [dotProduct_mulVec, vecMul_vecMul, ← dotProduct_mulVec, mulVec_mulVec] at h1
      rw [sub_mulVec, dotProduct_sub, sub_eq_zero]
      exact h1
    refine matrix_ext_of_isSymm h_symm rfl ?_
    simp only [h_quad, zero_mulVec, dotProduct_zero, implies_true]
  exact ⟨Aᵀ, invertibleTranspose A, by rw [transpose_transpose, sub_eq_zero.mp h_eq]⟩

noncomputable def isometryEquiv_oplus_prod
    {m' n' : Type*} [Fintype m'] [DecidableEq m'] [Fintype n'] [DecidableEq n']
    (M : Matrix m' m' α) (N : Matrix n' n' α) :
    (M ⊕ₘ N).toQuadraticMap'.IsometryEquiv
      (M.toQuadraticMap'.prod N.toQuadraticMap') where
  toLinearEquiv := LinearEquiv.sumArrowLequivProdArrow m' n' α α
  map_app' x := by
    simp only [Matrix.toQuadraticMap', LinearMap.BilinMap.toQuadraticMap_apply,
      Matrix.toLinearMap₂'_apply', QuadraticMap.prod_apply, matDirectSum, fromBlocks,
      mulVec, dotProduct, of_apply, Fintype.sum_sum_type, LinearEquiv.sumArrowLequivProdArrow,
      Equiv.sumArrowEquivProdArrow, Function.comp, Sum.elim_inl, Sum.elim_inr, zero_apply,
      zero_mul, Finset.sum_const_zero, add_zero, zero_add]

noncomputable def oplusLeftCancel [Invertible (2 : α)]
    (hN : IsSymm N) (hP : IsSymm P)
    (h : M ⊕ₘ N ∼ₘ M ⊕ₘ P) : N ∼ₘ P := by
  have h_iso : (M ⊕ₘ N).toQuadraticMap'.IsometryEquiv (M ⊕ₘ P).toQuadraticMap' :=
    MatCongr_toIsometryEquiv h
  let eN := isometryEquiv_oplus_prod M N
  let eP := isometryEquiv_oplus_prod M P
  have h_prod : (M.toQuadraticMap'.prod N.toQuadraticMap').IsometryEquiv
      (M.toQuadraticMap'.prod P.toQuadraticMap') :=
    eN.symm.trans (h_iso.trans eP)
  have h_cancel : N.toQuadraticMap'.IsometryEquiv P.toQuadraticMap' :=
    QuadraticForm.witt_cancellation M.toQuadraticMap' N.toQuadraticMap' P.toQuadraticMap' h_prod
  exact IsometryEquiv_toMatCongr hN hP h_cancel

end MatCongr
