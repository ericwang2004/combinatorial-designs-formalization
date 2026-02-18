import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.LinearAlgebra.Matrix.IsDiag
import CombinatorialDesign.MatrixCongruence

/-!
# Diagonalizability of Bilinear Forms and Matrices

This file proves that a bilinear form over a field of characteristic ≠ 2 is diagonalizable
if and only if it is symmetric, and develops the corresponding matrix theory.

## Main Definitions

* `IsDiagonalWrt B b` - A bilinear form B is diagonal with respect to a basis b
* `IsDiagonalizable B` - A bilinear form B admits some basis making it diagonal
* `Matrix.IsDiagonalizable' M` - A matrix is diagonalizable via congruence
* `Matrix.DiagonalForm M hM` - The diagonal form of a symmetric matrix under congruence

## Main Results

* `diagonalizable_iff_isSymm` - A bilinear form is diagonalizable iff it is symmetric
* `Matrix.isDiagonalizable'_iff_isSymm` - A matrix is congruence-diagonalizable iff symmetric
* `nondegenerate_iff_diag_ne_zero` - A diagonal form is nondegenerate iff all diagonal entries are nonzero
* `Matrix.invertible_iff_diagEntries_ne_zero` - A symmetric matrix is invertible iff its diagonal form has no zero entries
* `symm_matCongr_diagonalForm` - Every symmetric matrix is congruent to its diagonal form
-/

open LinearMap (BilinForm)
open Submodule FiniteDimensional BilinForm Module Matrix

variable {F : Type*} [Field F] [NeZero (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
variable {ι : Type*} [DecidableEq ι] [Fintype ι]

/-- A bilinear form is diagonal with respect to a basis if off-diagonal entries vanish -/
def IsDiagonalWrt  (B : BilinForm F V) (b : Basis ι F V) : Prop :=
  ∀ i j, i ≠ j → B (b i) (b j) = 0

/-- A bilinear form is diagonalizable if there exists a basis making it diagonal -/
def IsDiagonalizable (B : BilinForm F V) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι) (b : Basis ι F V), IsDiagonalWrt B b

omit [FiniteDimensional F V] [NeZero (2 : F)] in
/-- A diagonalizable bilinear form is symmetric -/
theorem IsDiagonalizable.isSymm (B : BilinForm F V) (hdiag : IsDiagonalizable B) :
    B.IsSymm := by
  obtain ⟨ι, _, b, hd⟩ := hdiag
  rw [BilinForm.isSymm_iff_basis b]
  intro i j
  by_cases hij : i = j
  · simp only [hij]
  · push_neg at hij
    rw [hd i j hij, hd j i hij.symm ]

omit [NeZero (2 : F)] in
/-- If v ≠ 0 and B(v,v) ≠ 0, then dim(v⊥) < dim(V) -/
theorem finrank_orthogonal_lt
    (B : BilinForm F V)
    (v : V) (hv0 : v ≠ 0) (hv : B v v ≠ 0) :
    finrank F (B.orthogonal (span F {v})) < finrank F V := by
  have hcompl := BilinForm.isCompl_span_singleton_orthogonal hv
  have hsum := Submodule.finrank_sup_add_finrank_inf_eq
                 (span F ({v} : Set V)) (B.orthogonal (span F {v}))
  rw [hcompl.sup_eq_top, hcompl.inf_eq_bot] at hsum
  simp only [finrank_top, finrank_bot] at hsum
  have h1 : finrank F (span F ({v} : Set V)) = 1 := finrank_span_singleton hv0
  omega

/-- A symmetric bilinear form is diagonalizable (over a field of characteristic ≠ 2) -/
theorem IsSymm.isDiagonalizable (B : BilinForm F V) (hsymm : B.IsSymm) :
    IsDiagonalizable B := by
  induction hn : finrank F V using Nat.strongRecOn generalizing V with
  | ind n ih =>
  by_cases hB : B = 0
  · subst hB
    refine ⟨_, inferInstance, finBasisOfFinrankEq F V hn, fun _ _ _ => ?_⟩
    simp [LinearMap.zero_apply]
  · have nonzeroB : ∃ v : V, B v v ≠ 0 := by
      by_contra h
      push_neg at h
      apply hB
      apply BilinForm.ext_of_isSymm hsymm BilinForm.isSymm_zero
      simp only [h, LinearMap.zero_apply, implies_true]
    obtain ⟨v, hv⟩ := nonzeroB
    have hv0 : v ≠ 0 := fun h => by simp [h] at hv
    set W := B.orthogonal (span F {v}) with hW_def
    have hcompl := BilinForm.isCompl_span_singleton_orthogonal hv
    have hdim : finrank F W < n := hn ▸ finrank_orthogonal_lt B v hv0 hv
    have hsymm_W : (B.restrict W).IsSymm := hsymm.restrict W
    obtain ⟨κ, hκ, bW, hdiagW⟩ := ih (finrank F W) hdim (B.restrict W) hsymm_W rfl
    have hfr1 : finrank F (span F ({v} : Set V)) = 1 := finrank_span_singleton hv0
    let bv : Basis (Fin 1) F (span F ({v} : Set V)) := finBasisOfFinrankEq F _ hfr1
    let bV : Basis (Fin 1 ⊕ κ) F V :=
      (bv.prod bW).map (Submodule.prodEquivOfIsCompl _ _ hcompl)
    refine ⟨Fin 1 ⊕ κ, inferInstance, bV, ?_⟩
    intro i j hij
    simp only [bV, Basis.map_apply, Submodule.coe_prodEquivOfIsCompl']
    cases i with
    | inl i =>
      cases j with
      | inl j =>
        exact absurd (congrArg Sum.inl (Subsingleton.elim i j)) hij
      | inr k =>
        simp only [Basis.prod_apply, LinearMap.coe_inl, LinearMap.coe_inr, Sum.elim_inl,
          Function.comp_apply, ZeroMemClass.coe_zero, add_zero, Sum.elim_inr, zero_add]
        have hmem_W : (bW k : V) ∈ B.orthogonal (span F {v}) := (bW k).2
        rw [BilinForm.mem_orthogonal_iff] at hmem_W
        exact hmem_W _ (bv i).2
    | inr k =>
      cases j with
      | inl j =>
        simp only [Basis.prod_apply, LinearMap.coe_inl, LinearMap.coe_inr, Sum.elim_inr,
          Function.comp_apply, ZeroMemClass.coe_zero, zero_add, Sum.elim_inl, add_zero]
        have hmem_W : (bW k : V) ∈ B.orthogonal (span F {v}) := (bW k).2
        rw [BilinForm.mem_orthogonal_iff] at hmem_W
        rw [hsymm.eq]
        exact hmem_W _ (bv j).2
      | inr k' =>
        simp only [Basis.prod_apply, LinearMap.coe_inl, LinearMap.coe_inr, Sum.elim_inr,
          Function.comp_apply, ZeroMemClass.coe_zero, zero_add]
        have hne : k ≠ k' := fun h => hij (congrArg Sum.inr h)
        have := hdiagW k k' hne
        rwa [BilinForm.restrict_apply] at this

/-- A bilinear form is diagonalizable if and only if it is symmetric -/
theorem diagonalizable_iff_isSymm (B : BilinForm F V) :
    IsDiagonalizable B ↔ B.IsSymm :=
  ⟨IsDiagonalizable.isSymm B, IsSymm.isDiagonalizable B⟩

/-! ## Matrix Diagonalizability

We transfer the bilinear form results to matrices, showing that a matrix is
diagonalizable if and only if it is symmetric.
-/

/-- A matrix is diagonalizable if its associated bilinear form is -/
def Matrix.IsDiagonalizable' {n : Type*} [Fintype n] [DecidableEq n]
    (M : Matrix n n F) : Prop :=
  IsDiagonalizable (Matrix.toBilin' M)

variable {n : Type*} [Fintype n] [DecidableEq n]

omit [NeZero (2 : F)] in
/-- The bilinear form of a matrix is symmetric iff the matrix is symmetric -/
theorem Matrix.toBilin'_isSymm_iff (M : Matrix n n F) :
    (Matrix.toBilin' M).IsSymm ↔ M.IsSymm := by
  rw [BilinForm.isSymm_iff_basis (Pi.basisFun F n)]
  simp only [Pi.basisFun_apply, Matrix.toBilin'_single]
  constructor
  · intro h
    ext i j
    exact (h i j).symm
  · intro h i j
    exact h.apply j i

/-- A matrix is diagonalizable if and only if it is symmetric -/
theorem Matrix.isDiagonalizable'_iff_isSymm (M : Matrix n n F) :
    M.IsDiagonalizable' ↔ M.IsSymm := by
  rw [Matrix.IsDiagonalizable', diagonalizable_iff_isSymm, Matrix.toBilin'_isSymm_iff]

/-- A basis that diagonalizes a symmetric matrix, reindexed to match the original type -/
noncomputable def Matrix.symmDiagBasis (M : Matrix n n F) (hM : M.IsSymm) :
    Basis n F (n → F) := by
  have h := (Matrix.isDiagonalizable'_iff_isSymm M).mpr hM
  set ι := h.choose
  letI : Fintype ι := h.choose_spec.choose
  set b : Basis ι F (n → F) := h.choose_spec.choose_spec.choose
  exact b.reindex (Fintype.equivOfCardEq
    ((finrank_eq_card_basis b).symm.trans (finrank_eq_card_basis (Pi.basisFun F n))))

/-- The diagonalizing basis for a symmetric matrix is indeed diagonal with respect to it -/
theorem Matrix.symmDiagBasis_isDiagonalWrt (M : Matrix n n F) (hM : M.IsSymm) :
    IsDiagonalWrt (Matrix.toBilin' M) (Matrix.symmDiagBasis M hM) := by
  intro i j hij
  simp only [Matrix.symmDiagBasis, Basis.reindex_apply]
  have h := (Matrix.isDiagonalizable'_iff_isSymm M).mpr hM
  exact h.choose_spec.choose_spec.choose_spec _ _
    (fun heq => hij (Equiv.injective _ heq))

/-- The diagonal form of a symmetric matrix: the diagonal matrix congruent to M -/
noncomputable def Matrix.DiagonalForm (M : Matrix n n F) (hM : M.IsSymm) :
    Matrix n n F :=
  let b := Matrix.symmDiagBasis M hM
  diagonal (fun i => Matrix.toBilin' M (b i) (b i))

/-- The diagonal form of a symmetric matrix is indeed a diagonal matrix -/
theorem Matrix.DiagonalForm_isDiag (M : Matrix n n F) (hM : M.IsSymm) :
    (Matrix.DiagonalForm M hM).IsDiag := by
  intro i j hij
  simp only [Matrix.DiagonalForm, diagonal_apply, if_neg hij]

/-! ## Nondegeneracy and Invertibility

We characterize nondegeneracy of a diagonal bilinear form and invertibility of a symmetric
matrix in terms of their diagonal entries.
-/

omit [NeZero (2 : F)] [FiniteDimensional F V] in
/-- A diagonal bilinear form is nondegenerate iff all diagonal entries are nonzero -/
theorem nondegenerate_iff_diag_ne_zero
    {B : BilinForm F V} {b : Basis ι F V}
    (hdiag : IsDiagonalWrt B b) :
    B.Nondegenerate ↔ ∀ i, B (b i) (b i) ≠ 0 := by
  constructor
  · intro hnd i hi
    exact b.ne_zero i (hnd (b i) (fun v => by
      rw [show v = ∑ j, (b.repr v) j • b j from (b.sum_repr v).symm]
      simp only [map_sum, BilinForm.smul_right]
      exact Finset.sum_eq_zero fun j _ => by
        by_cases hij : i = j
        · subst hij; simp [hi]
        · simp [hdiag i j hij]))
  · intro hd v hv
    by_contra hne
    have hexists : ∃ i, b.repr v i ≠ 0 := by
      by_contra hall; push_neg at hall
      exact hne (by
        have hzero : b.repr v = 0 := by
          ext i; exact hall i
        rw [show v = b.repr.symm (b.repr v) from (b.repr.symm_apply_apply v).symm,
          hzero, map_zero])
    obtain ⟨i, hi⟩ := hexists
    have hbi : B v (b i) = 0 := hv (b i)
    have hv_expand : v = ∑ j, (b.repr v) j • b j := (b.sum_repr v).symm
    rw [hv_expand] at hbi
    simp only [map_sum, LinearMap.sum_apply, BilinForm.smul_left] at hbi
    have hterm : ∀ j, j ≠ i → (b.repr v) j * B (b j) (b i) = 0 := fun j hji => by
      rw [hdiag j i hji, mul_zero]
    rw [Finset.sum_eq_single i
      (fun j _ hji => hterm j hji)
      (fun h => absurd (Finset.mem_univ i) h)] at hbi
    exact hd i (mul_eq_zero.mp hbi |>.resolve_left hi)

/-- A symmetric matrix is invertible iff its diagonal form has all nonzero diagonal entries -/
theorem Matrix.invertible_iff_diagEntries_ne_zero (M : Matrix n n F) (hM : M.IsSymm) :
    Nonempty (Invertible M) ↔ ∀ i, (Matrix.DiagonalForm M hM) i i ≠ 0 := by
  simp only [Matrix.DiagonalForm, diagonal_apply_eq]
  set B := Matrix.toBilin' M
  set b := Matrix.symmDiagBasis M hM
  have hsymm : B.IsSymm := (Matrix.toBilin'_isSymm_iff M).mpr hM
  have hdiag := Matrix.symmDiagBasis_isDiagonalWrt M hM
  rw [show Nonempty (Invertible M) ↔ B.Nondegenerate from by
    rw [nonempty_invertible_iff_isUnit, Matrix.isUnit_iff_isUnit_det,
      isUnit_iff_ne_zero, ← Matrix.nondegenerate_iff_det_ne_zero,
      Matrix.nondegenerate_toBilin'_iff]]
  exact nondegenerate_iff_diag_ne_zero hdiag

/-! ## Congruence to Diagonal Form -/

open MatCongr

/-- Every symmetric matrix is congruent to its diagonal form -/
noncomputable def symm_matCongr_diagonalForm
    (M : Matrix n n F) (hM : M.IsSymm) :
    M ∼ₘ Matrix.DiagonalForm M hM := by
  set B := Matrix.toBilin' M
  set b := Matrix.symmDiagBasis M hM
  set e := Pi.basisFun F n
  set P := e.toMatrix b
  have hP_inv : Invertible P := e.invertibleToMatrix b
  have h_eM : LinearMap.BilinForm.toMatrix e B = M := by
    change (LinearMap.BilinForm.toMatrix (Pi.basisFun F n)) B = M
    rw [LinearMap.BilinForm.toMatrix_basisFun]
    exact LinearMap.BilinForm.toMatrix'_toBilin' M
  have h_basis : (Pᵀ * M * P) = LinearMap.BilinForm.toMatrix b B := by
    rw [← h_eM]
    exact LinearMap.BilinForm.toMatrix_mul_basis_toMatrix e b B
  have h_diag : LinearMap.BilinForm.toMatrix b B = Matrix.DiagonalForm M hM := by
    ext i j
    rw [LinearMap.BilinForm.toMatrix_apply]
    simp only [Matrix.DiagonalForm, diagonal_apply]
    split
    · next h => subst h; rfl
    · next hij =>
      exact Matrix.symmDiagBasis_isDiagonalWrt M hM i j hij
  have key : Pᵀ * M * P = Matrix.DiagonalForm M hM := by
    rw [h_basis, h_diag]
  set D := Matrix.DiagonalForm M hM
  have cong_rev : D ∼ₘ M := by
    refine ⟨Pᵀ, ?_, ?_⟩
    · exact invertibleTranspose P
    · rw [transpose_transpose]; exact key.symm
  exact cong_rev.symm
