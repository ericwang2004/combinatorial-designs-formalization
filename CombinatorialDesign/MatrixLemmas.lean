import Mathlib.Data.Matrix.Rank
import Mathlib.Data.Finset.Basic
import Mathlib.NumberTheory.SumFourSquares
import Mathlib.LinearAlgebra.Matrix.Block

open Matrix Finset

def allOnes (m n α) [One α] : Matrix m n α :=
  of (fun _ _ ↦ 1)

def isZeroOne {m n} {α} [One α] [Zero α] (M : Matrix m n α) : Prop :=
  ∀ i j, M i j = 0 ∨ M i j = 1

/-- ### Matrix Determinant Lemma -/
theorem det_one_add_column_mul_row {α n} [CommRing α] [Fintype n] [DecidableEq n]
    (u : Matrix n (Fin 1) α) (v : Matrix (Fin 1) n α) : det (1 + u * v) = 1 + (v * u) 0 0 := by
  let A := fromBlocks (1 : Matrix n n α) 0 v (1 : Matrix (Fin 1) (Fin 1) α)
  let B := fromBlocks (1 + u * v) u 0 (1 : Matrix (Fin 1) (Fin 1) α)
  let C := fromBlocks (1 : Matrix n n α) 0 (-v) (1 : Matrix (Fin 1) (Fin 1) α)
  let D := fromBlocks (1 : Matrix n n α) u 0 (1 + v * u)
  have detA : det A = 1 := by
    simp only [A, det_fromBlocks_zero₁₂, det_one, mul_one]
  have detB : det B = det (1 + u * v) := by
    simp only [B, det_fromBlocks_zero₂₁, det_unique, one_apply_eq, mul_one]
  have detC : det C = 1 := by
    simp only [C, det_fromBlocks_zero₁₂, det_one, det_unique, one_apply_eq, mul_one]
  have detD : det D = 1 + (v * u) 0 0 := by
    simp only [det_fromBlocks_zero₂₁, det_one, det_unique, Fin.default_eq_zero, Fin.isValue,
      add_apply, one_apply_eq, one_mul, D]
  have hABCD : A * B * C = D := by
    simp only [A, B, C, D, fromBlocks_multiply, one_mul, Matrix.mul_zero, add_zero,
      mul_one, Matrix.one_mul, Matrix.mul_one, Matrix.mul_neg, add_neg_cancel_right,
      zero_add, fromBlocks_inj, true_and]
    constructor
    · rw [Matrix.mul_add, Matrix.mul_one, Matrix.add_mul, neg_add, Matrix.one_mul, add_comm v,
        add_assoc, add_comm _ (-v), ←add_assoc v, add_neg_cancel, zero_add, ←Matrix.mul_assoc,
        add_neg_cancel]
    · rw [add_comm]
  calc
    det (1 + u * v) = det A * det B * det C := by rw [detA, detB, detC, one_mul, mul_one]
    _ = det (A * B * C) := by simp only [det_mul]
    _ = det D := by rw [hABCD]
    _ = 1 + (v * u) 0 0 := by rw [detD]

theorem det_ones_add_diagonal {α} (n) [Field α] [Fintype n] [DecidableEq n] (a b : α) (hb : b ≠ 0) :
    det (a • allOnes n n α + b • 1) = b ^ Fintype.card n * (1 + a / b * Fintype.card n) := by
  let u := allOnes n (Fin 1) α
  let v := allOnes (Fin 1) n α
  have expr : a • allOnes n n α + b • 1 = b • (1 + ((a / b) • u) * v) := by
    ext
    simp only [add_apply, smul_apply, smul_eq_mul, smul_mul, one_apply, allOnes, of_apply,
      mul_apply, mul_one, mul_ite, mul_zero, univ_unique, Fin.default_eq_zero, Fin.isValue,
      sum_singleton, u, v]
    rw [mul_add, mul_ite, mul_one, mul_zero, add_comm, mul_div_cancel₀ _ hb]
  have v_mul_u : v * u = Fintype.card n • allOnes (Fin 1) (Fin 1) α := by
    ext
    simp only [mul_apply, allOnes, v, u, mul_one, sum_const, card_univ,
      nsmul_eq_mul, smul_apply, of_apply]
  have det_expr := (det_one_add_column_mul_row ((a / b) • u) v)
  simp only [smul_mul, Fin.isValue, Matrix.mul_smul, smul_apply, smul_eq_mul,
    v_mul_u, allOnes, smul_eq_mul, mul_one, of_apply, ] at det_expr
  simp only [nsmul_eq_mul, mul_one] at det_expr
  calc
    det (a • allOnes n n α + b • 1) = det (b • (1 + (a / b) • (u * v))) := by rw [expr, smul_mul, smul_add]
    _ = b ^ Fintype.card n * det (1 + (a / b) • (u * v)) := by rw [det_smul]
    _ = b ^ Fintype.card n * (1 + a / b * Fintype.card n) := by rw [det_expr]

theorem rank_ones_add_diagonal {α n} [Field α] [Fintype n] [DecidableEq n]
    (a b : α) (hb : b ≠ 0) (hab : 1 + a / b * Fintype.card n ≠ 0) :
    rank (a • allOnes n n α + b • 1) = Fintype.card n := by
  apply rank_of_isUnit
  rw [isUnit_iff_isUnit_det, det_ones_add_diagonal n a b hb, isUnit_iff_ne_zero]
  exact mul_ne_zero (pow_ne_zero _ hb) hab

theorem isUnit_of_full_rank {n α} [Fintype n] [DecidableEq n] [Field α]
    {A : Matrix n n α} (h : A.rank = Fintype.card n) : IsUnit A := by
  rw [←linearIndependent_rows_iff_isUnit, linearIndependent_iff_card_eq_finrank_span,
    ←h, rank_eq_finrank_span_row]
  rfl

theorem eq_of_full_rank_mul_eq {n m o α} [Fintype n] [Fintype m] [DecidableEq m] [Fintype o]
    [Field α] {A : Matrix n m α} {B₁ B₂ : Matrix m o α} (f : n ≃ m)
    (rankA : rank A = Fintype.card m) (h : A * B₁ = A * B₂) : B₁ = B₂ := by
  let A' := reindex f (Equiv.refl _) A
  have h' : A' * B₁ = A' * B₂ := by
    ext i' j
    rw [←Matrix.ext_iff] at h
    specialize h (f.symm i') j
    rwa [mul_apply] at h
  have rankA' : rank A' = Fintype.card m := by rw [←rankA]; apply rank_reindex
  obtain ⟨⟨_, A₁, _, hA₁⟩, rfl⟩ := isUnit_of_full_rank rankA'
  calc
    B₁ = A₁ * A' * B₁ := by rw [hA₁, Matrix.one_mul]
    _ = B₂ := by rw [Matrix.mul_assoc, h', ←Matrix.mul_assoc, hA₁, Matrix.one_mul]

structure MatCongr {m n α : Type*} [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m] [CommRing α]
    (M : Matrix m m α) (N : Matrix n n α) extends m ≃ n where
  A : Matrix n n α
  inv : Invertible A
  cong : (reindexAlgEquiv α α toEquiv) M = A * N * Aᵀ

infixl:25 " ∼ₘ " => MatCongr

namespace MatCongr

variable {m n o p α : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
  [Fintype o] [DecidableEq o] [Fintype p] [DecidableEq p] [Field α]
  {M : Matrix m m α} {N : Matrix n n α} {O : Matrix o o α} {P : Matrix p p α}

@[symm] protected def symm (c : M ∼ₘ N) : N ∼ₘ M :=
  have := c.inv
  {
    toEquiv := c.toEquiv.symm
    A := (reindexAlgEquiv α α c.toEquiv.symm) ⅟c.A
    inv := Invertible.map _ _
    cong := by calc
      _ = (reindexAlgEquiv α α c.toEquiv.symm) (⅟c.A * c.A * N * c.Aᵀ * ⅟c.Aᵀ) := by
        congr
        simp only [invOf_eq_nonsing_inv, inv_mul_of_invertible, one_mul,
          mul_inv_cancel_right_of_invertible]
      _ = (reindexAlgEquiv α α c.toEquiv.symm)
          (⅟c.A * ((reindexAlgEquiv α α c.toEquiv) M) * ⅟c.Aᵀ) := by
        rw [c.cong]; group
      _ = _ := by
        rw [reindexAlgEquiv_mul, reindexAlgEquiv_mul]; congr
        exact (AlgEquiv.eq_symm_apply (reindexAlgEquiv _ _ _)).mp rfl
  }

@[refl] protected def refl (M : Matrix n n α) : M ∼ₘ M where
  toEquiv := Equiv.refl n
  A := 1
  inv := invertibleOne
  cong := by rw [transpose_one, one_mul, mul_one]; rfl

@[trans] protected def trans (c₁ : M ∼ₘ N) (c₂ : N ∼ₘ O) : M ∼ₘ O :=
  have := c₁.inv; have := c₂.inv
  have := Invertible.map (reindexAlgEquiv α _ c₂.toEquiv) c₁.A
  {
    toEquiv := Equiv.trans c₁.toEquiv c₂.toEquiv
    A := (reindexAlgEquiv α α c₂.toEquiv) c₁.A * c₂.A
    inv := invertibleMul _ _
    cong := by
      calc
        _ = (reindexAlgEquiv α α (Equiv.trans c₁.toEquiv c₂.toEquiv))
            ((reindexAlgEquiv α α c₁.toEquiv.symm) (c₁.A * N * c₁.Aᵀ)) := by
          congr; rw [←c₁.cong, ←AlgEquiv.symm_apply_eq]; rfl
        _ = (reindexAlgEquiv α α c₂.toEquiv c₁.A) *
            (reindexAlgEquiv α α c₂.toEquiv N) *
            (reindexAlgEquiv α α c₂.toEquiv c₁.Aᵀ) := by
          repeat rw [reindexAlgEquiv_mul]; congr 2
          all_goals
          ext
          simp only [reindexAlgEquiv_apply, reindex_apply, Equiv.symm_symm,
            submatrix_apply, Equiv.symm_trans_apply, Equiv.apply_symm_apply]
        _ = (reindexAlgEquiv α α c₂.toEquiv c₁.A) *
            (c₂.A * O * c₂.Aᵀ) *
            (reindexAlgEquiv α α c₂.toEquiv c₁.Aᵀ) := by rw [←c₂.cong]
        _ = _ := by
          rw [transpose_mul]; group; congr
  }

instance : Trans (MatCongr (m := m) (n := n) (α := α))
    (MatCongr (n := o)) MatCongr where
  trans := by intro; exact MatCongr.trans

def matCongrOfReindex (e : m ≃ n) (h : reindex e e M = N) : M ∼ₘ N where
  toEquiv := e
  A := 1
  inv := invertibleOne
  cong := by rw [one_mul, transpose_one, mul_one, ←h]; rfl

def matDirectSum {l m n o} (A : Matrix l m α) (B : Matrix n o α) := fromBlocks A 0 0 B

infixl:30 " ⊕ₘ " => matDirectSum

def oplus_assoc : M ⊕ₘ N ⊕ₘ O ∼ₘ M ⊕ₘ (N ⊕ₘ O) :=
  matCongrOfReindex (Equiv.sumAssoc _ _ _) (by aesop)

theorem det_oplus : det (M ⊕ₘ N) = det M * det N := by
  simp [matDirectSum]

omit [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n] in
theorem oplus_symmetric (h₁ : M = Mᵀ) (h₂ : N = Nᵀ) : (M ⊕ₘ N) = (M ⊕ₘ N)ᵀ := by
  ext i j
  have h₁' := Matrix.ext_iff.mpr h₁
  have h₂' := Matrix.ext_iff.mpr h₂
  simp only [matDirectSum, transpose_apply] at h₁' h₂' ⊢
  match i with
  | Sum.inl i =>
    match j with
    | Sum.inl j => simp only [fromBlocks_apply₁₁, h₁']
    | Sum.inr j => simp only [fromBlocks_apply₁₂, zero_apply, fromBlocks_apply₂₁]
  | Sum.inr i =>
    match j with
    | Sum.inl j => simp only [fromBlocks_apply₂₁, zero_apply, fromBlocks_apply₁₂]
    | Sum.inr j => simp only [fromBlocks_apply₂₂, h₂']

def smul_oplus_congr {a : α} (h : M ∼ₘ N) : a • M ∼ₘ a • N where
  toEquiv := h.toEquiv
  A := h.A
  inv := h.inv
  cong := by rw [Matrix.mul_smul, Matrix.smul_mul, ←h.cong]; rfl

def smul_oplus {a : α} : (a • M) ⊕ₘ (a • N) ∼ₘ a • (M ⊕ₘ N) where
  toEquiv := Equiv.refl _
  A := 1
  inv := invertibleOne
  cong := by
    simp only [reindexAlgEquiv_refl, matDirectSum, AlgEquiv.coe_refl,
      id_eq, Algebra.mul_smul_comm, one_mul, transpose_one, mul_one]
    aesop

def oplus_congr (h₁ : M ∼ₘ N) (h₂ : O ∼ₘ P) : (M ⊕ₘ O) ∼ₘ (N ⊕ₘ P) := by sorry

def oplus_one (h : m ⊕ n ≃ o) :
    (1 : Matrix m m α) ⊕ₘ (1 : Matrix n n α) ∼ₘ (1 : Matrix o o α) where
  toEquiv := h
  A := 1
  inv := invertibleOne
  cong := by simp [matDirectSum]

noncomputable def matCongrOneOfFourDiv [CharZero α] (hn : 4 ∣ Fintype.card n)
    (m : ℤ) (mpos : m > 0) : (m : α) • (1 : Matrix n n α) ∼ₘ (1 : Matrix n n α) := by
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
    exact (m : α)⁻¹ • Aᵀ
    simp only [Algebra.mul_smul_comm, HA, A, A']
    refine inv_smul_smul₀ ?_ 1
    refine Int.cast_ne_zero.mpr  (Ne.symm (Int.ne_of_lt mpos))
  exact {
    toEquiv := Equiv.refl n
    A := A
    inv := A_is_invertible
    cong := by
      simp only [reindexAlgEquiv_refl, zsmul_eq_mul, mul_one, map_intCast, HA, A', A,
        Int.cast_smul_eq_zsmul, zsmul_eq_mul, mul_one]
      }

/-- ## Witt cancellation lemma
 - from BW Jones: `The Arithmetic Theory Of Quadratic Forms`, chapter 1
-/
def oplus_left_cancel [CharZero α] {A B : Matrix n n α} {C : Matrix m m α}
    (hA : A = Aᵀ) (hB : B = Bᵀ) (hC : C = Cᵀ) (h : C ⊕ₘ A ∼ₘ C ⊕ₘ B) : A ∼ₘ B :=
  sorry

end MatCongr
