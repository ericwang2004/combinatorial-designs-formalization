import CombinatorialDesign.Basic
import CombinatorialDesign.MatrixLemmas

/-!

# Incidence matrices

This file defines the incidence matrix of a design.
Given a design Φ = (X, A), the incidence matrix of Φ
is a #X × #A matrix M where Mij = 1 if xᵢ ∈ Aⱼ and
Mij = 0 otherwise.

Conversely, any matrix gives rise to a design in the
obvious way.

We prove basic theorems about the correspondence between
algebraic properties of incidence matrices and combinatorial
properties of designs.

-/

open CombinatorialDesign Matrix Finset Fintype
namespace CombinatorialDesign

variable {ι X m n : Type*} [Fintype X] [Fintype ι] [DecidableEq X] [DecidableEq ι] [Fintype m] [Fintype n] {k l : ℕ}
  (Φ : BIBD ι X k l)

/-- Convert a design to an incidence matrix -/
def toIncMat (α : Type*) [One α] [Zero α] (Φ : Design ι X) :
    Matrix X ι α :=
  of (fun x i ↦ if x ∈ Φ.blocks i then 1 else 0)

/-- Convert an incidence matrix to a design -/
def fromIncMat (α : Type*) [DecidableEq α] [One α] (M : Matrix X ι α) : Design ι X where
  blocks := fun i ↦ {x | M x i = 1}


omit [DecidableEq ι] in
/-- Any column of the incidence matrix of a (v, k, λ)-BIBD sums to k -/
theorem col_sum_incmat (α : Type*) [DecidableEq α] [AddCommMonoidWithOne α] (j : ι) :
    ∑ x, (toIncMat α Φ.toDesign) x j = k := by
  simp only [toIncMat, of_apply, Finset.sum_ite_mem, univ_inter, sum_const, nsmul_one]
  rw [Φ.uniform]

omit [DecidableEq ι] in
/-- Any row of the incidence matrix of a (v, k, λ)-BIBD Φ sums to rep Φ -/
theorem row_sum_incmat (α : Type*) [DecidableEq α] [AddCommMonoidWithOne α] [Inhabited X] (x : X) :
    ∑ j, (toIncMat α Φ.toDesign) x j = rep Φ := by
  simp only [toIncMat, of_apply, sum_boole]
  rw [←rep_eq_rep_elem _ x, rep_elem]

/-- If Φ has incidence matrix M, the design corresponding to Mᵀ is the dual of Φ -/
def dual (α : Type*) [DecidableEq α] [One α] [Zero α] (Φ : Design ι X)
    : Design X ι := fromIncMat α (toIncMat α Φ)ᵀ

/--
Let Φ be a (v, k, λ, b, r)-BIBD, and let Ψ be its dual design.
The following hold:
  * Every block of Ψ has size r.
  * Every point in Ψ occurs in k blocks of Ψ.
  * Any two blocks B₁ ≠ B₂ of Ψ intersect in λ points.
-/
theorem properties_of_dual {α : Type*} [Inhabited X] [DecidableEq α]
    [One α] [Zero α] [NeZero (R := α) 1] :
    let Ψ := dual α Φ.toDesign
    (∀ i, #(Ψ.blocks i) = rep Φ) ∧
    (∀ y, #{i | y ∈ Ψ.blocks i} = k) ∧
    (∀ i j, i ≠ j → #(Ψ.blocks i ∩ Ψ.blocks j) = l) := by
  simp only [transpose_apply, of_apply, ite_eq_left_iff, zero_ne_one, imp_false,
    Decidable.not_not, mem_filter, mem_univ, true_and, ne_eq, dual, fromIncMat, toIncMat]
  constructor
  · intro i
    rw [←rep_eq_rep_elem _ _, rep_elem]
  · constructor
    · intro y
      rw [filter_univ_mem, Φ.uniform]
    · intro i j hij
      rw [filter_inter, univ_inter, filter_filter]
      convert Φ.balance {i, j} (card_pair hij) using 2
      ext x; simp only [insert_subset_iff, singleton_subset_iff, and_comm]

/--
Let M be a matrix. We say that M satisfies the RPBD condition if:
  * Every entry of M is 0 or 1.
  * MMᵀ = λJ + (r - λ)I.
-/
def rpbdCondition (α : Type*) [Ring α]
    [DecidableEq m] (l r : α) (M : Matrix m n α) : Prop :=
  isZeroOne M ∧
  M * Mᵀ = l • (allOnes _ _ _) + (r - l) • 1

/--
Let M be a matrix. We say that M satisfies the BIBD condition if:
  * M satisfies the RPBD condition.
  * uM = ku, where u is the all-ones vector.
-/
def bibdCondition (α : Type*) [Ring α] [LT α] [LE α] [DecidableEq m]
    (k l r : α) (M : Matrix m n α) : Prop :=
  (Fintype.card m > k ∧ k ≥ 2) ∧
  (allOnes _ _ α) * M = k • (allOnes (Fin 1) _ α) ∧
  rpbdCondition α l r M


/-
## RPBD and BIBD conditions

Let Φ be a design and M its incidence matrix.

The rest of this file proves that:
  * Φ is a RPBD if and only if M satisfies the RPBD condition.
  * Φ is a BIBD if and only if M satisfies the BIBD condition.
-/

variable {r : ℕ} (Ψ : RPBD ι X l r)

omit [Fintype X] [DecidableEq ι] in
theorem rpbd_incmat_allOnes (α n) [Ring α] :
    toIncMat α Ψ.toDesign * allOnes _ n _ = (r : α) • allOnes _ _ _ := by
  ext
  simp only [toIncMat, allOnes, mul_apply, of_apply, smul_apply, mul_one, sum_boole, smul_eq_mul]
  rw [Ψ.regularity]

omit [Fintype X] [DecidableEq ι] in
theorem rpbdCondition_of_rpbd (α) [Ring α] :
    rpbdCondition α l r (toIncMat _ Ψ.toDesign) := by
  constructor
  · intro i j
    simp only [toIncMat, of_apply]
    exact (ite_eq_or_eq _ _ _).symm
  · ext x y
    simp only [toIncMat, allOnes, one_apply, mul_apply, add_apply, transpose_apply, of_apply,
    smul_apply, mul_ite, mul_one, mul_zero]
    by_cases hxy : x = y
    · subst hxy
      simp only [mul_one, reduceIte, smul_eq_mul, add_sub_cancel]
      rw [sum_congr _ (fun i ↦ if x ∈ Ψ.blocks i then 1 else 0) (fun _ ↦ by simp_all only [reduceIte]),
        sum_boole, Ψ.regularity]
    · simp only [mul_one, smul_eq_mul, mul_zero, hxy, reduceIte, add_zero]
      rw [sum_congr _ (fun i ↦ if {y, x} ⊆ Ψ.blocks i then 1 else 0)
        (fun _ ↦ by simp only [insert_subset_iff, singleton_subset_iff, ite_and]), sum_boole,
        Ψ.balance {y, x} (card_pair (Ne.symm hxy))]

omit [DecidableEq ι] in
theorem bibdCondition_of_bibd {α} [Ring α] [LinearOrder α] [IsStrictOrderedRing α] [Inhabited X] :
    bibdCondition α k l (rep Φ) (toIncMat _ Φ.toDesign) := by
  constructor
  · simp_all only [Nat.cast_lt, Φ.incomplete, Φ.t_le_k, Nat.ofNat_le_cast, and_self]
  · constructor
    · ext i j
      simp only [toIncMat, allOnes, mul_apply, of_apply, smul_apply, one_mul,
        Finset.sum_ite_mem, univ_inter, sum_const, nsmul_eq_mul, mul_one, Φ.uniform, smul_eq_mul]
    · exact (rpbdCondition_of_rpbd (BIBD_to_RPBD Φ) α)

def pbd_of_rpbdCondition {α : Type*} [DecidableEq α] [Ring α] [NeZero (R := α) 1] [CharZero α]
    {M : Matrix X ι α} (l r : ℕ) (hM : rpbdCondition α l r M) : PBD ι X l where
  blocks := (fromIncMat _ M).blocks
  balance := by
    intro s hs
    obtain ⟨x, y, hxy, hs'⟩ := card_eq_two.mp hs
    have hyp := (ext_iff.mpr hM.2) x y
    simp only [allOnes, mul_apply, transpose_apply, add_apply, of_apply, smul_apply,
      one_apply, hxy, reduceIte, add_zero, smul_eq_mul, mul_zero, mul_one] at hyp
    simp only [fromIncMat]
    have : ∀ i, M x i * M y i = if M x i = 1 ∧ M y i = 1 then 1 else 0 := by
      intro i
      rcases hM.1 x i with hx | hx
      · simp only [hx, zero_mul, zero_ne_one, false_and, ite_false]
      · rcases hM.1 y i with hy | hy
        · simp only [hy, mul_zero, zero_ne_one, and_false, ite_false]
        · simp only [hx, hy, one_mul, true_and, ite_true]
    rw [sum_congr _ _ this, sum_boole, Nat.cast_inj] at hyp
    simp only [hs', mem_filter, mem_univ, true_and, insert_subset_iff, singleton_subset_iff, hyp]

def rpbd_of_rpbdCondition {α : Type*} [DecidableEq α] [Ring α] [NeZero (R := α) 1] [CharZero α]
    {M : Matrix X ι α} (l r : ℕ) (hM : rpbdCondition α l r M) :
    RPBD ι X l r := {
  blocks := (fromIncMat _ M).blocks
  balance := (pbd_of_rpbdCondition l r hM).balance
  regularity := by
    intro x
    have hyp := (ext_iff.mpr hM.2) x x
    simp only [mul_apply, transpose_apply, add_apply, smul_apply, one_apply, allOnes, of_apply,
    smul_eq_mul, ite_true, mul_one, add_sub_cancel] at hyp
    have : ∀ i, M x i * M x i = if M x i = 1 then 1 else 0 := by
      intro i
      rcases hM.1 x i with hi | hi
      · simp only [hi, mul_zero, zero_ne_one, ite_false]
      · simp only [hi, mul_one, ite_true]
    simp only [fromIncMat, mem_filter, mem_univ, true_and]
    rwa [sum_congr _ _ this, sum_boole, Nat.cast_inj] at hyp
}

def bibd_of_bibdCondition {α : Type*} [DecidableEq α] [Ring α] [LinearOrder α] [IsStrictOrderedRing α]
    {M : Matrix X ι α} (k l r : ℕ) (hM : bibdCondition α k l r M) :
    BIBD ι X k l where
  blocks := (fromIncMat _ M).blocks
  uniform := by
    intro i
    have hyp := (ext_iff.mpr hM.2.1) 0 i
    simp only [allOnes, mul_apply, of_apply, one_mul, smul_apply, smul_eq_mul, mul_one] at hyp
    have : ∀ x, M x i = if M x i = 1 then 1 else 0 := by
      intro x
      rcases hM.2.2.1 x i
      · simp_all only [zero_ne_one, reduceIte]
      · simp_all only [reduceIte]
    rwa [sum_congr _ _ this, sum_boole, Nat.cast_inj] at hyp
  incomplete := by
    obtain ⟨⟩ := hM
    simp_all only [Nat.cast_lt, Nat.ofNat_le_cast]
  t_le_k :=  by
    obtain ⟨⟩ := hM
    simp_all only [Nat.cast_lt, Nat.ofNat_le_cast]
  balance := (pbd_of_rpbdCondition l r hM.2.2).balance

end CombinatorialDesign
