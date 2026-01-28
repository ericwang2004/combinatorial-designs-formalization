import CombinatorialDesign.IncidenceMatrix

open CombinatorialDesign Matrix Finset
namespace CombinatorialDesign

variable {ι α : Type*} [Fintype ι] [DecidableEq ι] [CommRing α] [DecidableEq α]

def isHadamard (M : Matrix ι ι α) : Prop :=
  (∀ i j, M i j = 1 ∨ M i j = -1) ∧
  M * Mᵀ = (Fintype.card ι) • 1

-- a standard Hadamard matrix is one whose (say, first) row is all 1s
def isStandardHadamard (i : ι) (M : Matrix ι ι α) : Prop :=
  isHadamard M ∧
  (∀ j, M i j = 1)

def scaleRow (c : α) (i : ι) (M : Matrix ι ι α) : Matrix ι ι α :=
  M.updateRow i (fun j ↦ c * M i j)

theorem isHadamard_of_scaleRow {M : Matrix ι ι α} (hM : isHadamard M) (i₀ : ι) :
    isHadamard (scaleRow (-1) i₀ M) := by
  -- probably will end up deleting this, or golfing it significantly
  -- I mainly went through this to refamiliarize myself with matrix manipulations
  obtain ⟨mvals, mprod⟩ := hM
  constructor
  · intro i j
    match mvals i j with
    | Or.inl h =>
      rw [scaleRow, updateRow_apply, h]
      match eq_or_ne i i₀ with
      | Or.inl hi =>
        right
        simp only [hi, ↓reduceIte, neg_mul, one_mul, neg_inj]
        rw [←hi, h]
      | Or.inr hi =>
        left
        simp only [hi, ↓reduceIte, one_mul, neg_inj]
    | Or.inr h =>
      rw [scaleRow, updateRow_apply, h]
      match eq_or_ne i i₀ with
      | Or.inl hi =>
        left
        simp only [hi, ↓reduceIte, neg_mul, one_mul, neg_inj]
        rw [←hi, h, neg_neg]
      | Or.inr hi =>
        right
        simp only [hi, ↓reduceIte, one_mul, neg_inj]
  ext i j
  simp only [scaleRow, updateRow_apply, mul_apply, smul_apply, one_apply,
    transpose_apply]
  have mprod' := ext_iff.mpr mprod
  simp only [mul_apply, transpose_apply, smul_apply, one_apply] at mprod'
  match eq_or_ne i j with
  | Or.inl hij =>
    simp only [if_pos hij]
    match eq_or_ne i i₀ with
    | Or.inl hi₀ =>
      simp only [if_pos hi₀,
        if_pos (c := j = i₀) (by rw [←hij, hi₀]),
        neg_mul, one_mul, mul_neg, neg_neg, mul_one]
      rw [mprod', if_pos rfl]
    | Or.inr hi₀ =>
      simp only [if_neg hi₀, ←hij]
      rw [mprod', if_pos rfl]
  | Or.inr hij =>
    simp only [if_neg hij]
    match eq_or_ne i i₀ with
    | Or.inl hi₀ =>
      simp only [if_pos hi₀]
      rw [←hi₀]
      simp only [if_neg hij.symm]
      simp_rw [mul_assoc]
      rw [←Finset.mul_sum, mprod', if_neg hij, smul_zero, mul_zero]
    | Or.inr hi₀ =>
      simp_rw [if_neg hi₀]
      match eq_or_ne j i₀ with
      | Or.inl hj₀ =>
        simp_rw [if_pos hj₀, ←mul_assoc, mul_comm _ (-1 : α), mul_assoc]
        rw [←Finset.mul_sum, mprod', if_neg hi₀, smul_zero, mul_zero]
      | Or.inr hj₀ =>
        simp_rw [if_neg hj₀]
        rw [mprod', if_neg hij]

-- any Hadamard matrix can be transformed to a standard Hadamard matrix
theorem exists_standard_hadamard {M : Matrix ι ι α} (hM : isHadamard M) :
    ∀ i, ∃ N : Matrix ι ι α, isStandardHadamard i N := by
  intro i
  sorry

-- if a finite sum of ±1 is 0, then the sum is over evenly many terms
theorem even_of_sum_zero {f : ι → α} (hf : ∀ i, f i = 1 ∨ f i = -1)
    (hsum : ∑ i, f i = 0) : 2 ∣ Fintype.card ι := by
  -- kind of a practice exercise, not necessarily used in the final proof
  sorry

theorem four_div_helper {f g : ι → α}
    (hf : ∀ i, f i = 1 ∨ f i = -1)
    (hg : ∀ i, g i = 1 ∨ g i = -1)
    (fsum : ∑ i, f i = 0)
    (gsum : ∑ i, g i = 0)
    (fgsum : ∑ i, f i * g i = 0) :
    4 ∣ Fintype.card ι := by
  let A : Finset ι := { i | f i = 1 ∧ g i = 1 }
  let B : Finset ι := { i | f i = 1 ∧ g i = -1 }
  let C : Finset ι := { i | f i = -1 ∧ g i = 1 }
  let D : Finset ι := { i | f i = -1 ∧ g i = -1 }
  let AB : Finset ι := { i | f i = 1 }
  let CD : Finset ι := { i | f i = -1 }
  let AC : Finset ι := { i | g i = 1 }
  let BD : Finset ι := { i | g i = -1 }
  have unionST : AB = A ∪ B ∧ CD = C ∪ D := by
    sorry
  -- could proceed by cardinality arguments like in Stinson,
  -- but I want to come up with something more elegant
  sorry

theorem four_div_of_hadamard {i₀ j₀ k₀ : ι}
    (hij : i₀ ≠ j₀) (hik : i₀ ≠ k₀) (hjk : j₀ ≠ k₀)
    {M : Matrix ι ι α} (hM : isHadamard M) :
    4 ∣ Fintype.card ι := by
  obtain ⟨N, ⟨valsN, hadN'⟩, rowN⟩ := exists_standard_hadamard hM i₀
  have hadN := ext_iff.mpr hadN'
  simp_rw [mul_apply, transpose_apply, smul_apply, one_apply] at hadN
  have had_ij := hadN i₀ j₀
  simp_rw [rowN, one_mul, if_neg hij, smul_zero] at had_ij
  have even := even_of_sum_zero (valsN j₀) had_ij
  -- just apply four_div_helper
  -- I haven't bothered to do this since we'll probably end up
  -- changing the statement of four_div_helper
  sorry

end CombinatorialDesign
