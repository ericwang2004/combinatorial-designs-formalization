import CombinatorialDesign.IncidenceMatrix

/-!

# Hadamard matrices

This files defines Hadamard matrices and proves that
the dimension of any Hadamard matrix must be a multiple of 4.

-/

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

/-
Proof sketch for `isHadamard_of_scaleRow`:
Scaling row i₀ by -1 preserves the Hadamard property.
1. Entries remain ±1: If M[i,j] ∈ {1,-1}, then -M[i,j] ∈ {-1,1}.
2. The product M·Mᵀ is unchanged because in each dot product of rows i and j:
   - If neither i nor j is i₀, the dot product is unchanged.
   - If exactly one of i,j is i₀, the dot product gains a factor of (-1)(-1)=1
     from the row and its transpose column.
   - If both are i₀ (i.e., the diagonal), each term is multiplied by (-1)²=1.
-/
omit [DecidableEq α] in
theorem isHadamard_of_scaleRow {M : Matrix ι ι α} (hM : isHadamard M) (i₀ : ι) :
    isHadamard (scaleRow (-1) i₀ M) := by
  obtain ⟨mvals, mprod⟩ := hM
  refine ⟨fun i j => ?_, ?_⟩
  · simp only [scaleRow, updateRow_apply]
    split_ifs with hi
    · rcases mvals i₀ j with h | h <;> simp [h]
    · exact mvals i j
  · have mprod' := ext_iff.mpr mprod
    simp only [mul_apply, transpose_apply, smul_apply, one_apply] at mprod'
    ext i j
    simp only [scaleRow, updateRow_apply, mul_apply, smul_apply, one_apply, transpose_apply]
    rcases eq_or_ne i j with hij | hij
    · subst hij
      rcases eq_or_ne i i₀ with hi₀ | hi₀
      · simp only [hi₀, ↓reduceIte, neg_mul, one_mul, mul_neg, neg_neg, mprod']
      · simp only [if_neg hi₀, mprod']
    · simp only [if_neg hij]
      rcases eq_or_ne i i₀ with hi₀ | hi₀
      · simp only [if_pos hi₀]; rw [← hi₀]; simp only [if_neg hij.symm]
        simp_rw [mul_assoc, ← Finset.mul_sum, mprod', if_neg hij, smul_zero, mul_zero]
      · simp only [if_neg hi₀]
        rcases eq_or_ne j i₀ with hj₀ | hj₀
        · simp_rw [if_pos hj₀, ← mul_assoc, mul_comm _ (-1 : α), mul_assoc, ← Finset.mul_sum,
            mprod', if_neg hi₀, smul_zero, mul_zero]
        · simp_rw [if_neg hj₀, mprod', if_neg hij]

/-
Proof sketch for `exists_standard_hadamard`:
Any Hadamard matrix can be normalized so that a given row i₀ is all 1s.
Define N[i,j] = M[i,j] · M[i₀,j] (multiply each column by the sign of its entry in row i₀).
1. Entries of N are ±1: products of ±1 values.
2. Row i₀ of N is all 1s: M[i₀,j]² = 1 for all j.
3. N·Nᵀ = n·I: The (i,j) entry of N·Nᵀ is ∑ₖ M[i,k]·M[i₀,k]·M[j,k]·M[i₀,k]
   = ∑ₖ M[i,k]·M[j,k]·(M[i₀,k])² = ∑ₖ M[i,k]·M[j,k] = (M·Mᵀ)[i,j].
-/
omit [DecidableEq α] in
theorem exists_standard_hadamard {M : Matrix ι ι α} (hM : isHadamard M) :
    ∀ i, ∃ N : Matrix ι ι α, isStandardHadamard i N := by
  intro i₀
  use fun i j => M i j * M i₀ j
  obtain ⟨mvals, mprod⟩ := hM
  have sq_eq_one : ∀ k, M i₀ k * M i₀ k = 1 := fun k => by rcases mvals i₀ k with h | h <;> simp [h]
  refine ⟨⟨fun i j => ?_, ?_⟩, fun j => ?_⟩
  · rcases mvals i j with h | h <;> rcases mvals i₀ j with h' | h' <;> simp [h, h']
  · ext i j
    simp only [mul_apply, transpose_apply, smul_apply, one_apply]
    have h1 : ∀ k, M i k * M i₀ k * (M j k * M i₀ k) = M i k * M j k := fun k => by
      rw [show M i k * M i₀ k * (M j k * M i₀ k) = M i k * M j k * (M i₀ k * M i₀ k) by ring,
          sq_eq_one, mul_one]
    simp_rw [h1]
    exact congrFun (congrFun mprod i) j |> fun h => by
      simp only [mul_apply, transpose_apply, smul_apply, one_apply] at h; exact h
  · rcases mvals i₀ j with h | h <;> simp [h]

/-
Proof sketch for `even_of_sum_zero`:
If f : ι → {1,-1} and ∑ᵢ f(i) = 0, then |ι| is even.
Partition ι into S = {i : f(i)=1} and T = {i : f(i)=-1}.
Then ∑ᵢ f(i) = |S| - |T| = 0, so |S| = |T|.
Hence |ι| = |S| + |T| = 2|T|, which is even.
-/
theorem even_of_sum_zero [CharZero α] {f : ι → α} (hf : ∀ i, f i = 1 ∨ f i = -1)
    (hsum : ∑ i, f i = 0) : 2 ∣ Fintype.card ι := by
  let S := Finset.univ.filter (fun i => f i = 1)
  let T := Finset.univ.filter (fun i => f i = -1)
  have one_ne : (1 : α) ≠ -1 := fun h => two_ne_zero (α := α) (by
      have h2 : (1 : α) + 1 = -1 + 1 := congrArg (· + 1) h
      simp only [neg_add_cancel] at h2; exact one_add_one_eq_two.symm.trans h2)
  have hST_disjoint : Disjoint S T := Finset.disjoint_filter.mpr fun _ _ h1 h2 => one_ne (h1.symm.trans h2)
  have hST_cover : S ∪ T = Finset.univ := by
    ext i; simp only [S, T, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
    rcases hf i with h | h <;> simp [h, one_ne, one_ne.symm]
  have hsum' : (S.card : α) - T.card = 0 := by
    have hS : ∑ i ∈ S, f i = S.card := by
      conv_lhs => rw [Finset.sum_congr rfl fun i hi => (Finset.mem_filter.mp hi).2, Finset.sum_const]
      simp [S]
    have hT : ∑ i ∈ T, f i = -(T.card : α) := by
      conv_lhs => rw [Finset.sum_congr rfl fun i hi => (Finset.mem_filter.mp hi).2, Finset.sum_const]
      simp [T]
    calc (S.card : α) - T.card = ∑ i ∈ S, f i + ∑ i ∈ T, f i := by rw [hS, hT]; ring
      _ = ∑ i, f i := by rw [← Finset.sum_union hST_disjoint, hST_cover]
      _ = 0 := hsum
  have hcard_eq : S.card = T.card := Nat.cast_injective (by rwa [sub_eq_zero] at hsum')
  have htotal : Fintype.card ι = S.card + T.card := by
    rw [← Finset.card_union_of_disjoint hST_disjoint, hST_cover, Finset.card_univ]
  rw [htotal, hcard_eq]; exact ⟨T.card, by ring⟩

/-
Proof sketch for `four_div_helper`:
Given f,g : ι → {1,-1} with ∑f = ∑g = ∑(f·g) = 0, we show 4 | |ι|.
Partition ι into four sets based on signs:
  A = {f=1, g=1}, B = {f=1, g=-1}, C = {f=-1, g=1}, D = {f=-1, g=-1}.
Then |ι| = |A| + |B| + |C| + |D|. From the three sum conditions:
  ∑f = 0  ⟹  |A| + |B| - |C| - |D| = 0  ⟹  |A| + |B| = |C| + |D|
  ∑g = 0  ⟹  |A| - |B| + |C| - |D| = 0  ⟹  |A| + |C| = |B| + |D|
  ∑fg = 0 ⟹  |A| - |B| - |C| + |D| = 0  ⟹  |A| + |D| = |B| + |C|
Solving: |A| = |B| = |C| = |D|, so |ι| = 4|A|.
-/
theorem four_div_helper [CharZero α] {f g : ι → α}
    (hf : ∀ i, f i = 1 ∨ f i = -1)
    (hg : ∀ i, g i = 1 ∨ g i = -1)
    (fsum : ∑ i, f i = 0)
    (gsum : ∑ i, g i = 0)
    (fgsum : ∑ i, f i * g i = 0) :
    4 ∣ Fintype.card ι := by
  let A := Finset.univ.filter (fun i => f i = 1 ∧ g i = 1)
  let B := Finset.univ.filter (fun i => f i = 1 ∧ g i = -1)
  let C := Finset.univ.filter (fun i => f i = -1 ∧ g i = 1)
  let D := Finset.univ.filter (fun i => f i = -1 ∧ g i = -1)
  have one_ne : (1 : α) ≠ -1 := fun h => two_ne_zero (α := α) (by
    have h2 : (1 : α) + 1 = -1 + 1 := congrArg (· + 1) h
    simp only [neg_add_cancel] at h2; exact one_add_one_eq_two.symm.trans h2)
  have hAB : Disjoint A B := Finset.disjoint_filter.mpr fun _ _ h1 h2 => one_ne (h1.2.symm.trans h2.2)
  have hAC : Disjoint A C := Finset.disjoint_filter.mpr fun _ _ h1 h2 => one_ne (h1.1.symm.trans h2.1)
  have hAD : Disjoint A D := Finset.disjoint_filter.mpr fun _ _ h1 h2 => one_ne (h1.1.symm.trans h2.1)
  have hBC : Disjoint B C := Finset.disjoint_filter.mpr fun _ _ h1 h2 => one_ne (h1.1.symm.trans h2.1)
  have hBD : Disjoint B D := Finset.disjoint_filter.mpr fun _ _ h1 h2 => one_ne (h1.1.symm.trans h2.1)
  have hCD : Disjoint C D := Finset.disjoint_filter.mpr fun _ _ h1 h2 => one_ne (h1.2.symm.trans h2.2)
  have hcover : A ∪ B ∪ C ∪ D = Finset.univ := by
    ext i; simp only [A, B, C, D, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
    rcases hf i with hfi | hfi <;> rcases hg i with hgi | hgi <;> simp [hfi, hgi]
  have htotal : Fintype.card ι = A.card + B.card + C.card + D.card := by
    rw [← Finset.card_univ, ← hcover]
    simp only [Finset.card_union_of_disjoint hAB,
      Finset.card_union_of_disjoint (Finset.disjoint_union_left.mpr ⟨hAC, hBC⟩),
      Finset.card_union_of_disjoint (Finset.disjoint_union_left.mpr ⟨Finset.disjoint_union_left.mpr ⟨hAD, hBD⟩, hCD⟩)]
  have sum4 : ∀ h : ι → α, ∑ i, h i = ∑ i ∈ A, h i + ∑ i ∈ B, h i + ∑ i ∈ C, h i + ∑ i ∈ D, h i := fun h => by
    rw [← hcover, Finset.sum_union (Finset.disjoint_union_left.mpr ⟨Finset.disjoint_union_left.mpr ⟨hAD, hBD⟩, hCD⟩),
      Finset.sum_union (Finset.disjoint_union_left.mpr ⟨hAC, hBC⟩), Finset.sum_union hAB]
  have sum_neg_one : ∀ S : Finset ι, ∑ i ∈ S, (-1 : α) = -(S.card : α) := fun S => by simp [Finset.sum_const]
  have memA : ∀ i ∈ A, f i = 1 ∧ g i = 1 := fun i hi => (Finset.mem_filter.mp hi).2
  have memB : ∀ i ∈ B, f i = 1 ∧ g i = -1 := fun i hi => (Finset.mem_filter.mp hi).2
  have memC : ∀ i ∈ C, f i = -1 ∧ g i = 1 := fun i hi => (Finset.mem_filter.mp hi).2
  have memD : ∀ i ∈ D, f i = -1 ∧ g i = -1 := fun i hi => (Finset.mem_filter.mp hi).2
  have eq1 : A.card + B.card = C.card + D.card := by
    have h : (A.card : α) + B.card = C.card + D.card := by
      have sumf := fsum; rw [sum4] at sumf
      have hA : ∑ i ∈ A, f i = A.card := by simp [Finset.sum_congr rfl fun i hi => (memA i hi).1]
      have hB : ∑ i ∈ B, f i = B.card := by simp [Finset.sum_congr rfl fun i hi => (memB i hi).1]
      have hC : ∑ i ∈ C, f i = -(C.card : α) := by rw [Finset.sum_congr rfl fun i hi => (memC i hi).1, sum_neg_one]
      have hD : ∑ i ∈ D, f i = -(D.card : α) := by rw [Finset.sum_congr rfl fun i hi => (memD i hi).1, sum_neg_one]
      simp only [hA, hB, hC, hD] at sumf; linear_combination sumf
    simp only [← Nat.cast_add] at h; exact Nat.cast_injective h
  have eq2 : A.card + C.card = B.card + D.card := by
    have h : (A.card : α) + C.card = B.card + D.card := by
      have sumg := gsum; rw [sum4] at sumg
      have hA : ∑ i ∈ A, g i = A.card := by simp [Finset.sum_congr rfl fun i hi => (memA i hi).2]
      have hB : ∑ i ∈ B, g i = -(B.card : α) := by rw [Finset.sum_congr rfl fun i hi => (memB i hi).2, sum_neg_one]
      have hC : ∑ i ∈ C, g i = C.card := by simp [Finset.sum_congr rfl fun i hi => (memC i hi).2]
      have hD : ∑ i ∈ D, g i = -(D.card : α) := by rw [Finset.sum_congr rfl fun i hi => (memD i hi).2, sum_neg_one]
      simp only [hA, hB, hC, hD] at sumg; linear_combination sumg
    simp only [← Nat.cast_add] at h; exact Nat.cast_injective h
  have eq3 : A.card + D.card = B.card + C.card := by
    have h : (A.card : α) + D.card = B.card + C.card := by
      have sumfg := fgsum; rw [sum4] at sumfg
      have hfgA : ∀ i ∈ A, f i * g i = 1 := fun i hi => by simp [(memA i hi).1, (memA i hi).2]
      have hfgB : ∀ i ∈ B, f i * g i = -1 := fun i hi => by simp [(memB i hi).1, (memB i hi).2]
      have hfgC : ∀ i ∈ C, f i * g i = -1 := fun i hi => by simp [(memC i hi).1, (memC i hi).2]
      have hfgD : ∀ i ∈ D, f i * g i = 1 := fun i hi => by simp [(memD i hi).1, (memD i hi).2]
      have hA : ∑ i ∈ A, f i * g i = A.card := by simp [Finset.sum_congr rfl hfgA]
      have hB : ∑ i ∈ B, f i * g i = -(B.card : α) := by rw [Finset.sum_congr rfl hfgB, sum_neg_one]
      have hC : ∑ i ∈ C, f i * g i = -(C.card : α) := by rw [Finset.sum_congr rfl hfgC, sum_neg_one]
      have hD : ∑ i ∈ D, f i * g i = D.card := by simp [Finset.sum_congr rfl hfgD]
      simp only [hA, hB, hC, hD] at sumfg; linear_combination sumfg
    simp only [← Nat.cast_add] at h; exact Nat.cast_injective h
  rw [htotal]; omega

/-
Proof sketch for `four_div_of_hadamard`:
If an n×n Hadamard matrix exists with n > 2, then 4 | n.
Given three distinct indices i₀, j₀, k₀, normalize M so row i₀ is all 1s (call it N).
Since N·Nᵀ = n·I, for distinct rows:
  - Row i₀ · Row j₀ = 0: ∑ₖ 1·N[j₀,k] = ∑ₖ N[j₀,k] = 0
  - Row i₀ · Row k₀ = 0: ∑ₖ N[k₀,k] = 0
  - Row j₀ · Row k₀ = 0: ∑ₖ N[j₀,k]·N[k₀,k] = 0
Apply `four_div_helper` with f = N[j₀,·] and g = N[k₀,·].
-/
theorem four_div_of_hadamard [CharZero α] {i₀ j₀ k₀ : ι}
    (hij : i₀ ≠ j₀) (hik : i₀ ≠ k₀) (hjk : j₀ ≠ k₀)
    {M : Matrix ι ι α} (hM : isHadamard M) :
    4 ∣ Fintype.card ι := by
  obtain ⟨N, ⟨valsN, hadN'⟩, rowN⟩ := exists_standard_hadamard hM i₀
  have hadN := fun a b => congrFun (congrFun hadN' a) b
  simp only [mul_apply, transpose_apply, smul_apply, one_apply] at hadN
  have had_ij : ∑ k, N j₀ k = 0 := by simpa [rowN, if_neg hij] using hadN i₀ j₀
  have had_ik : ∑ k, N k₀ k = 0 := by simpa [rowN, if_neg hik] using hadN i₀ k₀
  have had_jk : ∑ k, N j₀ k * N k₀ k = 0 := by simpa [if_neg hjk] using hadN j₀ k₀
  exact four_div_helper (valsN j₀) (valsN k₀) had_ij had_ik had_jk

end CombinatorialDesign
