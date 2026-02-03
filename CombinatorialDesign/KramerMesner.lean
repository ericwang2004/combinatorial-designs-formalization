import CombinatorialDesign.Isomorphism
import CombinatorialDesign.MatrixLemmas
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.Data.Multiset.Fintype

open CombinatorialDesign Finset MulAction Quotient

variable {ι X G : Type*} [Fintype X] [Fintype ι]
  [DecidableEq X] [DecidableEq ι] [Fintype G] [Group G] [MulAction G X]

instance : SMul G (Finset X) where
  smul g S := image (g • ·) S

omit [Fintype X] [Fintype G] in
theorem mem_smul_subset {g : G} {S : Finset X} {x : X} :
    x ∈ g • S ↔ ∃ w ∈ S, g • w = x := by
  constructor <;> intro hx
  · have : x ∈ image (fun x ↦ g • x) S := hx
    rwa [Finset.mem_image] at this
  · have : g • S = image (fun x ↦ g • x) S := rfl
    rwa [this, Finset.mem_image]

instance : MulAction G (Finset X) where
  one_smul S := by
    ext
    rw [mem_smul_subset]
    exact ⟨fun ⟨_, _, ha⟩ ↦ by rwa [←ha, one_smul],
      fun hx ↦ ⟨_, hx, by rw [one_smul]⟩⟩
  mul_smul x y S := by
    ext
    simp only [mem_smul_subset, exists_exists_and_eq_and]
    constructor; all_goals
    exact fun ⟨_, hw, ha⟩ ↦ ⟨_, hw, by rw [←ha, mul_smul]⟩

variable (G X)
abbrev jOrbits := Quotient <| orbitRel G (Finset X)

noncomputable instance : DecidableEq (Quotient <| orbitRel G X) :=
  Classical.typeDecidableEq _

noncomputable def countSubsetOrbit (O : jOrbits X G) (P : jOrbits X G) : ℕ :=
  Quotient.lift (fun Yi ↦ #{A | ⟦A⟧ = O ∧ Yi ⊆ A}) (by
  intro Y₁ Y₂ ⟨g, hg⟩
  simp only at hg ⊢
  have hg' : Y₂ = g⁻¹ • Y₁ := eq_inv_smul_iff.mpr hg
  apply card_bijective (fun S ↦ g⁻¹ • S) (MulAction.bijective _)
  intro S
  constructor <;> intro hS <;>
    simp only [mem_filter, mem_univ, true_and] at hS ⊢
  · constructor
    · rw [←hS.1]
      exact sound (by use g⁻¹)
    · intro x hx
      rw [hg', mem_smul_subset] at hx
      obtain ⟨_, hw, rfl⟩ := hx
      rw [mem_smul_subset]
      exact ⟨_, hS.2 hw, rfl⟩
  · constructor
    · rw [←hS.1]
      exact sound (by use g; simp only [smul_inv_smul])
    · intro x hx
      rw [←hg, mem_smul_subset] at hx
      obtain ⟨w, hw, rfl⟩ := hx
      have := hS.2 hw
      simp only [mem_smul_subset] at this
      obtain ⟨w_1, hw_1_mem, hw_1_eq⟩ := this
      rw [← hw_1_eq, ← mul_smul, mul_inv_cancel, one_smul]
      exact hw_1_mem
  ) P

variable {G X}

def orbitCard (O : jOrbits X G) : ℤ :=
  Quotient.lift (fun Yi ↦ #Yi) (by
  intro Y₁ Y₂ ⟨g, hg⟩
  simp only at hg ⊢
  refine Int.ofNat_inj.mpr ?_
  apply card_bijective (fun x ↦ g⁻¹  • x) (MulAction.bijective _)
  intro x
  rw [← hg]
  rw [mem_smul_subset]
  constructor
  · intro ⟨y, hy, hxy⟩
    rw [← hxy]
    rw [← mul_smul, inv_mul_cancel, one_smul]
    exact hy
  · intro h
    use g⁻¹ • x
    constructor
    · exact h
    · rw [← mul_smul, mul_inv_cancel, one_smul]
  ) O

noncomputable def orbit_blocks [Fintype X] [DecidableEq X]
  [Fintype G] [Group G] [MulAction G X]
  {k : ℤ} (O : {O : jOrbits X G // orbitCard O = k}) : Multiset (Finset X) :=
  (Finset.univ : Finset (Finset X)).val.filter (fun S => ⟦S⟧ = O.val)

variable (X G)
noncomputable def A (k₁ k₂ : ℕ) :
    Matrix {O : jOrbits X G // orbitCard O = k₁} {O : jOrbits X G // orbitCard O = k₂} ℤ :=
  Matrix.of (countSubsetOrbit X G · ·)

noncomputable instance {k : ℤ} : Fintype {O : jOrbits X G // orbitCard O = k} :=
  Fintype.ofFinite _

def KramerMesnerCondition {k : ℕ} (l : ℕ)
    (z : Matrix (Fin 1) {O : jOrbits X G // orbitCard O = k} ℤ) : Prop :=
  z * (A X G k 2) = l • allOnes (Fin 1) {O : jOrbits X G // orbitCard O = 2} ℤ

def multiset_to_function {X : Type*} [DecidableEq X] (ms : Multiset (Finset X)) :
  ms.ToType → Finset X := fun i => i

lemma card_filter_multiset_eq_card_filter_indexed {X : Type*} [DecidableEq X]
    (ms : Multiset (Finset X)) (p : (Finset X) → Prop) [DecidablePred p] :
    (ms.filter p).card = #{i : ms.ToType | p (multiset_to_function ms i)} :=
  calc
    _ = (((Finset.univ : Finset ms.ToType).val.map (↑·)).filter p).card := by
      rw [Multiset.map_univ_coe]
    _ = ((Finset.univ.val.filter fun i => p (multiset_to_function ms i)).map fun (i : ms.ToType) => (i : Finset X)).card := by
      rw [Multiset.filter_map]; rfl
    _ = (Finset.univ.val.filter fun i => p (multiset_to_function ms i)).card := by
      rw [Multiset.card_map]
    _ = _ := by rw [← Finset.filter_val, Finset.card_val]

/-- ### Kramer-Mesner Construction  -/
noncomputable def bibdOfKMCondition {k : ℕ} (l : ℕ)
    (hvk' : k < (Fintype.card X ) ∧ 2 ≤ k)
    (z : Matrix (Fin 1) {O : jOrbits X G // orbitCard O = k} ℤ) (hz : ∀ O, 0 ≤ z 0 O)
    (km : KramerMesnerCondition X G l z) :
    let ms := Finset.sum (Finset.univ : Finset {O : jOrbits X G // orbitCard O = k})
      (fun O => (z 0 O).natAbs • (orbit_blocks O));
    let ι := ms.ToType;
    BIBD ι X k l where
  blocks := by
    let ms := Finset.sum (Finset.univ : Finset {O : jOrbits X G // orbitCard O = k})
      (fun O => (z 0 O).natAbs • (orbit_blocks O))
    exact (multiset_to_function ms)
  t_le_k := hvk'.2
  incomplete := hvk'.1
  uniform := by
    let ms := Finset.sum (Finset.univ : Finset {O : jOrbits X G // orbitCard O = k})
      (fun O => (z 0 O).natAbs • (orbit_blocks O))
    intro i
    have hi_mem : (i.fst : Finset X) ∈ ms := Multiset.coe_mem
    rcases (Finset.mem_sum
            (s := (Finset.univ : Finset {O : jOrbits X G // orbitCard O = k}))
            (f := fun O ↦ (z 0 O).natAbs • orbit_blocks O)
            (b := (i.fst : Finset X))).mp
           hi_mem with ⟨O, -, hO⟩
    have hS_in : (i.fst : Finset X) ∈ orbit_blocks O := by
      exact Multiset.mem_of_mem_nsmul hO
    have hquot : (⟦(i.fst : Finset X)⟧ : jOrbits X G) = O.val := by
      have := (Multiset.mem_filter).1 hS_in
      exact this.2
    have h_eq : orbitCard (⟦(i.fst : Finset X)⟧ : jOrbits X G) = (k : ℤ) := by
      simp [hquot]
      exact O.property
    have h_int : (i.fst.card : ℤ) = k := by
      simpa [orbitCard] using h_eq
    have : Int.ofNat i.fst.card = (k : ℤ) := by
      simpa using h_int
    exact (Int.ofNat.inj this)
  balance := by
    intro s hs
    obtain ⟨x, y, hxy, rfl⟩ := card_eq_two.mp hs
    set ms := Finset.sum (Finset.univ : Finset {O : jOrbits X G // orbitCard O = k})
     (fun O => (z 0 O).natAbs • (orbit_blocks O))
    let pair_set : Finset X := {x, y}
    have h_pair_card : #pair_set = 2 := by
      exact card_pair hxy
    let O₂ : {O : jOrbits X G // orbitCard O = 2} :=
      ⟨⟦pair_set⟧, by rw [orbitCard, Quotient.lift_mk]; exact congrArg Nat.cast h_pair_card⟩
    have key_eq : (z * (A X G k 2)) 0 O₂ = l := by
      unfold KramerMesnerCondition at km
      rw [← Matrix.ext_iff] at km
      have := km 0 O₂
      simpa [Nat.cast_ofNat, Fin.isValue, Matrix.smul_apply, nsmul_eq_mul,
        allOnes, Fin.isValue, Matrix.of_apply, mul_one] using this
    symm
    rw [Mathlib.Tactic.Zify.natCast_eq]
    calc ↑l = ∑ O, z 0 O * ↑(countSubsetOrbit X G ↑O ↑O₂) := by
          exact id (Eq.symm key_eq)
        _ = ∑ O, ((z 0 O).natAbs : ℤ) *
              ↑((orbit_blocks O).filter (fun S : Finset X ↦ {x, y} ⊆ S)).card := by
          congr 1
          ext O
          rw [Int.natAbs_of_nonneg (hz O)]
          congr 1
          unfold countSubsetOrbit
          rw [Quotient.lift_mk]
          unfold orbit_blocks pair_set
          simp only [Multiset.filter_filter, Nat.cast_inj, ← Finset.filter_val, card_val]
          congr 1
          ext a
          simp only [mem_filter, mem_univ, true_and]
        _ = ↑(ms.filter (fun S => {x, y} ⊆ S)).card := by
          classical
          have h_nat : (ms.filter (fun S : Finset X ↦ {x, y} ⊆ S)).card =
              ∑ O : {O : jOrbits X G // orbitCard O = k},
                (z 0 O).natAbs * ((orbit_blocks O).filter (fun S : Finset X ↦ {x, y} ⊆ S)).card := by
            let p : Finset X → Prop := fun S ↦ {x, y} ⊆ S
            have h : ∀ T : Finset {O : jOrbits X G // orbitCard O = k},
                ((Finset.sum T (fun O ↦ (z 0 O).natAbs • orbit_blocks O)).filter
                      (fun S : Finset X ↦ p S)).card =
                    ∑ O ∈ T, (z 0 O).natAbs * ((orbit_blocks O).filter (fun S : Finset X ↦ p S)).card := by
              intro T
              refine Finset.induction ?h0 ?hstep T
              · simp
              · intro a T haT hIH
                have h1 : (((z 0 a).natAbs • orbit_blocks a).filter (fun S : Finset X ↦ p S)).card =
                    (z 0 a).natAbs * ((orbit_blocks a).filter (fun S : Finset X ↦ p S)).card := by
                  simp [Multiset.filter_nsmul, Multiset.card_nsmul]
                simp [Finset.sum_insert haT, Multiset.filter_add, Multiset.card_add, h1, hIH,
                      mul_comm, mul_left_comm, mul_assoc]
            simpa [p, ms] using h (Finset.univ)
          simpa using congrArg (fun n : ℕ ↦ (n : ℤ)) (Eq.symm h_nat)
        _ = ↑(#{i | {x, y} ⊆ multiset_to_function ms i}) := by
          congr 1
          exact card_filter_multiset_eq_card_filter_indexed ms (Subset {x, y})
