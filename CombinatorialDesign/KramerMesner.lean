import CombinatorialDesign.Isomorphism
import Mathlib.GroupTheory.GroupAction.Quotient

open CombinatorialDesign Finset MulAction Quotient

variable {X G} [Fintype X] [DecidableEq X] [Fintype G] [Group G] [MulAction G X]

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
      sorry
  ) P

variable {G X}
def orbitCard (O : jOrbits X G) : ℤ :=
  Quotient.lift (fun Yi ↦ #Yi) (by
  intro Y₁ Y₂ ⟨g, hg⟩
  simp only at hg ⊢
  refine Int.ofNat_inj.mpr ?_
  apply card_bijective (fun x ↦ g • x) (MulAction.bijective _)
  intro x
  sorry) O

variable (G X)
noncomputable def A (k₁ k₂ : ℕ) :
    Matrix {O : jOrbits X G // orbitCard O = k₁} {O : jOrbits X G // orbitCard O = k₂} ℤ :=
  Matrix.of (countSubsetOrbit X G · ·)

noncomputable instance {k} : Fintype {O : jOrbits X G // orbitCard O = k} :=
  Fintype.ofFinite _

def KramerMesnerCondition {k : ℕ} (l : ℕ)
    (z : Matrix (Fin 1) {O : jOrbits X G // orbitCard O = k} ℤ) : Prop :=
  z * (A X G k 2) = l • allOnes (Fin 1) {O : jOrbits X G // orbitCard O = 2} ℤ

/-- ### Kramer-Mesner Construction  -/
-- have to figure out what `b` is in the output `BIBD X v b k l`
def bibdOfKMCondition {k : ℕ} (v l : ℕ)
    (z : Matrix (Fin 1) {O : jOrbits X G // orbitCard O = k} ℤ)
    (km : KramerMesnerCondition X G l z) : BIBD X v b k l where
  blocks := sorry
  hvk := sorry
  hX := sorry
  hA := sorry
  balance := sorry

-- theorem bibdOfKMCondition_property {v k l : ℕ}
--     {z : Matrix (Fin 1) {O : jOrbits X G // orbitCard O = k} ℤ}
--     (km : KramerMesnerCondition X G l z) :
--     let Φ := bibdOfKMCondition X G v l z km
