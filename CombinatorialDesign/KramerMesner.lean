import CombinatorialDesign.Isomorphism
import CombinatorialDesign.MatrixLemmas
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.Data.Multiset.Fintype

/-!
# Kramer-Mesner Theorem for t-Designs

This file formalizes the Kramer-Mesner theorem, which provides a powerful method for
constructing t-designs using group actions.

## Main Definitions

* `jOrbits X G` - The set of orbits of k-subsets of X under the group action of G
* `countSubsetOrbit O P` - Counts k-subsets in orbit O that contain a representative of orbit P
* `orbitCard O` - The cardinality of any representative of orbit O (well-defined on orbits)
* `IsGInvariant D` - Property that a design's block multiset is invariant under G
* `KMat X G k₁ k₂` - The Kramer-Mesner matrix indexed by orbits
* `GeneralizedKramerMesnerCondition` - The condition z * A(k,t) = λ * 1

## Main Results

* `tDesignOfKMCondition` - Constructs a t-design from a solution to the KM system
* `tDesignOfKMCondition_isGInvariant` - The constructed design is G-invariant
* `kmConditionOfGInvariantDesign` - A G-invariant design yields a KM solution (converse)

## References

* Stinson, Combinatorial Designs, Constructions and Analysis
* E. Kramer and D. Mesner, "t-designs on hypergraphs", Discrete Math. 15 (1976) 263-296

-/

open CombinatorialDesign Finset MulAction Quotient

/-! ## Group Action on Finite Subsets

We define the natural action of a group G on finite subsets of X: for g ∈ G and S ⊆ X,
we have g • S = {g • x : x ∈ S}. This is the pointwise action.
-/

variable {ι X G : Type*} [Fintype X] [Fintype ι]
  [DecidableEq X] [DecidableEq ι] [Fintype G] [Group G] [MulAction G X]

/-- The scalar multiplication of G on Finset X: g • S = {g • x : x ∈ S} -/
instance : SMul G (Finset X) where
  smul g S := image (g • ·) S

omit [Fintype X] [Fintype G] in
/-- Membership characterization: x ∈ g • S iff x = g • w for some w ∈ S -/
theorem mem_smul_subset {g : G} {S : Finset X} {x : X} :
    x ∈ g • S ↔ ∃ w ∈ S, g • w = x := Finset.mem_image

/-- The pointwise action of G on Finset X forms a MulAction -/
instance : MulAction G (Finset X) where
  one_smul S := by ext x; simp [mem_smul_subset]
  mul_smul g h S := by
    ext x
    simp only [mem_smul_subset, exists_exists_and_eq_and, mul_smul]

/-! ## Orbits of Subsets

We define the orbits of finite subsets under the group action, and functions to count
subsets within orbits. These are the key ingredients for the Kramer-Mesner matrix.
-/

variable (G X)

/-- The orbits of finite subsets of X under the action of G -/
abbrev jOrbits := Quotient <| orbitRel G (Finset X)

noncomputable instance : DecidableEq (Quotient <| orbitRel G X) :=
  Classical.typeDecidableEq _

/-- Count the number of subsets in orbit O that contain a representative of orbit P. -/
noncomputable def countSubsetOrbit (O : jOrbits X G) (P : jOrbits X G) : ℕ :=
  Quotient.lift (fun Yi ↦ #{A | ⟦A⟧ = O ∧ Yi ⊆ A}) (by
    intro Y₁ Y₂ ⟨g, hg⟩
    simp only at hg ⊢
    have hg' : Y₂ = g⁻¹ • Y₁ := eq_inv_smul_iff.mpr hg
    apply card_bijective (fun S ↦ g⁻¹ • S) (MulAction.bijective _)
    intro S
    constructor <;> intro hS <;> simp only [mem_filter, mem_univ, true_and] at hS ⊢
    · exact ⟨by rw [← hS.1]; exact sound ⟨g⁻¹, rfl⟩, fun x hx ↦ by
        rw [hg', mem_smul_subset] at hx; obtain ⟨_, hw, rfl⟩ := hx
        rw [mem_smul_subset]; exact ⟨_, hS.2 hw, rfl⟩⟩
    · refine ⟨by rw [← hS.1]; exact sound ⟨g, smul_inv_smul g S⟩, fun x hx ↦ ?_⟩
      rw [← hg, mem_smul_subset] at hx; obtain ⟨w, hw, rfl⟩ := hx
      obtain ⟨w', hw'_mem, hw'_eq⟩ := mem_smul_subset.mp (hS.2 hw)
      rw [← hw'_eq, ← mul_smul, mul_inv_cancel, one_smul]; exact hw'_mem
  ) P

variable {G X}

/-- The cardinality of any representative of an orbit. -/
def orbitCard (O : jOrbits X G) : ℤ :=
  Quotient.lift (fun Yi ↦ #Yi) (by
    intro Y₁ Y₂ ⟨g, hg⟩
    simp only at hg ⊢
    refine Int.ofNat_inj.mpr (card_bijective (fun x ↦ g⁻¹ • x) (MulAction.bijective _) fun x ↦ ?_)
    rw [← hg, mem_smul_subset]
    exact ⟨fun ⟨y, hy, hxy⟩ ↦ by simp only [← hxy, inv_smul_smul]; exact hy,
           fun h ↦ ⟨g⁻¹ • x, h, smul_inv_smul g x⟩⟩
  ) O

/-- The multiset of all subsets in a given orbit O of k-subsets -/
noncomputable def orbit_blocks [Fintype X] [DecidableEq X]
    [Fintype G] [Group G] [MulAction G X]
    {k : ℤ} (O : {O : jOrbits X G // orbitCard O = k}) : Multiset (Finset X) :=
  (Finset.univ : Finset (Finset X)).val.filter (fun S => ⟦S⟧ = O.val)

noncomputable instance {k : ℤ} : Fintype {O : jOrbits X G // orbitCard O = k} :=
  Fintype.ofFinite _

/-! ## G-Invariance

A design is **G-invariant** if its multiset of blocks is closed under the group action.
We define this property and the related concepts of block and orbit multiplicities.
-/

section GInvariance

variable (ι X G : Type*) [Fintype X] [Fintype ι] [DecidableEq X] [DecidableEq ι]
  [Fintype G] [Group G] [MulAction G X]

/-- A design is G-invariant if for every g ∈ G, the action on blocks is a permutation of the
    block multiset. Equivalently, the multiset of blocks is invariant under G. -/
def IsGInvariant (D : Design ι X) : Prop :=
  ∀ g : G, (Finset.univ : Finset ι).val.map D.blocks =
           (Finset.univ : Finset ι).val.map (fun i => g • D.blocks i)

/-- The multiplicity of a k-subset S in the block multiset of a design -/
noncomputable def blockMultiplicity (D : Design ι X) (S : Finset X) : ℕ :=
  Multiset.count S ((Finset.univ : Finset ι).val.map D.blocks)

omit [Fintype X] [DecidableEq ι] [Fintype G] in
/-- For a G-invariant design, blocks in the same orbit have the same multiplicity -/
lemma orbit_multiplicity_constant (D : Design ι X) (hD : IsGInvariant ι X G D)
    (S₁ S₂ : Finset X) (hOrbit : ⟦S₁⟧ = (⟦S₂⟧ : jOrbits X G)) :
    blockMultiplicity ι X D S₁ = blockMultiplicity ι X D S₂ := by
  obtain ⟨g, hg⟩ := Quotient.exact hOrbit
  simp only at hg
  unfold blockMultiplicity
  have hinv := hD g
  have hmap : (Finset.univ : Finset ι).val.map (fun i => g • D.blocks i) =
              ((Finset.univ : Finset ι).val.map D.blocks).map (g • ·) := by rw [Multiset.map_map]; rfl
  calc Multiset.count S₁ ((Finset.univ : Finset ι).val.map D.blocks)
      = Multiset.count (g • S₂) ((Finset.univ : Finset ι).val.map D.blocks) := by rw [hg]
    _ = Multiset.count (g • S₂) ((Finset.univ : Finset ι).val.map (fun i => g • D.blocks i)) := by rw [← hinv]
    _ = Multiset.count (g • S₂) (((Finset.univ : Finset ι).val.map D.blocks).map (g • ·)) := by rw [hmap]
    _ = Multiset.count S₂ ((Finset.univ : Finset ι).val.map D.blocks) := by
        rw [Multiset.count_map_eq_count' (fun S => g • S) _ (MulAction.injective g)]

/-- The orbit multiplicity: how many times blocks from a given orbit appear in the design -/
noncomputable def orbitMultiplicity (D : Design ι X) (hD : IsGInvariant ι X G D)
    (O : jOrbits X G) : ℕ :=
  Quotient.lift (fun S => blockMultiplicity ι X D S)
    (fun S₁ S₂ h => orbit_multiplicity_constant ι X G D hD S₁ S₂ (Quotient.sound h)) O

omit [Fintype X] [DecidableEq ι] [Fintype G] in
/-- orbitMultiplicity unfolds to blockMultiplicity of any representative -/
lemma orbitMultiplicity_eq_blockMultiplicity (D : Design ι X) (hD : IsGInvariant ι X G D)
    (S : Finset X) : orbitMultiplicity ι X G D hD ⟦S⟧ = blockMultiplicity ι X D S := by
  unfold orbitMultiplicity
  rfl

omit [Fintype X] [DecidableEq ι] in
/-- blockMultiplicity equals the cardinality of block indices mapping to S -/
lemma blockMultiplicity_eq_card (D : Design ι X) (S : Finset X) :
    blockMultiplicity ι X D S = #{i : ι | D.blocks i = S} := by
  unfold blockMultiplicity
  rw [Multiset.count_eq_card_filter_eq]
  conv_lhs => rw [Multiset.filter_map]
  rw [Multiset.card_map, ← Finset.filter_val, Finset.card_val]
  congr 1; ext i
  simp only [Function.comp_apply, Finset.mem_filter, Finset.mem_univ, true_and, eq_comm]

omit [Fintype G] in
/-- countSubsetOrbit counts k-sets in an orbit containing a given t-set -/
lemma countSubsetOrbit_eq_card (O : jOrbits X G) (T : Finset X) :
    countSubsetOrbit X G O ⟦T⟧ = #{S : Finset X | ⟦S⟧ = O ∧ T ⊆ S} := by
  unfold countSubsetOrbit
  rfl

end GInvariance

/-! ## The Kramer-Mesner Matrix

The Kramer-Mesner matrix `KMat(k₁, k₂)` has rows indexed by orbits of k₁-subsets,
columns indexed by orbits of k₂-subsets, and entry `KMat[O, P] = countSubsetOrbit(O, P)`.
-/

variable (X G)

/-- The Kramer-Mesner matrix: KMat[O, P] counts k₁-subsets in orbit O containing
    a representative k₂-subset from orbit P -/
noncomputable def KMat (k₁ k₂ : ℕ) :
    Matrix {O : jOrbits X G // orbitCard O = k₁} {O : jOrbits X G // orbitCard O = k₂} ℤ :=
  Matrix.of (countSubsetOrbit X G · ·)

/-! ## Auxiliary Lemmas for Multisets -/

/-- Coercion from multiset indices to the underlying type -/
def multiset_to_function {X : Type*} [DecidableEq X] (ms : Multiset (Finset X)) :
    ms.ToType → Finset X := fun i => i

/-- Filtering a multiset and counting equals filtering the index type -/
lemma card_filter_multiset_eq_card_filter_indexed {X : Type*} [DecidableEq X]
    (ms : Multiset (Finset X)) (p : (Finset X) → Prop) [DecidablePred p] :
    (ms.filter p).card = #{i : ms.ToType | p (multiset_to_function ms i)} :=
  calc
    _ = (((Finset.univ : Finset ms.ToType).val.map (↑·)).filter p).card := by
      rw [Multiset.map_univ_coe]
    _ = ((Finset.univ.val.filter fun i => p (multiset_to_function ms i)).map
          fun (i : ms.ToType) => (i : Finset X)).card := by
      rw [Multiset.filter_map]; rfl
    _ = (Finset.univ.val.filter fun i => p (multiset_to_function ms i)).card := by
      rw [Multiset.card_map]
    _ = _ := by rw [← Finset.filter_val, Finset.card_val]

/-!
## Kramer-Mesner Theorem

The **Kramer-Mesner theorem** provides a method for constructing t-designs using group actions.

### Statement

Let G be a permutation group acting on a set X of v points. Let T₁, T₂, ..., Tₘ be the orbits
of t-subsets of X under G, and let K₁, K₂, ..., Kₙ be the orbits of k-subsets of X under G.

Define the **Kramer-Mesner matrix** KMat = (aᵢⱼ) where:
  aᵢⱼ = |{K ∈ Kⱼ : T ⊆ K}|
for any fixed representative T ∈ Tᵢ (this value is independent of the choice of representative).

Then a G-invariant t-(v, k, λ) design exists if and only if there exists a non-negative integer
solution x = (x₁, x₂, ..., xₙ)ᵀ to the system:
  x * KMat = λ1
where 1 is the all-ones vector.
-/

/-- Kramer-Mesner condition for t-designs.
    A solution z to z * A(k,t) = λ * 1 gives a G-invariant t-(v,k,λ) design. -/
def KramerMesnerCondition (t k : ℕ) (l : ℕ)
    (z : Matrix (Fin 1) {O : jOrbits X G // orbitCard O = k} ℤ) : Prop :=
  z * (KMat X G k t) = l • allOnes (Fin 1) {O : jOrbits X G // orbitCard O = t} ℤ

/-!
## Forward Direction: Constructing Designs from Kramer-Mesner Solutions

Given a non-negative integer solution to the Kramer-Mesner system, we construct a t-design
and prove that it is automatically G-invariant.
-/

section ForwardDirection

variable (X G : Type*) [Fintype X] [DecidableEq X] [Fintype G] [Group G] [MulAction G X]

/-- ### Kramer-Mesner Construction

Given a non-negative integer solution to the Kramer-Mesner system, construct a t-design. -/
noncomputable def tDesignOfKMCondition (t k : ℕ) (l : ℕ)
    (hvk' : k < Fintype.card X ∧ t ≤ k)
    (z : Matrix (Fin 1) {O : jOrbits X G // orbitCard O = k} ℤ) (hz : ∀ O, 0 ≤ z 0 O)
    (km : KramerMesnerCondition X G t k l z) :
    let ms := Finset.sum (Finset.univ : Finset {O : jOrbits X G // orbitCard O = k})
      (fun O => (z 0 O).natAbs • (orbit_blocks O));
    let ι := ms.ToType;
    TDesign ι X t k l where
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
    rcases (Multiset.mem_sum
            (s := (Finset.univ : Finset {O : jOrbits X G // orbitCard O = k}))
            (m := fun O ↦ (z 0 O).natAbs • orbit_blocks O)
            (a := (i.fst : Finset X))).mp hi_mem with ⟨O, -, hO⟩
    have hS_in : (i.fst : Finset X) ∈ orbit_blocks O := Multiset.mem_of_mem_nsmul hO
    have hquot : (⟦(i.fst : Finset X)⟧ : jOrbits X G) = O.val := ((Multiset.mem_filter).1 hS_in).2
    have h_eq : orbitCard (⟦(i.fst : Finset X)⟧ : jOrbits X G) = (k : ℤ) := by
      simp [hquot]; exact O.property
    exact Int.ofNat.inj (by simpa [orbitCard] using h_eq)
  balance := by
    intro s hs
    set ms := Finset.sum (Finset.univ : Finset {O : jOrbits X G // orbitCard O = k})
      (fun O => (z 0 O).natAbs • (orbit_blocks O))
    let Ot : {O : jOrbits X G // orbitCard O = t} :=
      ⟨⟦s⟧, by rw [orbitCard, Quotient.lift_mk]; exact congrArg Nat.cast hs⟩
    have key_eq : (z * (KMat X G k t)) 0 Ot = l := by
      unfold KramerMesnerCondition at km
      rw [← Matrix.ext_iff] at km
      simpa [allOnes, Matrix.smul_apply, nsmul_eq_mul] using km 0 Ot
    symm
    rw [Mathlib.Tactic.Zify.natCast_eq]
    calc
      ↑l = ∑ O, z 0 O * ↑(countSubsetOrbit X G ↑O ↑Ot) := key_eq.symm
      _ = ∑ O, ((z 0 O).natAbs : ℤ) *
            ↑((orbit_blocks O).filter (fun S : Finset X ↦ s ⊆ S)).card := by
        congr 1; ext O
        rw [Int.natAbs_of_nonneg (hz O)]; congr 1
        unfold countSubsetOrbit; rw [Quotient.lift_mk]; unfold orbit_blocks
        simp only [Nat.cast_inj, ← Finset.filter_val, card_val]
        congr 1; ext a; simp only [mem_filter, mem_univ, true_and]
      _ = ↑(ms.filter (fun S => s ⊆ S)).card := by
        classical
        have h_nat : (ms.filter (fun S : Finset X ↦ s ⊆ S)).card =
            ∑ O : {O : jOrbits X G // orbitCard O = k},
              (z 0 O).natAbs * ((orbit_blocks O).filter (fun S : Finset X ↦ s ⊆ S)).card := by
          let p : Finset X → Prop := fun S ↦ s ⊆ S
          have h : ∀ T : Finset {O : jOrbits X G // orbitCard O = k},
              ((Finset.sum T (fun O ↦ (z 0 O).natAbs • orbit_blocks O)).filter p).card =
                  ∑ O ∈ T, (z 0 O).natAbs * ((orbit_blocks O).filter p).card := by
            intro T
            refine Finset.induction (by simp) ?hstep T
            intro a T haT hIH
            have h1 : (((z 0 a).natAbs • orbit_blocks a).filter p).card =
                (z 0 a).natAbs * ((orbit_blocks a).filter p).card := by
              simp [Multiset.filter_nsmul, Multiset.card_nsmul]
            simp [Finset.sum_insert haT, Multiset.filter_add, Multiset.card_add, h1, hIH]
          simpa [p, ms] using h Finset.univ
        simpa using congrArg (fun n : ℕ ↦ (n : ℤ)) h_nat.symm
      _ = ↑(#{i | s ⊆ multiset_to_function ms i}) := by
        congr 1; exact card_filter_multiset_eq_card_filter_indexed ms (Subset s)

/-- Each orbit is invariant under the group action: g • (orbit O) = orbit O. -/
lemma orbit_blocks_map_smul (g : G) {k : ℤ} (O : {O : jOrbits X G // orbitCard O = k}) :
    (orbit_blocks O).map (g • ·) = orbit_blocks O := by
  unfold orbit_blocks
  ext S
  have h_count : Multiset.count S (Multiset.map (g • ·)
      (Multiset.filter (fun S => ⟦S⟧ = O.val) (Finset.univ : Finset (Finset X)).val)) =
      Multiset.count (g⁻¹ • S) (Multiset.filter (fun S => ⟦S⟧ = O.val) Finset.univ.val) := by
    conv_lhs => rw [show S = g • (g⁻¹ • S) by simp]
    exact Multiset.count_map_eq_count' (f := (g • · : Finset X → Finset X))
      (Multiset.filter (fun S => ⟦S⟧ = O.val) Finset.univ.val) (MulAction.injective g) (g⁻¹ • S)
  rw [h_count]
  simp only [Multiset.count_filter,
    Quotient.sound (s := orbitRel G (Finset X)) ⟨g⁻¹, rfl⟩,
    Multiset.count_eq_one_of_mem Finset.univ.nodup (Finset.mem_univ _)]

/-- The design constructed from a KM solution is G-invariant. -/
theorem tDesignOfKMCondition_isGInvariant (t k : ℕ) (l : ℕ)
    (hvk' : k < Fintype.card X ∧ t ≤ k)
    (z : Matrix (Fin 1) {O : jOrbits X G // orbitCard O = k} ℤ) (hz : ∀ O, 0 ≤ z 0 O)
    (km : KramerMesnerCondition X G t k l z) :
    let ms := Finset.sum (Finset.univ : Finset {O : jOrbits X G // orbitCard O = k})
      (fun O => (z 0 O).natAbs • (orbit_blocks O))
    let D := tDesignOfKMCondition X G t k l hvk' z hz km
    IsGInvariant ms.ToType X G D.toIncompleteDesign.toBlockDesign.toDesign := by
  intro ms D g
  simp only [tDesignOfKMCondition, D]
  have h_lhs : (Finset.univ : Finset ms.ToType).val.map (multiset_to_function ms) = ms :=
    Multiset.map_univ_coe ms
  have h_rhs : (Finset.univ : Finset ms.ToType).val.map (fun i => g • multiset_to_function ms i) =
      ms.map (g • ·) := by
    conv_lhs => rw [show (fun i => g • multiset_to_function ms i) =
           (fun x => g • x) ∘ (multiset_to_function ms) from rfl]
    rw [← Multiset.map_map]
    exact congrArg (Multiset.map fun x => g • x) h_lhs
  rw [h_lhs, h_rhs]
  have h_inv : ms.map (g • ·) = ms := by
    calc ms.map (g • ·) = (∑ O, (z 0 O).natAbs • orbit_blocks O).map (g • ·) := rfl
      _ = ∑ O, ((z 0 O).natAbs • orbit_blocks O).map (g • ·) := by
          rw [← Multiset.mapAddMonoidHom_apply, map_sum]; rfl
      _ = ∑ O, (z 0 O).natAbs • (orbit_blocks O).map (g • ·) := by
          congr 1; ext O; rw [Multiset.map_nsmul]
      _ = ∑ O, (z 0 O).natAbs • orbit_blocks O := by simp only [orbit_blocks_map_smul]
      _ = ms := rfl
  exact h_inv.symm

end ForwardDirection

/-!
## Converse Direction: G-invariant Designs Yield Kramer-Mesner Solutions

Given a G-invariant t-(v,k,λ) design, the orbit multiplicities form a non-negative
integer solution to the Kramer-Mesner system.
-/

section ConverseDirection

variable (ι X G : Type*) [Fintype X] [Fintype ι] [DecidableEq X] [DecidableEq ι]
  [Fintype G] [Group G] [MulAction G X]

/-- The solution vector extracted from a G-invariant design -/
noncomputable def solutionFromDesign {t k l : ℕ} (D : TDesign ι X t k l)
    (hD : IsGInvariant ι X G D.toDesign) :
    Matrix (Fin 1) {O : jOrbits X G // orbitCard O = k} ℤ :=
  Matrix.of (fun _ O => (orbitMultiplicity ι X G D.toDesign hD O.val : ℤ))

omit [DecidableEq ι] [Fintype G] in
/-- The solution from a G-invariant design is non-negative -/
lemma solutionFromDesign_nonneg {t k l : ℕ} (D : TDesign ι X t k l)
    (hD : IsGInvariant ι X G D.toDesign)
    (O : {O : jOrbits X G // orbitCard O = k}) :
    0 ≤ solutionFromDesign ι X G D hD 0 O := by
  unfold solutionFromDesign
  simp only [Matrix.of_apply]
  exact Int.natCast_nonneg (orbitMultiplicity ι X G D.toDesign hD ↑O)

omit [DecidableEq ι] in
/-- Summing blockMultiplicity over k-sets containing T equals the number of blocks containing T -/
lemma sum_blockMultiplicity_eq_card {t k l : ℕ} (D : TDesign ι X t k l) (T : Finset X) :
    ∑ S : Finset X, (if T ⊆ S then blockMultiplicity ι X D.toDesign S else 0) =
    #{i : ι | T ⊆ D.blocks i} := by
  classical
  simp_rw [blockMultiplicity_eq_card]
  have h1 : ∀ i : ι, T ⊆ D.blocks i →
      ∑ S : Finset X, (if T ⊆ S then (if D.blocks i = S then 1 else 0) else 0) = 1 := by
    intro i hi
    rw [Finset.sum_eq_single (D.blocks i)]
    · simp [hi]
    · intro S _ hS; simp [hS.symm]
    · intro h; exact absurd (Finset.mem_univ _) h
  have h2 : ∀ i : ι, ¬T ⊆ D.blocks i →
      ∑ S : Finset X, (if T ⊆ S then (if D.blocks i = S then 1 else 0) else 0) = 0 := by
    intro i hi
    apply Finset.sum_eq_zero; intro S _
    by_cases hTS : T ⊆ S
    · simp only [hTS, ↓reduceIte]
      by_cases heq : D.blocks i = S
      · exact absurd (heq ▸ hTS) hi
      · simp [heq]
    · simp [hTS]
  calc ∑ S : Finset X, (if T ⊆ S then #{i : ι | D.blocks i = S} else 0)
      = ∑ S : Finset X, (if T ⊆ S then ∑ i : ι, (if D.blocks i = S then 1 else 0) else 0) := by
        congr 1; ext S
        split_ifs with hTS
        · rw [Finset.card_eq_sum_ones, Finset.sum_filter]
        · rfl
    _ = ∑ S : Finset X, ∑ i : ι, (if T ⊆ S then (if D.blocks i = S then 1 else 0) else 0) := by
        congr 1; ext S
        split_ifs with hTS
        · rfl
        · simp
    _ = ∑ i : ι, ∑ S : Finset X, (if T ⊆ S then (if D.blocks i = S then 1 else 0) else 0) := by
        rw [Finset.sum_comm]
    _ = ∑ i : ι, (if T ⊆ D.blocks i then 1 else 0) := by
        congr 1; ext i
        by_cases hi : T ⊆ D.blocks i
        · rw [if_pos hi, h1 i hi]
        · rw [if_neg hi, h2 i hi]
    _ = #{i : ι | T ⊆ D.blocks i} := by
        rw [Finset.card_eq_sum_ones, Finset.sum_filter]

omit [DecidableEq ι] [Fintype G] in
/-- A G-invariant t-(v,k,λ) design yields a non-negative integer solution to the KM system. -/
theorem kmConditionOfGInvariantDesign {t k l : ℕ} (D : TDesign ι X t k l)
    (hD : IsGInvariant ι X G D.toDesign) :
    KramerMesnerCondition X G t k l (solutionFromDesign ι X G D hD) := by
  unfold KramerMesnerCondition
  ext i Ot
  simp only [Matrix.mul_apply, Matrix.smul_apply, nsmul_eq_mul, allOnes,
    Matrix.of_apply, mul_one]
  obtain ⟨T, hT⟩ := Quotient.exists_rep Ot.val
  have hTOt : Ot.val = ⟦T⟧ := hT.symm
  have hTcard : #T = t := by
    have : orbitCard (X := X) (G := G) ⟦T⟧ = t := by rw [hT]; exact Ot.property
    simp only [orbitCard, Quotient.lift_mk] at this
    exact Int.ofNat_inj.mp this
  have h_balance : #{i : ι | T ⊆ D.blocks i} = l := D.balance T hTcard
  have h_uniform : ∀ j : ι, #(D.blocks j) = k := D.uniform
  have h_block_orbit : ∀ j : ι, orbitCard (X := X) (G := G) ⟦D.blocks j⟧ = k := by
    intro j; simp only [orbitCard, Quotient.lift_mk]; exact congrArg Nat.cast (h_uniform j)
  simp only [solutionFromDesign, KMat, Matrix.of_apply]
  rw [hTOt]
  suffices h : (∑ O : {O : jOrbits X G // orbitCard O = k},
      orbitMultiplicity ι X G D.toDesign hD O.val * countSubsetOrbit X G O.val ⟦T⟧ : ℕ) = l by
    have step1 : ∀ O : {O : jOrbits X G // orbitCard O = k},
        (orbitMultiplicity ι X G D.toDesign hD O.val : ℤ) * (countSubsetOrbit X G O.val ⟦T⟧ : ℤ) =
        ((orbitMultiplicity ι X G D.toDesign hD O.val * countSubsetOrbit X G O.val ⟦T⟧ : ℕ) : ℤ) := by
      intro O; exact (Nat.cast_mul _ _).symm
    simp only [step1, ← Nat.cast_sum, h]
  conv_rhs => rw [← h_balance]
  rw [← sum_blockMultiplicity_eq_card ι X D T]
  have h_nonk_zero : ∀ S : Finset X, #S ≠ k → blockMultiplicity ι X D.toDesign S = 0 := by
    intro S hS
    unfold blockMultiplicity
    rw [Multiset.count_eq_zero]
    intro hSmem
    rw [Multiset.mem_map] at hSmem
    obtain ⟨j, _, hj⟩ := hSmem
    exact hS (by rw [← hj]; exact h_uniform j)
  have h_const : ∀ O : {O : jOrbits X G // orbitCard O = k}, ∀ S : Finset X,
      (⟦S⟧ : jOrbits X G) = O.val →
      blockMultiplicity ι X D.toDesign S = orbitMultiplicity ι X G D.toDesign hD O.val := by
    intro O S hS; rw [← hS]
    exact (orbitMultiplicity_eq_blockMultiplicity ι X G D.toDesign hD S).symm
  calc ∑ O : {O : jOrbits X G // orbitCard O = k},
        orbitMultiplicity ι X G D.toDesign hD O.val * countSubsetOrbit X G O.val ⟦T⟧
      = ∑ O : {O : jOrbits X G // orbitCard O = k},
          orbitMultiplicity ι X G D.toDesign hD O.val *
          #{S : Finset X | (⟦S⟧ : jOrbits X G) = O.val ∧ T ⊆ S} := by
        apply Finset.sum_congr rfl
        intro O _
        rw [countSubsetOrbit_eq_card]
    _ = ∑ O : {O : jOrbits X G // orbitCard O = k},
          ∑ S ∈ Finset.filter (fun S => (⟦S⟧ : jOrbits X G) = O.val ∧ T ⊆ S) Finset.univ,
            orbitMultiplicity ι X G D.toDesign hD O.val := by
        congr 1; ext O
        rw [Finset.sum_const, smul_eq_mul, mul_comm]
    _ = ∑ O : {O : jOrbits X G // orbitCard O = k},
          ∑ S ∈ Finset.filter (fun S => (⟦S⟧ : jOrbits X G) = O.val ∧ T ⊆ S) Finset.univ,
            blockMultiplicity ι X D.toDesign S := by
        congr 1; ext O
        apply Finset.sum_congr rfl
        intro S hS
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hS
        exact (h_const O S hS.1).symm
    _ = ∑ S ∈ Finset.filter (fun S => T ⊆ S ∧ orbitCard (X := X) (G := G) ⟦S⟧ = k) Finset.univ,
          blockMultiplicity ι X D.toDesign S := by
        rw [← Finset.sum_biUnion]
        · apply Finset.sum_congr _ (fun _ _ => rfl)
          ext S
          simp only [Finset.mem_biUnion, Finset.mem_univ, Finset.mem_filter, true_and,
            Subtype.exists, exists_prop]
          constructor
          · intro ⟨O, hO, hSO, hTS⟩
            exact ⟨hTS, by rw [hSO]; exact hO⟩
          · intro ⟨hTS, hSk⟩
            exact ⟨⟦S⟧, hSk, rfl, hTS⟩
        · intro O₁ _ O₂ _ hne
          simp only [Function.onFun]
          rw [Finset.disjoint_left]
          intro S hS1 hS2
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hS1 hS2
          exact hne (Subtype.ext (hS1.1.symm.trans hS2.1))
    _ = ∑ S : Finset X, (if T ⊆ S then blockMultiplicity ι X D.toDesign S else 0) := by
        rw [Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro S _
        by_cases hTS : T ⊆ S
        · simp only [hTS, ↓reduceIte]
          by_cases hSk : #S = k
          · have hOrbitCard : orbitCard (X := X) (G := G) ⟦S⟧ = k := by
              simp only [orbitCard, Quotient.lift_mk]; exact congrArg Nat.cast hSk
            simp only [hOrbitCard, and_self, ↓reduceIte]
          · simp only [h_nonk_zero S hSk]
            have hOrbitCard : orbitCard (X := X) (G := G) ⟦S⟧ ≠ k := by
              simp only [orbitCard, Quotient.lift_mk, ne_eq]
              exact fun h => hSk (Int.ofNat_inj.mp h)
            simp only [hOrbitCard, and_false, ↓reduceIte]
        · simp only [hTS, false_and, ↓reduceIte]

end ConverseDirection

universe u

variable (X G : Type u) [Fintype X] [DecidableEq X] [Fintype G] [Group G] [MulAction G X]

/-- **Kramer-Mesner Theorem**: A G-invariant t-(v,k,λ) design exists if and only if
    there exists a non-negative integer solution to the Kramer-Mesner system z * A(k,t) = λ * 1. -/
theorem kramerMesner_iff (t k l : ℕ) (hvk' : k < Fintype.card X ∧ t ≤ k) :
    (∃ (ι : Type u) (_ : Fintype ι) (_ : DecidableEq ι) (D : TDesign ι X t k l),
      IsGInvariant ι X G D.toDesign) ↔
    (∃ z : Matrix (Fin 1) {O : jOrbits X G // orbitCard O = k} ℤ,
      (∀ O, 0 ≤ z 0 O) ∧ KramerMesnerCondition X G t k l z) := by
  constructor
  · intro ⟨ι, _, _, D, hD⟩
    exact ⟨solutionFromDesign ι X G D hD, solutionFromDesign_nonneg ι X G D hD,
           kmConditionOfGInvariantDesign ι X G D hD⟩
  · intro ⟨z, hz, km⟩
    set ms := Finset.sum (Finset.univ : Finset {O : jOrbits X G // orbitCard O = k})
      (fun O => (z 0 O).natAbs • (orbit_blocks O))
    exact ⟨ms.ToType, inferInstance, Classical.typeDecidableEq _,
           tDesignOfKMCondition X G t k l hvk' z hz km,
           tDesignOfKMCondition_isGInvariant X G t k l hvk' z hz km⟩

/-- **Kramer-Mesner Theorem for BIBD**: A G-invariant 2-(v,k,λ) design (BIBD) exists iff
    there exists a non-negative integer solution to z * A(k,2) = λ * 1. -/
theorem kramerMesner_BIBD_iff (k l : ℕ) (hvk' : k < Fintype.card X ∧ 2 ≤ k) :
    (∃ (ι : Type u) (_ : Fintype ι) (_ : DecidableEq ι) (D : BIBD ι X k l),
      IsGInvariant ι X G D.toDesign) ↔
    (∃ z : Matrix (Fin 1) {O : jOrbits X G // orbitCard O = k} ℤ,
      (∀ O, 0 ≤ z 0 O) ∧ KramerMesnerCondition X G 2 k l z) := kramerMesner_iff X G 2 k l hvk'
