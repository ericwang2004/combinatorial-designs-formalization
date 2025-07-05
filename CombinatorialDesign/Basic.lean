import CombinatorialDesign.Defs

open Finset CombinatorialDesign
namespace CombinatorialDesign

variable {ι X} [Fintype X] [Fintype ι] [DecidableEq X] {k l : ℕ} (Φ : BIBD ι X k l)

theorem v_pos_of_bibd (Φ : BIBD ι X k l) : Fintype.card X > 0 :=
  lt_of_le_of_lt Φ.hvk.2 Φ.hvk.1 |> lt_trans Nat.zero_lt_two

theorem k_pos_of_bibd (Φ : BIBD ι X k l) : k > 0 :=
  Nat.zero_lt_of_lt Φ.hvk.2

theorem v_ge_two_of_nontrivialRPBD {r : ℕ} (Ψ : nontrivialRPBD ι X l r) : Fintype.card X ≥ 2 := by
  obtain ⟨i, hi₁, hi₂⟩ := Ψ.nontrivial
  refine (Nat.two_le_iff (Fintype.card X)).mpr ?_
  constructor
  · exact Nat.ne_zero_of_lt hi₂
  · rintro p
    simp_all only [card_pos, Nat.lt_one_iff, card_eq_zero, Finset.not_nonempty_empty]

theorem v_pos_of_nontrivialRPBD {r : ℕ} (Ψ : nontrivialRPBD ι X l r) : Fintype.card X > 0 :=
  v_ge_two_of_nontrivialRPBD Ψ |> Nat.zero_lt_of_lt

theorem v_ge_one_of_nontrivialRPBD {r : ℕ} (Ψ : nontrivialRPBD ι X l r) : Fintype.card X ≥ 1 :=
  v_ge_two_of_nontrivialRPBD Ψ |> Nat.one_le_of_lt

theorem r_pos_of_nontrivialRPBD {r : ℕ} (Ψ : nontrivialRPBD ι X l r) : r > 0 := by
  obtain ⟨i, hi, _⟩ := Ψ.nontrivial
  obtain ⟨x, hx⟩ := card_pos.mp hi
  rw [←Ψ.regularity x, gt_iff_lt, card_pos]
  use i
  simp only [mem_filter, mem_univ, true_and, hx]

def rep_elem (x : X) := #{i | x ∈ Φ.blocks i}

theorem card_dependent {α β} [Fintype α] [Fintype β]
    (P : α → Prop) [DecidablePred P]
    (Q : α → β → Prop) [∀ x, DecidablePred (Q x)]
    {k : ℕ} (hk : ∀ x, P x → #{y | Q x y} = k) :
    #{(x, y) | P x ∧ Q x y} = k * #{x | P x} := by
  let g x (hx : P x) : { y // Q x y } ≃ Fin k := by
    rw [←hk x hx]
    apply Fintype.equivFinOfCardEq
    apply Fintype.card_of_subtype
    intro y
    simp only [mem_filter, mem_univ, true_and]
  let J : Finset (Fin k × α) := Finset.product univ {x | P x}
  have sizeJ : #J = k * #{x | P x} := by calc
    _ = _ := by apply Finset.card_product
    _ = _ := by rw [card_fin k]
  rw [←sizeJ]
  apply card_bij (fun (x, y) hxy ↦ by
    simp only [mem_filter, mem_univ, true_and] at hxy
    exact (g x hxy.1 ⟨y, hxy.2⟩, x)
  )
  · intro ⟨x, y⟩ hxy
    simp only [mem_filter, mem_univ, true_and] at hxy
    exact mem_product.mpr ⟨by apply mem_univ,
      by simp only [mem_filter, mem_univ, true_and]; exact hxy.1⟩
  · intro ⟨x₁, y₁⟩ hxy₁ ⟨x₂, y₂⟩ hxy₂
    simp only [mem_filter, mem_univ, true_and] at hxy₁ hxy₂
    simp only [Prod.mk.injEq, and_imp]
    exact fun hg xeq ↦
      ⟨xeq, by subst xeq; simp_all only [EmbeddingLike.apply_eq_iff_eq, Subtype.mk.injEq]⟩
  · intro ⟨i, x⟩ hJ
    have hx : P x := (mem_filter.mp (mem_product.mp hJ).2).2
    use (x, (g x hx).symm i)
    simp only [Subtype.coe_eta, Equiv.apply_symm_apply, mem_filter, mem_univ, true_and, exists_prop,
      and_true]
    exact ⟨hx, ((g x hx).symm i).property⟩

theorem card_of_swap {α β} [Fintype α] [Fintype β]
    {P : α → β → Prop} [∀ x, DecidablePred (P x)]
    {Q : β → α → Prop} [∀ y, DecidablePred (Q y)]
    (hPQ : ∀ x y, P x y ↔ Q y x) :
    #{(x, y) | P x y} = #{(y, x) | Q y x} := by
  apply card_bij (fun (x, y) _ ↦ (y, x))
  · intro ⟨x, y⟩ hxy
    simp only [mem_filter, mem_univ, true_and] at hxy ⊢
    exact (hPQ _ _).1 hxy
  · intro ⟨x₁, y₁⟩ hxy₁ ⟨x₂, y₂⟩ hxy₂
    simp only [mem_filter, mem_univ, true_and] at hxy₁ hxy₂
    simp only [Prod.mk.injEq, and_imp]
    exact fun hy hx ↦ ⟨hx, hy⟩
  · intro ⟨x, y⟩ hxy
    simp only [mem_filter, mem_univ, true_and] at hxy
    use ⟨y, x⟩
    simp only [mem_filter, mem_univ, true_and, exists_prop, and_true]
    exact (hPQ _ _).2 hxy

theorem rep_constant : ∀ x, (k - 1) * rep_elem Φ x = l * ((Fintype.card X) - 1) := by
  intro x
  let P₁ : X → Prop := fun y ↦ x ≠ y
  let Q₁ : X → ι → Prop := fun y i ↦ x ∈ Φ.blocks i ∧ y ∈ Φ.blocks i
  have aux₁ : ∀ y, P₁ y → #{i | Q₁ y i} = l := Φ.balance x
  have count₁ := card_dependent P₁ Q₁ aux₁
  let P₂ : ι → Prop := fun i ↦ x ∈ Φ.blocks i
  let Q₂ : ι → X → Prop := fun i y ↦ x ≠ y ∧ y ∈ Φ.blocks i
  have : ∀ i, filter (fun y ↦ Q₂ i y) univ = (Φ.blocks i).erase x := by
    intro i; ext y
    constructor
    · intro hy
      simp only [mem_filter, mem_univ, true_and] at hy
      exact mem_erase.mpr ⟨Ne.symm hy.1, hy.2⟩
    · intro hy
      simp only [mem_filter, mem_univ, true_and]
      rw [mem_erase] at hy
      exact ⟨Ne.symm hy.1, hy.2⟩
  have aux₂ : ∀ i, P₂ i → #{y | Q₂ i y} = k - 1 := by
    intro i hi
    rw [this, card_erase_of_mem hi, Φ.hA i]
  have count₂ := card_dependent P₂ Q₂ aux₂
  have : #(filter P₁ univ) = (Fintype.card X) - 1 := by
    rw [filter_ne _ _]
    simp only [mem_univ, card_erase_of_mem, card_univ]
  have swap_condition : ∀ y i, P₁ y ∧ Q₁ y i ↔ P₂ i ∧ Q₂ i y := by tauto
  rwa [card_of_swap swap_condition, count₂, this] at count₁

noncomputable def rep [Inhabited X] (Φ : BIBD ι X k l) : ℕ := by
  let x : X := Classical.choice instNonemptyOfInhabited
  exact rep_elem Φ x

theorem rep_property [Inhabited X] (Φ : BIBD ι X k l) :
    (k - 1) * rep Φ =  l * ((Fintype.card X) - 1) := by
  rw [rep, rep_constant]

theorem rep_eq_rep_elem [Inhabited X] : ∀ x, rep_elem Φ x = rep Φ := by
  intro x
  have h := rep_constant Φ x
  rw [←rep_property Φ] at h
  exact Nat.eq_of_mul_eq_mul_left (Nat.zero_lt_sub_of_lt Φ.hvk.2) h

theorem rep_elem_eq_rep_elem : ∀ x y, rep_elem Φ x = rep_elem Φ y := by
  intro x y
  have h := rep_constant Φ x
  rw [←rep_constant Φ y] at h
  exact Nat.eq_of_mul_eq_mul_left (Nat.zero_lt_sub_of_lt Φ.hvk.2) h

theorem blocks_constant : ∀ x, k * (Fintype.card ι) = rep_elem Φ x * (Fintype.card X) := by
  intro x
  let P₁ : X → Prop := fun _ ↦ True
  let Q₁ : X → ι → Prop := fun x i ↦ x ∈ Φ.blocks i
  have aux₁ : ∀ y, P₁ y → #{i | Q₁ y i} = rep_elem Φ x :=
    fun y _ ↦ by rw [rep_elem_eq_rep_elem]; rfl
  have count₁ := card_dependent P₁ Q₁ aux₁
  let P₂ : ι → Prop := fun _ ↦ True
  let Q₂ : ι → X → Prop := fun i x ↦ x ∈ Φ.blocks i
  have aux₂ : ∀ i, P₂ i → #{y | Q₂ i y} = k :=
    fun i _ ↦ by simp only [filter_univ_mem, Q₂]; exact Φ.hA i
  have count₂ := card_dependent P₂ Q₂ aux₂
  have swap_condition : ∀ y i, P₁ y ∧ Q₁ y i ↔ P₂ i ∧ Q₂ i y := by tauto
  rw [card_of_swap swap_condition, count₂] at count₁
  have : #(filter P₂ univ) = Fintype.card ι := by rw [filter_True, card_univ]
  rw [this] at count₁
  have : #(filter P₁ univ) = Fintype.card X := by rw [filter_True, card_univ]
  rwa [this] at count₁

theorem kb_eq_repv [Inhabited X] : k * (Fintype.card ι) = rep Φ * (Fintype.card X) := by
  let x : X := Classical.choice instNonemptyOfInhabited
  rw [blocks_constant _ x, rep_eq_rep_elem]

theorem b_eq_v_iff_rep_eq_k [Inhabited X] : (Fintype.card ι) = (Fintype.card X) ↔ rep Φ = k := by
  have aux := kb_eq_repv Φ
  constructor <;> intro h
  · have hb : Fintype.card ι > 0 := by
      rw [h]; exact v_pos_of_bibd Φ
    rw [← h] at aux
    exact Nat.eq_of_mul_eq_mul_right hb aux.symm
  · rw [h] at aux
    exact Nat.eq_of_mul_eq_mul_left (k_pos_of_bibd Φ) aux

theorem eq_of_symmBIBD [Inhabited X] (Φ : BIBD X X k l) : l * ((Fintype.card X) - 1) = k * (k - 1) := by
  rw [←rep_property Φ, (b_eq_v_iff_rep_eq_k Φ).mp rfl, mul_comm]

/-- Useful coercions --/
--A BBD is also a Design
def BBD_to_Design : (BBD ι X l) → (Design ι X) := BBD.toDesign

--A RPBD is also a BBD
def RPBD_to_BBD : (r : ℕ) → (RPBD ι X l r) → (BBD ι X l) := fun _ ↦ RPBD.toBBD

--Thus, a RPBD is also a Design
def RPBD_to_Design : (r : ℕ) → (RPBD ι X l r) → (Design ι X) :=
  fun r ↦ BBD_to_Design ∘ (RPBD_to_BBD r)

--A BIBD is also a BBD
def BIBD_to_BBD : (BIBD ι X k l) → (BBD ι X l) := BIBD.toBBD

--A BIBD is also a Design
def BIBD_to_Design : (BIBD ι X k l) → (Design ι X) := BBD.toDesign ∘ BIBD.toBBD

--A BIBD is also an RPBD
noncomputable def BIBD_to_RPBD [Inhabited X] (Φ : BIBD ι X k l) :
    (RPBD ι X l (rep Φ)) := by
  constructor
  . exact (rep_eq_rep_elem Φ)

--A nonempty BIBD is also an RPBD
 noncomputable def BIBD_to_nontrivialRPBD [Inhabited X] (Φ : BIBD ι X k l) (i : ι) :
    (nontrivialRPBD ι X l (rep Φ)) where
  toRPBD := by
    constructor; swap
    · exact Φ.toBBD
    · apply rep_eq_rep_elem
  nontrivial := by
    use i
    simp only [Φ.hA]
    exact ⟨lt_of_le_of_lt' Φ.hvk.2 Nat.zero_lt_two, Φ.hvk.1⟩


end CombinatorialDesign
