import CombinatorialDesign.Basic
import CombinatorialDesign.Isomorphism
import CombinatorialDesign.SymmetricBIBD
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FinCases

namespace CombinatorialDesign
open CombinatorialDesign Finset

/-  The depiction of Fano Plane; six triples are given via a line,
  and the last one {1,4,6} is specified by a bold font.
     0==0==0
     |  |  |
     |  |  |
     𝟭  |  𝟲
     |\ | /|
     | \|/ |
     |  3  |
     | /|\ |
     |/ | \|
     2--𝟰--5
  For a better depiction, see
  https://en.wikipedia.org/wiki/Fano_plane#/media/File:Fano_plane.svg
-/
def fanoPlane : BIBD (Fin 7) (Fin 7) 3 1 := {
  blocks i := match i with
    | 0 => {0, 1, 2}
    | 1 => {2, 4, 5}
    | 2 => {5, 6, 0}
    | 3 => {0, 3, 4}
    | 4 => {1, 3, 5}
    | 5 => {2, 3, 6}
    | 6 => {1, 4, 6}
  incomplete := by norm_num
  t_le_k := by norm_num
  uniform i := by fin_cases i; all_goals trivial
  balance s hs := by fin_cases s; all_goals trivial
}

def fanoPlaneIso : DesignIsomorphism fanoPlane.toDesign fanoPlane.toDesign :=
  let f (i : Fin 7) : Fin 7 := match i with
    | 0 => 0
    | 1 => 1
    | 2 => 2
    | 3 => 4
    | 4 => 3
    | 5 => 6
    | 6 => 5
  let σ (i : Fin 7) : Fin 7 := match i with
    | 0 => 0
    | 1 => 5
    | 2 => 2
    | 3 => 3
    | 4 => 6
    | 5 => 1
    | 6 => 4
  {
  toFun := f
  invFun := f
  left_inv i := by fin_cases i; all_goals trivial
  right_inv i := by fin_cases i; all_goals trivial
  perm := {
    toFun := σ
    invFun := σ
    left_inv i := by fin_cases i; all_goals trivial
    right_inv i := by fin_cases i; all_goals trivial
  }
  map_blocks := by trivial
}

variable {ι X : Type*} [Fintype ι] [Fintype X] [DecidableEq X]

example {a b : ℕ} (h : a < b) : a * a < b * b := by exact Nat.mul_self_lt_mul_self h

/-
 There is no (22, 7, 2)-BIBD
-/
theorem no_22_7_2_BIBD (hv : Fintype.card X = 22) (Φ : BIBD ι X 7 2) : False := by
  have : Inhabited X := by
    refine Classical.inhabited_of_nonempty ?_
    apply Fintype.card_pos_iff.mp
    rw [hv]
    exact Nat.zero_lt_succ 21
  have repΦ : rep Φ = 7 := by
    have := rep_property Φ
    omega
  have hι : Fintype.card X = Fintype.card ι := by
    have := kb_eq_repv Φ
    rw [repΦ] at this
    omega
  have Φ' := reindexBIBD (Equiv.refl X) (Fintype.equivOfCardEq hι) Φ
  obtain ⟨n, hn⟩ := bruck_ryser_chowla_even (by rw [hv]; use 11) Φ'
  simp only [Nat.reduceSub] at hn
  have boundn : n ≤ 3 := by
    by_contra hn'
    rw [not_le] at hn'
    have aux := Nat.mul_self_lt_mul_self hn'
    omega
  interval_cases n <;> omega

end CombinatorialDesign
