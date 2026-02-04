import CombinatorialDesign.Basic
import CombinatorialDesign.Isomorphism
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

end CombinatorialDesign
