import BalancedIncompleteBlockDesign.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FinCases

open BalancedIncompleteBlockDesign
open Finset

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
def fanoPlane : BIBD (Fin 7) 7 7 3 1 := {
  blocks := fun i ↦ match i with
    | 0 => {0, 1, 2}
    | 1 => {2, 4, 5}
    | 2 => {5, 6, 0}
    | 3 => {0, 3, 4}
    | 4 => {1, 3, 5}
    | 5 => {2, 3, 6}
    | 6 => {1, 4, 6}
  hvk := by norm_num
  hX := rfl
  hA := fun i ↦ by fin_cases i; all_goals decide
  balance := fun x y _ ↦ by fin_cases x, y; all_goals trivial
}
