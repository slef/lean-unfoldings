module

public import Unfoldings.Geometry.HeadingChordError
public import Unfoldings.Geometry.ComplexRotation

/-! Actual hinge-fixed suffix rotations retain translations and all original bank link lengths. -/

@[expose] public section

noncomputable section

namespace Unfoldings.PolygonalChain

variable {n : ℕ} (P : PolygonalChain ℂ n)

/-- Rotate the actual suffix around its current hinge, keeping the preceding bank fixed. -/
def rotateSuffix (hinge : Fin (n + 1)) (angle : ℝ) : PolygonalChain ℂ n where
  vertex i := if i ≤ hinge then P.vertex i else
    P.vertex hinge + complexRotation angle (P.vertex i - P.vertex hinge)

theorem rotateSuffix_vertex_le (hinge : Fin (n + 1)) (angle : ℝ) (i : Fin (n + 1))
    (before : i ≤ hinge) : (P.rotateSuffix hinge angle).vertex i = P.vertex i := by
  exact ite_eq_left before

theorem rotateSuffix_vertex_ge (hinge : Fin (n + 1)) (angle : ℝ) (i : Fin (n + 1))
    (after : hinge ≤ i) : (P.rotateSuffix hinge angle).vertex i =
      P.vertex hinge + complexRotation angle (P.vertex i - P.vertex hinge) := by
  by_cases same : i = hinge
  · subst i
    simp [rotateSuffix]
  · exact ite_eq_right (fun before => same (le_antisymm before after))

theorem rotateSuffix_start (hinge : Fin (n + 1)) (angle : ℝ) :
    (P.rotateSuffix hinge angle).vertex 0 = P.vertex 0 :=
  P.rotateSuffix_vertex_le hinge angle 0 (Fin.zero_le _)

/-- The hinge translation is retained, while every later edge is rotated by its true angle. -/
theorem rotateSuffix_edge (hinge : Fin (n + 1)) (angle : ℝ) (i : Fin n) :
    (P.rotateSuffix hinge angle).edge i =
      polarRay (if hinge ≤ i.castSucc then angle else 0) * P.edge i := by
  by_cases after : hinge ≤ i.castSucc
  · rw [ite_eq_left after]
    change (P.rotateSuffix hinge angle).vertex i.succ -
      (P.rotateSuffix hinge angle).vertex i.castSucc = _
    rw [P.rotateSuffix_vertex_ge hinge angle i.succ (after.trans (Fin.castSucc_le_succ i)),
      P.rotateSuffix_vertex_ge hinge angle i.castSucc after]
    simp only [complexRotation_apply, edge]
    ring
  · rw [ite_eq_right after, polarRay_zero, one_mul]
    have before : i.succ ≤ hinge := by
      have strict := lt_of_not_ge after
      change i.val < hinge.val at strict
      change i.val + 1 ≤ hinge.val
      omega
    change (P.rotateSuffix hinge angle).vertex i.succ -
      (P.rotateSuffix hinge angle).vertex i.castSucc = _
    rw [P.rotateSuffix_vertex_le hinge angle i.succ before,
      P.rotateSuffix_vertex_le hinge angle i.castSucc
        ((Fin.castSucc_le_succ i).trans before)]
    rfl

theorem rotateSuffix_length (hinge : Fin (n + 1)) (angle : ℝ) :
    (P.rotateSuffix hinge angle).projectedLength = P.projectedLength :=
  P.projectedLength_eq_of_rotated_edges (P.rotateSuffix hinge angle)
    (fun i => if hinge ≤ i.castSucc then angle else 0) (P.rotateSuffix_edge hinge angle)

/-- One opening record remembers the actual hinge index and its real, unreduced rotation. -/
structure Opening (n : ℕ) where
  hinge : Fin (n + 1)
  angle : ℝ

def openings (events : List (Opening n)) : PolygonalChain ℂ n :=
  events.foldl (fun Q event => Q.rotateSuffix event.hinge event.angle) P

/-- Each original link has its exact accumulated real heading correction. -/
def openingHeading (events : List (Opening n)) (i : Fin n) : ℝ :=
  (events.map (fun event => if event.hinge ≤ i.castSucc then event.angle else 0)).sum

theorem openings_edge (events : List (Opening n)) (i : Fin n) :
    (P.openings events).edge i = polarRay (openingHeading events i) * P.edge i := by
  induction events generalizing P with
  | nil => simp [openings, openingHeading]
  | cons event events ih =>
    change ((P.rotateSuffix event.hinge event.angle).openings events).edge i = _
    rw [ih, P.rotateSuffix_edge]
    simp only [openingHeading, List.map_cons, List.sum_cons, polarRay_add]
    ring

theorem openings_length (events : List (Opening n)) :
    (P.openings events).projectedLength = P.projectedLength :=
  P.projectedLength_eq_of_rotated_edges (P.openings events) (openingHeading events)
    (P.openings_edge events)

end Unfoldings.PolygonalChain
