module

public import Unfoldings.Cap.RestrictedStraightTurns
public import Unfoldings.Polyhedron.BoundaryDirections
public import Unfoldings.Cap.SectionAngles

/-!
# Actual straight boundary sections

A trace records only the actual directed bank adjacency, original folded vertex
positions, and their increasing times on a straight projected section. All fan
angle and turn comparisons are derived, including at flat subdivision vertices.
-/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexCap C)

open Classical in
structure BoundarySectionTrace (U : Set Face) (origin direction : Plane) where
  turns : ℕ
  bank : Fin (turns + 2) → (C.restrictFaces U).BoundaryEnd Set.univ
  next : ∀ i : Fin (turns + 1), (C.restrictFaces U).boundaryMate Set.univ
    ((C.restrictFaces U).boundaryTurn Set.univ (bank i.castSucc)) = bank i.succ
  time : Fin (turns + 2) → ℝ
  increasing : StrictMono time
  position : ∀ i, (K.folding.restrictFaces U).boundaryPosition (bank i) =
    K.roofSectionPoint origin direction (time i)

namespace BoundarySectionTrace

variable {K} {U : Set Face} {origin direction : Plane}
  (T : K.BoundarySectionTrace U origin direction)

open Classical in
def turnError (i : Fin T.turns) : ℝ :=
  let R := C.restrictFaces U
  let w := R.boundaryEndVertex Set.univ (T.bank i.castSucc.succ)
  (Real.pi - R.totalAngle Set.univ w) -
    (Real.pi - R.regionalCornerSum Set.univ
      (fun c => (K.projectedTriangle c.1.val).cornerAngle c.2) w)

open Classical in
theorem outgoing (i : Fin T.turns) :
    (K.folding.restrictFaces U).germDirection (T.bank i.castSucc.succ).val =
      K.roofSectionSecant origin direction T.time i.succ := by
  have step := (K.folding.restrictFaces U).germDirection_boundary_step (T.next i.succ)
  rw [T.position, T.position] at step
  simpa only [ConvexCap.roofSectionSecant, Fin.succ_castSucc] using step

open Classical in
theorem incoming (i : Fin T.turns) :
    (K.folding.restrictFaces U).germDirection
      ((C.restrictFaces U).boundaryMate Set.univ (T.bank i.castSucc.succ)).val =
      -K.roofSectionSecant origin direction T.time i.castSucc := by
  have step := (K.folding.restrictFaces U).germDirection_boundary_incoming (T.next i.castSucc)
  rw [T.position, T.position] at step
  simpa only [ConvexCap.roofSectionSecant, neg_sub] using step

theorem horizontal_secant (i : Fin (T.turns + 1)) :
    Cap.horizontal (K.roofSectionSecant origin direction T.time i) =
      (T.time i.succ - T.time i.castSucc) • direction := by
  rw [ConvexCap.roofSectionSecant, K.roofSectionPoint_sub origin direction
    (T.increasing (show i.castSucc < i.succ from Fin.castSucc_lt_succ)),
    map_smul, Cap.horizontal_horizontalAtHeight]

open Classical in
/-- Literal straightness of the bank positions gives the exact projected halfplane fan. -/
theorem straight (unit : ‖direction‖ = 1) (i : Fin T.turns) :
    InnerProductGeometry.angle
      (Cap.horizontal ((K.folding.restrictFaces U).germDirection (T.bank i.castSucc.succ).val))
      (Cap.horizontal ((K.folding.restrictFaces U).germDirection
        ((C.restrictFaces U).boundaryMate Set.univ (T.bank i.castSucc.succ)).val)) = Real.pi := by
  have genuine : direction ≠ 0 := by intro zero; rw [zero, norm_zero] at unit; norm_num at unit
  rw [T.outgoing, T.incoming, map_neg, T.horizontal_secant, T.horizontal_secant,
    InnerProductGeometry.angle_neg_right,
    InnerProductGeometry.angle_smul_left_of_pos _ _
      (sub_pos.mpr (T.increasing Fin.castSucc_lt_succ)),
    InnerProductGeometry.angle_smul_right_of_pos _ _
      (sub_pos.mpr (T.increasing Fin.castSucc_lt_succ)),
    InnerProductGeometry.angle_self genuine, sub_zero]

open Classical in
/-- Each actual one-sided fan error is no greater than its corresponding actual section bend. -/
theorem abs_turnError_le_spatial (unit : ‖direction‖ = 1) (i : Fin T.turns)
    (internal : ¬ C.IsBoundaryVertex Set.univ
      (C.includeRestrictedVertexUniv U ((C.restrictFaces U).boundaryEndVertex Set.univ
        (T.bank i.castSucc.succ)))) :
    |T.turnError i| ≤ InnerProductGeometry.angle
      (K.roofSectionSecant origin direction T.time i.castSucc)
      (K.roofSectionSecant origin direction T.time i.succ) := by
  have bound := K.abs_restricted_straight_turn_error_le_spatial_bend U
    (T.bank i.castSucc.succ) internal (T.straight unit i)
  simpa only [turnError, T.outgoing, T.incoming, InnerProductGeometry.angle_neg_neg,
    InnerProductGeometry.angle_comm] using bound

open Classical in
/-- The entire closing section costs at most twice the tilt, with no per-vertex charge. -/
theorem sum_abs_turnError_le_tilt (unit : ‖direction‖ = 1)
    (internal : ∀ i : Fin T.turns, ¬ C.IsBoundaryVertex Set.univ
      (C.includeRestrictedVertexUniv U ((C.restrictFaces U).boundaryEndVertex Set.univ
        (T.bank i.castSucc.succ))))
    {φ : ℝ} (nonnegative : 0 ≤ φ) (small : φ < Real.pi / 2) (tilt : K.TiltBound φ) :
    (∑ i, |T.turnError i|) ≤ 2 * φ :=
  (Finset.sum_le_sum (fun i _ => T.abs_turnError_le_spatial unit i (internal i))).trans
    (K.sum_roofSection_spatial_turn_le_tilt nonnegative small tilt origin direction unit
      T.time T.increasing)

end BoundarySectionTrace
end Unfoldings.ConvexCap
