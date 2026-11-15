module

public import Unfoldings.Cap.RestrictedCutFanAgreement
public import Unfoldings.Complex.RestrictedBoundaryChainAgreement

/-! Physical bank positions determine complete normalized rolls in a common cap mesh. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexCap C)

open Classical in
/-- Either orientation is recovered from the actual complete one-sided fan. -/
theorem projected_restricted_cut_boundaryMate_negative_iff (U : Set Face)
    {retain : Set (C.restrictFaces U).Seam}
    (p : (C.restrictFaces U).BoundaryEnd retain) :
    K.projectedGermOrientation (C.includeRestrictedGerm U
      ((C.restrictFaces U).boundaryMate retain p).val) < 0 ↔
        0 < K.projectedGermOrientation (C.includeRestrictedGerm U p.val) := by
  let R := C.restrictFaces U
  obtain ⟨n, c, first, last, _covers⟩ := R.exists_boundary_link retain p
  let d := C.includeRestrictedLinkChain U (R.restoreLinkChain (Set.subset_univ retain) c)
  have sign := K.projected_chain_orientation_sign d (Fin.last n)
  change (0 < K.projectedGermOrientation (C.includeRestrictedGerm U c.last.val)) ↔
    0 < K.projectedGermOrientation (C.includeRestrictedGerm U c.first.val) at sign
  rw [first] at sign
  have terminal : C.turnGerm (C.includeRestrictedGerm U c.last.val) =
      C.includeRestrictedGerm U (R.boundaryMate retain p).val :=
    congrArg (C.includeRestrictedGerm U) last
  rw [← terminal, K.projectedGermOrientation_turn, neg_neg_iff_pos]
  exact sign

open Classical in
/-- Exchanging the actual endpoints reverses the physical raw bank orientation. -/
theorem projected_restricted_boundaryTurn (U : Set Face)
    {retain : Set (C.restrictFaces U).Seam}
    (p : (C.restrictFaces U).BoundaryEnd retain) :
    K.projectedGermOrientation (C.includeRestrictedGerm U
        ((C.restrictFaces U).boundaryTurn retain p).val) =
      -K.projectedGermOrientation (C.includeRestrictedGerm U p.val) := by
  rw [C.includeRestrictedGerm_boundaryTurn]
  simpa only [C.germOfEndpoint_germEdge] using! K.projectedGermOrientation_bank_end
    (C.germEdge (C.includeRestrictedGerm U p.val)) (C.includeRestrictedGerm U p.val).2

open Classical in
/-- A positive initial bank orients an entire actual boundary chain. -/
theorem projected_restricted_boundary_chain_positive (U : Set Face)
    {retain : Set (C.restrictFaces U).Seam} {n : ℕ}
    (c : ((C.restrictFaces U).boundarySystem retain).Chain n)
    (positive : 0 < K.projectedGermOrientation (C.includeRestrictedGerm U c.first.val))
    (i : Fin (n + 1)) :
    0 < K.projectedGermOrientation (C.includeRestrictedGerm U (c.point i).val) := by
  induction i using Fin.induction with
  | zero => exact positive
  | succ k previous =>
    apply (K.projected_restricted_cut_boundaryMate_negative_iff U (c.point k.succ)).mp
    have paired := congrArg ((C.restrictFaces U).boundaryMate retain) (c.next k)
    change (C.restrictFaces U).boundaryMate retain
      ((C.restrictFaces U).boundaryMate retain
        ((C.restrictFaces U).boundaryTurn retain (c.point k.castSucc))) =
          (C.restrictFaces U).boundaryMate retain (c.point k.succ) at paired
    rw [(C.restrictFaces U).boundaryMate_involutive] at paired
    rw [← paired, K.projected_restricted_boundaryTurn]
    exact neg_neg_of_pos previous

local instance projectedChainMembership (U : Set Face) : DecidablePred (· ∈ U) :=
  Classical.decPred _

variable (U V : Set Face)
  {leftRetain : Set (C.restrictFaces U).Seam}
  {rightRetain : Set (C.restrictFaces V).Seam} {n : ℕ}
  (c : ((C.restrictFaces U).boundarySystem leftRetain).Chain n)
  (d : ((C.restrictFaces V).boundarySystem rightRetain).Chain n)
  (position : ∀ i, Cap.horizontal ((K.folding.restrictFaces U).boundaryPosition (c.point i)) =
    Cap.horizontal ((K.folding.restrictFaces V).boundaryPosition (d.point i)))
  (finish : Cap.horizontal ((K.folding.restrictFaces U).boundaryPosition
      ((C.restrictFaces U).boundaryTurn leftRetain c.last)) =
    Cap.horizontal ((K.folding.restrictFaces V).boundaryPosition
      ((C.restrictFaces V).boundaryTurn rightRetain d.last)))
  (positive_c : 0 < K.projectedGermOrientation (C.includeRestrictedGerm U c.first.val))
  (positive_d : 0 < K.projectedGermOrientation (C.includeRestrictedGerm V d.first.val))

include position finish positive_c positive_d in
open Classical in
/-- Only projected vertex positions and initial orientation are supplied. Actual directed
banks, including the terminal bank, are recovered rather than assumed to match. -/
theorem restricted_boundary_chain_germs_eq_of_projection (i : Fin (n + 1)) :
    C.includeRestrictedGerm U (c.point i).val = C.includeRestrictedGerm V (d.point i).val := by
  dsimp only [PairedInvolutions.System.Chain.last] at finish
  have apex : (K.projectedTriangle (c.point i).val.1.1.val).vertex (c.point i).val.1.2 =
      (K.projectedTriangle (d.point i).val.1.1.val).vertex (d.point i).val.1.2 := by
    simpa only [SpatialFolding.boundaryPosition_raw] using! position i
  have direction :
      Cap.horizontal ((K.folding.restrictFaces U).germDirection (c.point i).val) =
        Cap.horizontal ((K.folding.restrictFaces V).germDirection (d.point i).val) := by
    refine Fin.lastCases ?_ (fun k => ?_) i
    · rw [(K.folding.restrictFaces U).germDirection_boundary_positions,
        (K.folding.restrictFaces V).germDirection_boundary_positions, map_sub, map_sub,
        finish, position]
    · rw [(K.folding.restrictFaces U).germDirection_boundary_step (c.next k),
        (K.folding.restrictFaces V).germDirection_boundary_step (d.next k), map_sub, map_sub,
        position, position]
  exact K.projected_raw_germ_unique _ _ apex
    (mul_pos (K.projected_restricted_boundary_chain_positive U c positive_c i)
      (K.projected_restricted_boundary_chain_positive V d positive_d i)) direction

include position finish positive_c positive_d in
open Classical in
/-- The physical comparison preserves every real rolling prefix. -/
theorem restricted_boundary_chain_heading_eq_of_projection (i : Fin (n + 1)) :
    (C.restrictFaces U).boundaryChainRollHeading c i =
      (C.restrictFaces V).boundaryChainRollHeading d i :=
  C.restricted_boundary_chain_rollHeading U V c d
    (K.restricted_boundary_chain_germs_eq_of_projection U V c d
      position finish positive_c positive_d) i

include position finish positive_c positive_d in
open Classical in
/-- The full normalized polygonal rolls agree, including lengths and hinge positions.
No bank-length, fan-angle or heading equality is required as input. -/
theorem restricted_boundary_chain_roll_eq_of_projection :
    (C.restrictFaces U).boundaryChainRoll c = (C.restrictFaces V).boundaryChainRoll d :=
  C.restricted_boundary_chain_roll U V c d
    (K.restricted_boundary_chain_germs_eq_of_projection U V c d
      position finish positive_c positive_d)

end Unfoldings.ConvexCap
