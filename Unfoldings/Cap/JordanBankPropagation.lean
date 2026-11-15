module

public import Unfoldings.Cap.JordanLocalTwoRays
public import Unfoldings.Cap.ProjectedRawBankRays
public import Unfoldings.Cap.ProjectedBoundaryChainAgreement

/-! Propagate the actual original bank side through a Jordan hinge from local curve geometry. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap

open Filter Topology

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexCap C)
  {J : Set Plane} (jordan : Schoenflies.IsJordanCurve J) (contains : J ⊆ K.footprint)
  (avoids : ∀ f, Disjoint (interior (K.projectedTriangle f).carrier) J)

include jordan contains avoids in
open Classical in
/-- One actual previous Jordan bank and the local two path rays identify the next bank.
The next incident face and both full one-sided corner fans are derived, rather than
specified independently at each vertex. -/
theorem exists_next_jordan_bank_of_local_rays (U : Set Face)
    {retain : Set (C.restrictFaces U).Seam}
    (a b : (C.restrictFaces U).BoundaryEnd retain)
    (step : (C.restrictFaces U).boundaryMate retain
      ((C.restrictFaces U).boundaryTurn retain a) = b)
    (p : (C.restrictFaces (K.jordanFaces J)).BoundaryEnd Set.univ)
    (named : C.includeRestrictedGerm (K.jordanFaces J) p.val = C.includeRestrictedGerm U a.val)
    (positive_a : 0 < K.projectedGermOrientation (C.includeRestrictedGerm U a.val))
    (positive_b : 0 < K.projectedGermOrientation (C.includeRestrictedGerm U b.val))
    (locally : ∀ᶠ x in 𝓝 (Cap.horizontal ((K.folding.restrictFaces U).boundaryPosition b)),
      x ∈ J → x - Cap.horizontal ((K.folding.restrictFaces U).boundaryPosition b) ∈
        nonnegativeRay (Cap.horizontal ((K.folding.restrictFaces U).germDirection b.val)) ∪
        nonnegativeRay (Cap.horizontal ((K.folding.restrictFaces U).germDirection
          ((C.restrictFaces U).boundaryMate retain b).val))) :
    ∃ q : (C.restrictFaces (K.jordanFaces J)).BoundaryEnd Set.univ,
      C.includeRestrictedGerm (K.jordanFaces J) q.val = C.includeRestrictedGerm U b.val := by
  let V := K.jordanFaces J
  let R := C.restrictFaces U
  let T := C.restrictFaces V
  let F := K.folding.restrictFaces U
  let G := K.folding.restrictFaces V
  let incoming := T.boundaryTurn Set.univ p
  let q := T.boundaryMate Set.univ incoming
  have old_incoming : R.boundaryMate retain b = R.boundaryTurn retain a := by
    rw [← step, R.boundaryMate_involutive]
  have named_incoming : C.includeRestrictedGerm V incoming.val =
      C.includeRestrictedGerm U (R.boundaryMate retain b).val := by
    rw [old_incoming, C.includeRestrictedGerm_boundaryTurn, C.includeRestrictedGerm_boundaryTurn]
    simpa only using! congrArg
      (fun r : C.Germ => C.germOfEndpoint (C.germEdge r) (!r.2)) named
  have position : Cap.horizontal (G.boundaryPosition q) =
      Cap.horizontal (F.boundaryPosition b) := by
    change Cap.horizontal (G.boundaryPosition (T.boundaryMate Set.univ incoming)) = _
    rw [G.boundaryPosition_mate]
    exact (K.restricted_boundaryPosition_eq_of_raw V U incoming (R.boundaryMate retain b)
      named_incoming).trans (congrArg Cap.horizontal (F.boundaryPosition_mate b))
  have positive_p : 0 < K.projectedGermOrientation (C.includeRestrictedGerm V p.val) := by
    rw [named]
    exact positive_a
  have positive_q : 0 < K.projectedGermOrientation (C.includeRestrictedGerm V q.val) := by
    apply (K.projected_restricted_cut_boundaryMate_negative_iff V q).mp
    change K.projectedGermOrientation
      (C.includeRestrictedGerm V (T.boundaryMate Set.univ
        (T.boundaryMate Set.univ incoming)).val) < 0
    rw [T.boundaryMate_involutive]
    change K.projectedGermOrientation
      (C.includeRestrictedGerm V (T.boundaryTurn Set.univ p).val) < 0
    rw [K.projected_restricted_boundaryTurn]
    exact neg_neg_of_pos positive_p
  have local_q : ∀ᶠ x in 𝓝 (Cap.horizontal (G.boundaryPosition q)),
      x ∈ J → x - Cap.horizontal (G.boundaryPosition q) ∈
        nonnegativeRay (Cap.horizontal (F.germDirection b.val)) ∪
        nonnegativeRay (Cap.horizontal (F.germDirection (R.boundaryMate retain b).val)) := by
    rw [position]
    exact locally
  rcases K.jordan_bank_direction_of_local_two_rays jordan contains avoids q _ _ local_q with
    ⟨r, positive, direction⟩ | ⟨r, positive, direction⟩
  · have apex : (K.projectedTriangle q.val.1.1.val).vertex q.val.1.2 =
        (K.projectedTriangle b.val.1.1.val).vertex b.val.1.2 := by
      simpa only [SpatialFolding.boundaryPosition_raw] using! position
    exact ⟨q, K.projected_positive_raw_germ_unique_of_positive_scale
      (C.includeRestrictedGerm V q.val) (C.includeRestrictedGerm U b.val)
      apex positive_q positive_b positive direction⟩
  · have incoming_direction := K.restricted_germDirection_eq_of_raw V U incoming.val
      (R.boundaryMate retain b).val named_incoming
    have genuine : Cap.horizontal (G.germDirection incoming.val) ≠ 0 := by
      let g : T.LinkGerm Set.univ (T.boundaryEndVertex Set.univ incoming) := ⟨incoming.val, rfl⟩
      have ray := K.projectedGermRay_ne_zero (C.includeRestrictedLinkGerm V g)
      rw [← K.horizontal_germDirection] at ray
      exact ray
    have separated := K.restricted_boundary_rays_angle_ne_zero V incoming
    change InnerProductGeometry.angle (Cap.horizontal (G.germDirection incoming.val))
      (Cap.horizontal (G.germDirection q.val)) ≠ 0 at separated
    rw [direction, ← incoming_direction,
      InnerProductGeometry.angle_smul_right_of_pos _ _ positive,
      InnerProductGeometry.angle_self genuine] at separated
    exact (separated rfl).elim

end Unfoldings.ConvexCap
