module

public import Unfoldings.Cap.JordanBankPropagation
public import Unfoldings.Cap.ProjectedSignedBankRays

/-! Propagate a physical selected Jordan bank in either traversal orientation. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap

open Filter Topology

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexCap C)

open Classical in
/-- Actual boundary successors occupy the same oriented side, for positive or negative traversal. -/
theorem projected_restricted_boundary_successor_sign (U : Set Face)
    {retain : Set (C.restrictFaces U).Seam}
    (a b : (C.restrictFaces U).BoundaryEnd retain)
    (step : (C.restrictFaces U).boundaryMate retain
      ((C.restrictFaces U).boundaryTurn retain a) = b) :
    0 < K.projectedGermOrientation (C.includeRestrictedGerm U a.val) *
      K.projectedGermOrientation (C.includeRestrictedGerm U b.val) := by
  have negative : K.projectedGermOrientation (C.includeRestrictedGerm U b.val) < 0 ↔
      K.projectedGermOrientation (C.includeRestrictedGerm U a.val) < 0 := by
    rw [← step, K.projected_restricted_cut_boundaryMate_negative_iff,
      K.projected_restricted_boundaryTurn, neg_pos]
  rcases lt_or_gt_of_ne (K.projectedGermOrientation_ne_zero
      (C.includeRestrictedGerm U a.val)) with first | first
  · exact mul_pos_of_neg_of_neg first (negative.mpr first)
  · have last : 0 < K.projectedGermOrientation (C.includeRestrictedGerm U b.val) :=
      lt_of_le_of_ne (le_of_not_gt (fun h => first.not_gt (negative.mp h)))
        (Ne.symm (K.projectedGermOrientation_ne_zero _))
    exact mul_pos first last

variable {J : Set Plane} (jordan : Schoenflies.IsJordanCurve J) (contains : J ⊆ K.footprint)
  (avoids : ∀ f, Disjoint (interior (K.projectedTriangle f).carrier) J)

include jordan contains avoids in
open Classical in
/-- A selected previous bank and the actual two-ray geometry determine the next original
bank on either occupied side. No sign, fan-angle or next-face certificate is supplied. -/
theorem exists_next_jordan_bank_of_local_rays_signed (U : Set Face)
    {retain : Set (C.restrictFaces U).Seam}
    (a b : (C.restrictFaces U).BoundaryEnd retain)
    (step : (C.restrictFaces U).boundaryMate retain
      ((C.restrictFaces U).boundaryTurn retain a) = b)
    (p : (C.restrictFaces (K.jordanFaces J)).BoundaryEnd Set.univ)
    (named : C.includeRestrictedGerm (K.jordanFaces J) p.val = C.includeRestrictedGerm U a.val)
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
  have ab := K.projected_restricted_boundary_successor_sign U a b step
  have pq := K.projected_restricted_boundary_successor_sign V p q rfl
  rw [named] at pq
  have qb : 0 < K.projectedGermOrientation (C.includeRestrictedGerm V q.val) *
      K.projectedGermOrientation (C.includeRestrictedGerm U b.val) := by
    rcases mul_pos_iff.mp ab with ⟨apos, bpos⟩ | ⟨aneg, bneg⟩
    · have qpos := (mul_pos_iff_of_pos_left apos).mp pq
      exact mul_pos qpos bpos
    · have qneg : K.projectedGermOrientation (C.includeRestrictedGerm V q.val) < 0 := by
        rcases mul_pos_iff.mp pq with ⟨apos, _⟩ | ⟨_, qneg⟩
        · exact (apos.not_gt aneg).elim
        · exact qneg
      exact mul_pos_of_neg_of_neg qneg bneg
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
    exact ⟨q, K.projected_raw_germ_unique_of_same_orientation_positive_scale
      (C.includeRestrictedGerm V q.val) (C.includeRestrictedGerm U b.val)
      apex qb positive direction⟩
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
