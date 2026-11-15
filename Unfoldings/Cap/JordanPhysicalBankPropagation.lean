module

public import Unfoldings.Cap.SignedJordanBankPropagation
public import Unfoldings.Cap.ProjectedUnsignedBankRays

/-! Actual Jordan banks follow physical original edges even when the selected side is opposite. -/

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
/-- The actual next Jordan bank has the original full spatial vector and endpoint position.
Only the physical preceding bank is identified; its raw incident face need not match.
The selected bank is derived in either original seam side, with no sign input. -/
theorem jordan_next_bank_preserves_physical_edge (U : Set Face)
    {retain : Set (C.restrictFaces U).Seam}
    (a b : (C.restrictFaces U).BoundaryEnd retain)
    (step : (C.restrictFaces U).boundaryMate retain
      ((C.restrictFaces U).boundaryTurn retain a) = b)
    (p : (C.restrictFaces (K.jordanFaces J)).BoundaryEnd Set.univ)
    (position : (K.folding.restrictFaces (K.jordanFaces J)).boundaryPosition p =
      (K.folding.restrictFaces U).boundaryPosition a)
    (direction : (K.folding.restrictFaces (K.jordanFaces J)).germDirection p.val =
      (K.folding.restrictFaces U).germDirection a.val)
    (internal : ¬ C.IsBoundaryVertex Set.univ
      (C.vertexOfCorner Set.univ (C.includeRestrictedGerm U b.val).1))
    (locally : ∀ᶠ x in 𝓝 (Cap.horizontal ((K.folding.restrictFaces U).boundaryPosition b)),
      x ∈ J → x - Cap.horizontal ((K.folding.restrictFaces U).boundaryPosition b) ∈
        nonnegativeRay (Cap.horizontal ((K.folding.restrictFaces U).germDirection b.val)) ∪
        nonnegativeRay (Cap.horizontal ((K.folding.restrictFaces U).germDirection
          ((C.restrictFaces U).boundaryMate retain b).val))) :
    let T := C.restrictFaces (K.jordanFaces J)
    let q := T.boundaryMate Set.univ (T.boundaryTurn Set.univ p)
    (K.folding.restrictFaces (K.jordanFaces J)).boundaryPosition q =
        (K.folding.restrictFaces U).boundaryPosition b ∧
      (K.folding.restrictFaces (K.jordanFaces J)).germDirection q.val =
        (K.folding.restrictFaces U).germDirection b.val := by
  let V := K.jordanFaces J
  let R := C.restrictFaces U
  let T := C.restrictFaces V
  let F := K.folding.restrictFaces U
  let G := K.folding.restrictFaces V
  let incoming := T.boundaryTurn Set.univ p
  let q := T.boundaryMate Set.univ incoming
  have at_q : G.boundaryPosition q = F.boundaryPosition b := by
    calc
      _ = G.boundaryPosition incoming := G.boundaryPosition_mate incoming
      _ = G.boundaryPosition p + G.germDirection p.val := by
        rw [G.germDirection_boundary_positions]
        abel
      _ = F.boundaryPosition a + F.germDirection a.val := by rw [position, direction]
      _ = F.boundaryPosition b := by
        rw [F.germDirection_boundary_step step]
        abel
  refine ⟨at_q, ?_⟩
  have local_q : ∀ᶠ x in 𝓝 (Cap.horizontal (G.boundaryPosition q)),
      x ∈ J → x - Cap.horizontal (G.boundaryPosition q) ∈
        nonnegativeRay (Cap.horizontal (F.germDirection b.val)) ∪
        nonnegativeRay (Cap.horizontal (F.germDirection (R.boundaryMate retain b).val)) := by
    rw [at_q]
    exact locally
  rcases K.jordan_bank_direction_of_local_two_rays jordan contains avoids q _ _ local_q with
    ⟨r, positive, ray⟩ | ⟨r, positive, ray⟩
  · have apex : (K.projectedTriangle q.val.1.1.val).vertex q.val.1.2 =
        (K.projectedTriangle b.val.1.1.val).vertex b.val.1.2 := by
      simpa only [SpatialFolding.boundaryPosition_raw] using! congrArg Cap.horizontal at_q
    have same_vertex : C.vertexOfCorner Set.univ
        (C.includeRestrictedGerm V q.val).1 =
      C.vertexOfCorner Set.univ (C.includeRestrictedGerm U b.val).1 :=
      K.projectedVertex_injective apex
    have original_internal : ¬ C.IsBoundaryVertex Set.univ
        (C.vertexOfCorner Set.univ (C.includeRestrictedGerm V q.val).1) :=
      same_vertex.symm ▸ internal
    exact K.projected_raw_direction_eq_of_positive_scale
      (C.includeRestrictedGerm V q.val) (C.includeRestrictedGerm U b.val)
      apex original_internal positive ray
  · have old_incoming : R.boundaryMate retain b = R.boundaryTurn retain a := by
      rw [← step, R.boundaryMate_involutive]
    have incoming_direction : G.germDirection incoming.val =
        F.germDirection (R.boundaryMate retain b).val := by
      rw [old_incoming, G.germDirection_boundaryTurn, F.germDirection_boundaryTurn, direction]
    have genuine : Cap.horizontal (G.germDirection incoming.val) ≠ 0 := by
      let g : T.LinkGerm Set.univ (T.boundaryEndVertex Set.univ incoming) := ⟨incoming.val, rfl⟩
      have nonzero := K.projectedGermRay_ne_zero (C.includeRestrictedLinkGerm V g)
      rw [← K.horizontal_germDirection] at nonzero
      exact nonzero
    have separated := K.restricted_boundary_rays_angle_ne_zero V incoming
    change InnerProductGeometry.angle (Cap.horizontal (G.germDirection incoming.val))
      (Cap.horizontal (G.germDirection q.val)) ≠ 0 at separated
    rw [ray, ← incoming_direction,
      InnerProductGeometry.angle_smul_right_of_pos _ _ positive,
      InnerProductGeometry.angle_self genuine] at separated
    exact (separated rfl).elim

end Unfoldings.ConvexCap
