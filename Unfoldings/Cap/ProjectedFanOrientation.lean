module

public import Unfoldings.Cap.ProjectedBankUniqueness
public import Unfoldings.Complex.RestoredLinkChain
public import Unfoldings.Complex.FaceRestrictionLinks

/-! Physical orientations along actual one-sided original and restricted corner fans. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexCap C)

@[simp] theorem projectedGermOrientation_turn (p : C.Germ) :
    K.projectedGermOrientation (C.turnGerm p) = -K.projectedGermOrientation p := by
  obtain ⟨corner, side⟩ := p
  cases side <;>
    simp only [projectedGermOrientation, TriangleComplex.turnGerm, Bool.not_true, Bool.not_false]
  all_goals unfold orient; ring

/-- Any original link subchain has disjoint projected corner cones, whether or not it
covers the full original vertex. -/
theorem projected_chain_cones_disjoint {w : C.Vertex Set.univ} {n : ℕ}
    (c : (C.linkSystem Set.univ w).Chain n) :
    Pairwise (fun i j : Fin (n + 1) => Disjoint
      (strictRayCone (K.projectedIntervalRay c i.castSucc) (K.projectedIntervalRay c i.succ))
      (strictRayCone (K.projectedIntervalRay c j.castSucc) (K.projectedIntervalRay c j.succ))) := by
  intro i j different
  rw [K.projectedIntervalRay_castSucc, K.projectedIntervalRay_succ,
    K.projectedIntervalRay_castSucc, K.projectedIntervalRay_succ,
    K.projectedGermRay_cone, K.projectedGermRay_cone]
  have face_ne : (c.point i).val.1.1 ≠ (c.point j).val.1.1 := by
    intro same
    have corner : (c.point i).val.1 = (c.point j).val.1 := congrArg Subtype.val
      (K.cornerAt_face_injective w
        (a₁ := ⟨(c.point i).val.1, (c.point i).property⟩)
        (a₂ := ⟨(c.point j).val.1, (c.point j).property⟩) same)
    rcases (C.germ_corner_eq_iff _ _).mp corner with equal | opposite
    · exact different (c.injective (Subtype.ext equal))
    · exact c.disjoint i j (Subtype.ext opposite)
  exact (K.projectedTriangle _).disjoint_cornerDirections (K.projectedTriangle _)
    (c.point i).val.1.2 (c.point j).val.1.2
    ((K.projectedGerm_apex (c.point i)).trans (K.projectedGerm_apex (c.point j)).symm)
    (K.projectedTriangles_nonoverlapping face_ne)

/-- The first raw orientation propagates along every actual original link subchain. -/
theorem projected_chain_orientation_sign {w : C.Vertex Set.univ} {n : ℕ}
    (c : (C.linkSystem Set.univ w).Chain n) (i : Fin (n + 1)) :
    (0 < K.projectedGermOrientation (c.point i).val) ↔
      0 < K.projectedGermOrientation c.first.val := by
  have result := interval_cone_orient_sign (K.projectedIntervalRay c)
    (fun j => by
      rw [K.projectedIntervalRay_castSucc, K.projectedIntervalRay_succ]
      exact K.projectedGermRay_orient_ne_zero _) (K.projected_chain_cones_disjoint c) i
  simpa only [K.projectedIntervalRay_castSucc, K.projectedIntervalRay_succ,
    K.projectedGermRay_orient, PairedInvolutions.System.Chain.first] using result

/-- At the other terminal bank the orientation is negative. This is intrinsic to the
actual original fan and does not require a planar development of the cut surface. -/
theorem projected_boundaryMate_negative {retain : Set C.Seam} (p : C.BoundaryEnd retain)
    (positive : 0 < K.projectedGermOrientation p.val) :
    K.projectedGermOrientation (C.boundaryMate retain p).val < 0 := by
  obtain ⟨n, c, first, last, _covers⟩ := C.exists_boundary_link retain p
  let d := C.restoreLinkChain (Set.subset_univ retain) c
  have start : 0 < K.projectedGermOrientation d.first.val := by
    change 0 < K.projectedGermOrientation c.first.val
    rw [first]
    exact positive
  have finish := (K.projected_chain_orientation_sign d (Fin.last n)).mpr start
  change 0 < K.projectedGermOrientation c.last.val at finish
  have terminal : C.turnGerm c.last.val = (C.boundaryMate retain p).val :=
    last
  rw [← terminal, K.projectedGermOrientation_turn]
  exact neg_neg_of_pos finish

open Classical in
/-- The same physical sign statement holds for a whole-face restricted fan. -/
theorem projected_restricted_boundaryMate_negative (U : Set Face)
    (p : (C.restrictFaces U).BoundaryEnd Set.univ)
    (positive : 0 < K.projectedGermOrientation (C.includeRestrictedGerm U p.val)) :
    K.projectedGermOrientation (C.includeRestrictedGerm U
      ((C.restrictFaces U).boundaryMate Set.univ p).val) < 0 := by
  let R := C.restrictFaces U
  obtain ⟨n, c, first, last, _covers⟩ := R.exists_boundary_link Set.univ p
  let d := C.includeRestrictedLinkChain U c
  have start : 0 < K.projectedGermOrientation d.first.val := by
    change 0 < K.projectedGermOrientation (C.includeRestrictedGerm U c.first.val)
    rw [first]
    exact positive
  have finish := (K.projected_chain_orientation_sign d (Fin.last n)).mpr start
  change 0 < K.projectedGermOrientation (C.includeRestrictedGerm U c.last.val) at finish
  have terminal : C.turnGerm (C.includeRestrictedGerm U c.last.val) =
      C.includeRestrictedGerm U (R.boundaryMate Set.univ p).val :=
    congrArg (C.includeRestrictedGerm U) last
  rw [← terminal, K.projectedGermOrientation_turn]
  exact neg_neg_of_pos finish

end Unfoldings.ConvexCap
