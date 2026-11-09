module

public import Unfoldings.Cone.CyclicShortcut
public import Unfoldings.Cone.CyclicSeams

/-!
# Strict apex shortcuts at every positive-curvature interior vertex

Start the actual cyclic link order at a corner representing the first point.
The angular comparison preserves every radial distance and identifies the
closing banks. The proved cyclic shortcut then supplies a strict intrinsic
shortcut for every pair of nonapex points in the actual tangent fan.
-/

@[expose] public section

open scoped NNReal

noncomputable section

namespace Unfoldings.TriangleComplex

universe u v

variable {Face : Type u} [Fintype Face] (C : TriangleComplex.{u, v} Face)
  (retain : Set C.Seam) (v : C.Vertex retain)

theorem exists_cyclic_link_from (interior : ¬ C.IsBoundaryVertex retain v)
    (p : C.LinkGerm retain v) :
    ∃ n, ∃ chain : (C.linkSystem retain v).Chain n,
      chain.first = p ∧
        C.linkMate retain v (C.linkTurn retain v chain.last) = chain.first ∧
          ∀ q, chain.Visited q := by
  have free (q : C.LinkGerm retain v) : C.linkMate retain v q ≠ q := fun fixed =>
    interior ((C.isBoundaryVertex_iff_linkMate_fixed retain v).mpr ⟨q, fixed⟩)
  exact (C.linkSystem retain v).exists_cycle_chain (C.linkSystem_connected retain v) free p

/-- Positive curvature at an interior vertex forbids metric equality through
the apex for every pair of other tangent points. -/
theorem tangent_edist_lt_via_origin (interior : ¬ C.IsBoundaryVertex retain v)
    (positive_curvature : C.totalAngle retain v < 2 * Real.pi)
    (z w : C.TangentFan retain v) (left_nonzero : z ≠ C.tangentOrigin retain v)
    (right_nonzero : w ≠ C.tangentOrigin retain v) :
    edist z w < edist z (C.tangentOrigin retain v) + edist (C.tangentOrigin retain v) w := by
  obtain ⟨⟨c, x⟩, rfl⟩ := MetricGluing.point_surjective
    (C.TangentCell retain v) (C.tangentGlue retain v) z
  let p : C.LinkGerm retain v := ⟨(c.val, false), c.property⟩
  obtain ⟨n, chain, first, closes, covers⟩ := C.exists_cyclic_link_from retain v interior p
  have corner : C.linkCornerAt retain v chain 0 = c :=
    Subtype.ext (congrArg (fun q : C.LinkGerm retain v => q.val.1) first)
  clear first
  subst c
  let A := C.linkAngularFan retain v chain
  let f := C.angularToTangent retain v chain
  let a : A.Cell 0 := C.linkSectorIsometry retain v chain 0 x
  have left_image : f (A.faceMap 0 a) =
      C.tangentFaceMap retain v (C.linkCornerAt retain v chain 0) x := by
    change C.tangentFaceMap retain v (C.linkCornerAt retain v chain 0)
      ((C.linkSectorIsometry retain v chain 0).symm
        (C.linkSectorIsometry retain v chain 0 x)) = _
    rw [IsometryEquiv.symm_apply_apply]
  obtain ⟨b, right_image⟩ := C.angularToTangent_surjective retain v chain covers w
  obtain ⟨⟨j, y⟩, rfl⟩ := MetricGluing.point_surjective A.Cell A.glue b
  change f (A.faceMap j y) = w at right_image
  have left_point_nonzero : a.val ≠ 0 := by
    intro zero
    have radius := C.angularToTangent_radial retain v chain (A.faceMap 0 a)
    change edist (C.tangentOrigin retain v) (f (A.faceMap 0 a)) =
      edist A.origin (A.faceMap 0 a) at radius
    rw [left_image, A.edist_origin_faceMap, zero, edist_self] at radius
    exact left_nonzero (edist_eq_zero.mp radius).symm
  have right_point_nonzero : y.val ≠ 0 := by
    intro zero
    have radius := C.angularToTangent_radial retain v chain (A.faceMap j y)
    change edist (C.tangentOrigin retain v) (f (A.faceMap j y)) =
      edist A.origin (A.faceMap j y) at radius
    rw [right_image, A.edist_origin_faceMap, zero, edist_self] at radius
    exact right_nonzero (edist_eq_zero.mp radius).symm
  have strict := A.cyclic_first_cell_shortcut f
    (C.angularToTangent_lipschitz retain v chain)
    (C.angularToTangent_outer_banks retain v chain closes)
    (C.tangentOrigin retain v) (C.angularToTangent_radial retain v chain)
    ((C.linkAngularFan_totalAngle retain v chain covers).trans_lt positive_curvature)
    j a y left_point_nonzero right_point_nonzero
  rw [left_image, right_image] at strict
  exact strict

end Unfoldings.TriangleComplex
