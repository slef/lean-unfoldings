module

public import Unfoldings.Roof.NestedMeshCutGeometry
public import Unfoldings.Roof.SpatialEnvelopeCap
public import Unfoldings.Geometry.NestedMeshInterior
public import Unfoldings.Complex.RestrictedIncidentAngles
public import Unfoldings.Complex.SubdivisionMetric

/-! Interior old-footprint fans agree exactly with actual full larger-mesh fans. -/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialEnvelope.Triangulation

universe u

variable {I : Type u} [Fintype I] [Nonempty I] {family : I → SpatialPlane}
  {Z W : ℝ} (T : Triangulation family Z) (U : Triangulation family W)

local instance nestedInteriorFanOldFintype : Fintype T.Index := @Fintype.ofFinite _ T.finite
local instance nestedInteriorFanNewFintype : Fintype U.Index := @Fintype.ofFinite _ U.finite

/-- Every full new face over a strictly interior old point belongs to the old subdivision. -/
theorem nested_incident_faces (cover : T.FaceRefinement U) (position : Space)
    (inside : Cap.horizontal position ∈ interior (clip family Z))
    (a : U.pairedComplex.Total) (same : U.pairedFolding.place a.1 a.2.val = position) :
    a.1 ∈ T.nestedPieceSet U := by
  apply T.nestedPiece_of_incident_interior U cover a.1 inside
  have horizontal : (family (U.support a.1)).project a.2.val = Cap.horizontal position :=
    ((family (U.support a.1)).horizontal_place a.2.val).symm.trans
      (congrArg Cap.horizontal same)
  rw [← horizontal]
  exact U.projected_member a.1 a.2.property

open Classical in
/-- The intrinsic cut equivalence preserves the actual original spatial fold. -/
theorem nestedSubdivision_fold_metricEquiv (cover : T.FaceRefinement U)
    (retain : Set T.pairedComplex.Seam) (fineRetain : Set (T.nestedComplex U).Seam)
    (H : (T.nestedSubdivision U cover).Conforming retain fineRetain)
    (x : (T.nestedComplex U).Realization fineRetain) :
    T.pairedFolding.toSpace retain (H.metricEquiv x) =
      (T.nestedFolding U).toSpace fineRetain x := by
  obtain ⟨⟨i, y⟩, rfl⟩ := MetricGluing.point_surjective (T.nestedComplex U).Cell
    ((T.nestedComplex U).glue fineRetain) x
  exact T.nestedSubdivision_spatial U cover i y.val

open Classical in
/-- All original corner weights agree with the full new mesh at an interior old-footprint copy. -/
theorem nested_interior_corner_weights (cover : T.FaceRefinement U) (cuts : Set Plane)
    (w : (T.nestedComplex U).Vertex (T.nestedRetain U cuts))
    (inside : Cap.horizontal ((T.nestedFolding U).toSpace (T.nestedRetain U cuts)
      ((T.nestedComplex U).vertexPoint (T.nestedRetain U cuts) w)) ∈ interior (clip family Z))
    (weight : U.pairedComplex.Corner → ℝ) :
    (∑ c : U.pairedComplex.Corner,
      if U.pairedComplex.vertexOfCorner (U.retainOutside cuts) c =
        U.pairedComplex.includeRestrictedVertex (T.nestedPieceSet U) (U.retainOutside cuts) w
      then weight c else 0) =
    ∑ d : (T.nestedComplex U).Corner,
      if (T.nestedComplex U).vertexOfCorner (T.nestedRetain U cuts) d = w
      then weight (d.1.val, d.2) else 0 :=
  U.pairedFolding.sum_restricted_incident_corner_weights (T.nestedPieceSet U)
    (U.retainOutside cuts) _ (T.nested_incident_faces U cover _ inside) w rfl weight

open Classical in
/-- The complete one-sided full-mesh fan equals its old-face subcomplex fan exactly. -/
theorem nested_interior_totalAngle (cover : T.FaceRefinement U) (cuts : Set Plane)
    (w : (T.nestedComplex U).Vertex (T.nestedRetain U cuts))
    (inside : Cap.horizontal ((T.nestedFolding U).toSpace (T.nestedRetain U cuts)
      ((T.nestedComplex U).vertexPoint (T.nestedRetain U cuts) w)) ∈ interior (clip family Z)) :
    U.pairedComplex.totalAngle (U.retainOutside cuts)
        (U.pairedComplex.includeRestrictedVertex (T.nestedPieceSet U) (U.retainOutside cuts) w) =
      (T.nestedComplex U).totalAngle (T.nestedRetain U cuts) w :=
  T.nested_interior_corner_weights U cover cuts w inside
    (fun c => (U.pairedComplex.triangle c.1).cornerAngle c.2)

end Unfoldings.SpatialEnvelope.Triangulation
