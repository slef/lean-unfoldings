module

public import Unfoldings.Roof.SpatialEnvelopeCoordinates
public import Unfoldings.Geometry.SpatialEnvelopeChordSlopes
public import Unfoldings.Cap.DegenerateNormalCurvature

/-! Incident slopes of the actual normalized spatial roof are active support slopes. -/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialEnvelope.Triangulation

universe u

variable {I : Type u} [Fintype I] [Nonempty I] {family : I → SpatialPlane}
  {Z : ℝ} (T : Triangulation family Z)

local instance spatialCurvatureIndexFintype : Fintype T.Index :=
  @Fintype.ofFinite _ T.finite

theorem incidentSlopes_subset_activeSlopes
    (conforming : TriangleFamily.Conforming T.projectedTriangle)
    (inside : (interior (clip family Z)).Nonempty) (v : T.pairedComplex.Vertex Set.univ) :
    (T.normalizedCap conforming inside).incidentSlopes v ⊆
      activeSlopes family ((T.normalizedCap conforming inside).projectedVertex v) := by
  let Q := T.normalizedCap conforming inside
  rintro z ⟨i, k, at_vertex, slope_eq⟩
  have corner : (T.projectedTriangle i).vertex k = Q.projectedVertex v :=
    (T.normalizedCap_projectedTriangle_vertex conforming inside i k).symm.trans
      ((Q.projectedVertex_ofCorner i k).symm.trans (congrArg Q.projectedVertex at_vertex))
  have member : Q.projectedVertex v ∈ (T.projectedTriangle i).carrier :=
    corner ▸ (T.projectedTriangle i).vertex_mem k
  refine ⟨T.support i, (T.active i _ member).symm, ?_⟩
  exact (T.normalizedCap_normalSlope conforming inside i).symm.trans slope_eq

end Unfoldings.SpatialEnvelope.Triangulation
