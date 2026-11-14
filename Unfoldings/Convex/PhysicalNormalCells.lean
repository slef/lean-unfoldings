module

public import Unfoldings.Convex.FiniteSlopeModel
public import Unfoldings.Convex.ActiveCell
public import Unfoldings.Roof.CurvatureNormalInterior
public import Unfoldings.Roof.SpatialEnvelopeRoof

/-! Positive curvature in an actual spatial model forces a full active conjugate normal cell. -/

@[expose] public section

noncomputable section

namespace Unfoldings.SlopeEnvelope.FiniteSlopeModel

variable {E : SlopeEnvelope} (M : E.FiniteSlopeModel) {Z : ℝ}
  (T : SpatialEnvelope.Triangulation M.plane Z)
  (conforming : TriangleFamily.Conforming T.projectedTriangle)
  (inside : (interior (SpatialEnvelope.clip M.plane Z)).Nonempty)

local instance : Fintype T.Index := @Fintype.ofFinite _ T.finite

theorem roof_incidentSlopes_subset_active (v : T.pairedComplex.Vertex Set.univ) :
    (T.roof conforming inside).incidentSlopes v ⊆
      {p | E.Active ((T.roof conforming inside).projectedVertex v) p} := by
  let Q := T.roof conforming inside
  rintro p ⟨f, i, corner, slope_eq⟩
  have vertex : (T.projectedTriangle f).vertex i = Q.projectedVertex v := by
    rw [← corner, Q.projectedVertex_ofCorner]
    change _ = Cap.horizontal (T.placement f ((T.triangle f).vertex i))
    change _ = Cap.horizontal ((M.plane (T.support f)).place
      ((M.plane (T.support f)).project.symm ((T.projectedTriangle f).vertex i)))
    rw [(M.plane (T.support f)).horizontal_place,
      (M.plane (T.support f)).project.apply_symm_apply]
  have member : Q.projectedVertex v ∈ (T.projectedTriangle f).carrier :=
    vertex ▸ (T.projectedTriangle f).vertex_mem i
  have active := T.active f _ member
  rw [M.height_eq] at active
  have slope : Q.normalSlope f = (T.support f).val := M.normalSlope (T.support f)
  rw [← slope_eq, slope]
  refine ⟨M.included _ (T.support f).property, ?_⟩
  change E.height (Q.projectedVertex v) =
    inner ℝ (Q.projectedVertex v) (T.support f).val - E.dual (T.support f).val
  change -E.height (Q.projectedVertex v) =
    E.dual (T.support f).val - inner ℝ (T.support f).val (Q.projectedVertex v) at active
  have comm : inner ℝ (T.support f).val (Q.projectedVertex v) =
      inner ℝ (Q.projectedVertex v) (T.support f).val := real_inner_comm _ _
  rw [comm] at active
  linarith

/-- This transfers actual intrinsic angular defect, rather than defining curvature through
normal-cell dimension. No tilt bound or normal-height bound is assumed. -/
theorem active_cell_interior_of_positive_curvature (convex : Convex ℝ E.slopes)
    (dual_convex : ConvexOn ℝ Set.univ E.dual) (v : T.pairedComplex.Vertex Set.univ)
    (curved : 0 < T.pairedComplex.interiorAngularDefect Set.univ v) :
    (interior {p | E.Active ((T.roof conforming inside).projectedVertex v) p}).Nonempty := by
  let Q := T.roof conforming inside
  have included : Q.normalPolygon v ⊆ {p | E.Active (Q.projectedVertex v) p} :=
    convexHull_min (M.roof_incidentSlopes_subset_active T conforming inside v)
      (E.convex_active_cell convex dual_convex _)
  exact (Q.normalPolygon_interior_nonempty_of_positive_curvature v curved).mono
    (interior_mono included)

end Unfoldings.SlopeEnvelope.FiniteSlopeModel
