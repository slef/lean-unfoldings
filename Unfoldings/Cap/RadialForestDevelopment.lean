module

public import Unfoldings.Cap.RadialCutForest
public import Unfoldings.Cap.CurvatureCutDevelopment

/-! A constructed radial cut forest develops as soon as its geometric support covers curvature. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap.RadialCutForest

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexCap C} {q : Plane} {cuts : Set Plane} (R : K.RadialCutForest q cuts)

/-- Each positive-curvature vertex selects an outgoing seam, so every copy is cut. -/
theorem curvature_endpoints
    (covered : ∀ w : C.Vertex Set.univ, 0 < C.interiorAngularDefect Set.univ w →
      K.projectedVertex w ∈ cuts)
    (w : C.Vertex Set.univ) (curved : 0 < C.interiorAngularDefect Set.univ w) :
    ∃ s b, s ∉ R.retain ∧ w = C.seamVertex s b := by
  have internal : ¬ C.IsBoundaryVertex Set.univ w := by
    intro boundary
    have zero : C.interiorAngularDefect Set.univ w = 0 := by
      simp only [TriangleComplex.interiorAngularDefect, ite_eq_left boundary]
    exact curved.ne' zero
  have nonroot : w ∉ R.parents.roots := by
    intro root
    rcases (Set.ext_iff.mp R.roots_eq w).mp root with boundary | outside
    · exact internal boundary
    · exact outside (covered w curved)
  let e : {w : C.Vertex Set.univ // w ∉ R.parents.roots} := ⟨w, nonroot⟩
  have cut : R.selection.edge e ∉ R.retain := fun retained => retained ⟨e, rfl⟩
  rcases R.selection.link e with first | last
  · exact ⟨R.selection.edge e, false, cut, first.1⟩
  · exact ⟨R.selection.edge e, true, cut, last.1⟩

/-- Curvature coverage is enough; unused flat interior vertices retain angle two pi. -/
theorem interior_flat
    (covered : ∀ w : C.Vertex Set.univ, 0 < C.interiorAngularDefect Set.univ w →
      K.projectedVertex w ∈ cuts)
    (w : C.Vertex R.retain) (internal : ¬ C.IsBoundaryVertex R.retain w) :
    C.totalAngle R.retain w = 2 * Real.pi :=
  K.interior_flat_of_curvature_cut R.retain (R.curvature_endpoints covered) w internal

/-- This constructs a locally isometric development; global overlap is a separate question. -/
theorem exists_development
    (covered : ∀ w : C.Vertex Set.univ, 0 < C.interiorAngularDefect Set.univ w →
      K.projectedVertex w ∈ cuts) :
    ∃ E : FacewiseDevelopment C R.retain, ∀ x, ‖(R.cutDisk x).val‖ < 1 → ∃ r > 0,
      Isometry (fun y : Metric.eball x (ENNReal.ofReal r) => E.toPlane y.val) :=
  K.exists_development_of_curvature_cut_disk R.retain R.cutDisk (R.curvature_endpoints covered)

end Unfoldings.ConvexCap.RadialCutForest
