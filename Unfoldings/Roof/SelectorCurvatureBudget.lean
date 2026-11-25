module

public import Unfoldings.Cap.SharpGnomonicSolidAngle
public import Unfoldings.Roof.CurvatureBudget
public import Unfoldings.Roof.NormalArea

/-! Sum the actual Gaussian curvature inside a convex selector's chart area. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof

open MeasureTheory
open scoped ENNReal

variable {Face : Type*} [Fintype Face] {C : TriangleComplex Face} (K : ConvexRoof C)

/-- The interior angular defect is bounded by the planar area of any convex
set containing the finitely many incident slopes. -/
theorem ofReal_totalCurvature_le_selector_volume {S : Set Plane} (convex : Convex ℝ S)
    (slopes : ∀ f, K.normalSlope f ∈ S) :
    ENNReal.ofReal (C.totalInteriorAngularDefect Set.univ) ≤ volume S := by
  classical
  have included (v : C.Vertex Set.univ) : K.normalPolygon v ⊆ S := by
    apply convexHull_min _ convex
    rintro p ⟨f, i, _, rfl⟩
    exact slopes f
  calc
    _ ≤ ∑ v : C.Vertex Set.univ, solidAngleMeasure (K.sphericalNormalPolygon v) :=
      K.ofReal_totalCurvature_le_solid_normal_area
    _ ≤ ∑ v : C.Vertex Set.univ, volume (K.normalPolygon v) :=
      Finset.sum_le_sum (fun v _ => Cap.solidAngle_gnomonic_le_volume (K.compact_normalPolygon v))
    _ ≤ _ := sum_measure_convex_le volume K.normalPolygon (fun _ => convex_convexHull ℝ _)
      (fun _ _ different => K.normalPolygons_nonoverlapping different) S included

end Unfoldings.ConvexRoof
