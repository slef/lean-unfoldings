module

public import Unfoldings.Cap.SectorCrossings
public import Unfoldings.Geometry.AngleMonotoneCrossings

/-!
# Forest crossing budgets in arbitrary planar frames

A translated orthogonal frame represents rays with arbitrary origins and
directions. Acuteness of the original root-path wedges derives the signed
crossing bound in every such frame; no orientation-specific certificate is input.
-/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap.SectorForest

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexCap C} {t : ℝ} {origin : C.Vertex Set.univ} (M : K.SectorForest t origin)

/-- The actual signed root-path crossing count is bounded for every ray direction. -/
theorem abs_rootPath_rayCrossings_inFrame_le_one (positive : 0 < t) (small : t < 1)
    (v : C.Vertex Set.univ) (L : Plane ≃ₗᵢ[ℝ] Plane) (center : Plane) (cut level : ℝ) :
    |∑ i : Fin (M.parents.distanceToRoot v), horizontalRayCrossing
      (fun j => ((M.rootPath v).inFrame L center).vertex j 0)
      (fun j => ((M.rootPath v).inFrame L center).vertex j 1) cut level i| ≤ 1 :=
  (M.rootPath_angleMonotone positive small v).abs_sum_rayCrossings_le_one (M.rootPath v)
    (threeSectorWidth_lt_pi_div_two positive small _) L center cut level

/-- The signed crossing of the actual parent edge, expressed in a translated orthogonal frame. -/
def parentRayCrossingInFrame (L : Plane ≃ₗᵢ[ℝ] Plane) (center : Plane) (cut level : ℝ)
    (v : C.Vertex Set.univ) : ℝ :=
  let a := L (K.projectedVertex v - center)
  let b := L (K.projectedVertex (M.parents.parent v) - center)
  let parameter := levelCrossingParameter (a 1) (b 1) level
  if cut < (1 - parameter) * a 0 + parameter * b 0 then
    levelIndicator level (b 1) - levelIndicator level (a 1) else 0

theorem rootPath_crossing_inFrame_eq_parent (L : Plane ≃ₗᵢ[ℝ] Plane) (center : Plane)
    (cut level : ℝ) (v : C.Vertex Set.univ) (i : Fin (M.parents.distanceToRoot v)) :
    horizontalRayCrossing (fun j => ((M.rootPath v).inFrame L center).vertex j 0)
      (fun j => ((M.rootPath v).inFrame L center).vertex j 1) cut level i =
      M.parentRayCrossingInFrame L center cut level (M.parents.parent^[i.val] v) := by
  simp only [horizontalRayCrossing, levelCrossingPosition, parentRayCrossingInFrame,
    PolygonalChain.inFrame, rootPath, Fin.val_succ, Fin.val_castSucc, Function.iterate_succ_apply']

open scoped Classical in
/-- Arbitrary-ray subtree corrections are bounded by the actual total cap curvature. -/
theorem abs_weighted_parentRayCrossings_inFrame_le_totalCurvature
    (positive : 0 < t) (small : t < 1) (L : Plane ≃ₗᵢ[ℝ] Plane) (center : Plane) (cut level : ℝ) :
    |∑ e : C.Vertex Set.univ, if e ∉ M.parents.roots then
      M.parentRayCrossingInFrame L center cut level e * M.subtreeCurvature e else 0| ≤
        C.totalInteriorAngularDefect Set.univ := by
  classical
  apply M.parents.abs_sum_subtree_weights_le
    (fun v => C.interiorAngularDefect Set.univ v) (M.parentRayCrossingInFrame L center cut level)
    K.interiorCurvature_nonneg
  intro v
  simpa only [M.rootPath_crossing_inFrame_eq_parent L center cut level] using
    M.abs_rootPath_rayCrossings_inFrame_le_one positive small v L center cut level

end Unfoldings.ConvexCap.SectorForest
