module

public import Unfoldings.Cap.CompletedParentDirections
public import Unfoldings.Geometry.AngleMonotoneCrossings
public import Unfoldings.Topology.SupportedSubtreeWeights
public import Unfoldings.Topology.OrderedChanges

/-! Mesh-independent crossing potentials need acute paths only at positive-curvature vertices. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap.RadialCutForest

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexCap C} {q : Plane} {cuts : Set Plane} (R : K.RadialCutForest q cuts)

def completedRootPath (w : C.Vertex Set.univ) :
    PolygonalChain Plane (R.spanningCompletion.parents.distanceToRoot w) where
  vertex i := K.projectedVertex (R.spanningCompletion.parents.parent^[i.val] w)

/-- The completion's arbitrary flat branches require no common acute wedge. -/
def CurvedPathWedges : Prop :=
  ∀ w : C.Vertex Set.univ, 0 < C.interiorAngularDefect Set.univ w →
    ∃ width < Real.pi / 2, (R.completedRootPath w).AngleMonotone width

def completedParentRayCrossing (L : Plane ≃ₗᵢ[ℝ] Plane) (center : Plane) (cut level : ℝ)
    (w : C.Vertex Set.univ) : ℝ :=
  let a := L (K.projectedVertex w - center)
  let b := L (K.projectedVertex (R.spanningCompletion.parents.parent w) - center)
  let parameter := levelCrossingParameter (a 1) (b 1) level
  if cut < (1 - parameter) * a 0 + parameter * b 0 then
    levelIndicator level (b 1) - levelIndicator level (a 1) else 0

theorem completedRootPath_crossing_eq_parent (L : Plane ≃ₗᵢ[ℝ] Plane) (center : Plane)
    (cut level : ℝ) (w : C.Vertex Set.univ)
    (i : Fin (R.spanningCompletion.parents.distanceToRoot w)) :
    horizontalRayCrossing (fun j => ((R.completedRootPath w).inFrame L center).vertex j 0)
      (fun j => ((R.completedRootPath w).inFrame L center).vertex j 1) cut level i =
      R.completedParentRayCrossing L center cut level
        (R.spanningCompletion.parents.parent^[i.val] w) := by
  simp only [horizontalRayCrossing, levelCrossingPosition, completedParentRayCrossing,
    PolygonalChain.inFrame, completedRootPath, Fin.val_succ, Fin.val_castSucc,
    Function.iterate_succ_apply']

open scoped Classical in
def completedRayCurvaturePotential (L : Plane ≃ₗᵢ[ℝ] Plane) (center : Plane) (cut level : ℝ) : ℝ :=
  ∑ e : C.Vertex Set.univ, if e ∉ R.spanningCompletion.parents.roots then
    R.completedParentRayCrossing L center cut level e * R.completedSubtreeCurvature e else 0

/-- Regroup signed crossings before taking absolute values. The bound has no factor depending
on the number of added vertices, edges, faces, or flat branches. -/
theorem abs_completedRayCurvaturePotential_le (wedges : R.CurvedPathWedges)
    (L : Plane ≃ₗᵢ[ℝ] Plane) (center : Plane) (cut level : ℝ) :
    |R.completedRayCurvaturePotential L center cut level| ≤
      C.totalInteriorAngularDefect Set.univ := by
  classical
  apply R.spanningCompletion.parents.abs_sum_subtree_weights_le_of_pos
    (fun w => C.interiorAngularDefect Set.univ w)
    (R.completedParentRayCrossing L center cut level) K.interiorCurvature_nonneg
  intro w curved
  obtain ⟨width, small, monotone⟩ := wedges w curved
  simpa only [R.completedRootPath_crossing_eq_parent L center cut level] using
    monotone.abs_sum_rayCrossings_le_one (R.completedRootPath w) small L center cut level

theorem abs_completedRayCurvaturePotential_sub_le (wedges : R.CurvedPathWedges)
    (L : Plane ≃ₗᵢ[ℝ] Plane) (center : Plane) (first last level : ℝ) :
    |R.completedRayCurvaturePotential L center last level -
      R.completedRayCurvaturePotential L center first level| ≤
        2 * C.totalInteriorAngularDefect Set.univ := by
  calc
    _ ≤ |R.completedRayCurvaturePotential L center last level| +
        |R.completedRayCurvaturePotential L center first level| := abs_sub _ _
    _ ≤ C.totalInteriorAngularDefect Set.univ + C.totalInteriorAngularDefect Set.univ :=
      add_le_add (R.abs_completedRayCurvaturePotential_le wedges L center last level)
        (R.abs_completedRayCurvaturePotential_le wedges L center first level)
    _ = _ := by ring

/-- A complete trace accumulates only twice the curvature budget, regardless of its length. -/
theorem abs_completed_potential_changes_le (wedges : R.CurvedPathWedges)
    (L : Plane ≃ₗᵢ[ℝ] Plane) (center : Plane) (level : ℝ) {n : ℕ}
    (query : Fin (n + 1) → ℝ) :
    |∑ i : Fin n, (R.completedRayCurvaturePotential L center (query i.succ) level -
      R.completedRayCurvaturePotential L center (query i.castSucc) level)| ≤
        2 * C.totalInteriorAngularDefect Set.univ := by
  rw [sum_fin_succ_sub (fun i => R.completedRayCurvaturePotential L center (query i) level)]
  exact R.abs_completedRayCurvaturePotential_sub_le wedges L center _ _ level

end Unfoldings.ConvexCap.RadialCutForest
