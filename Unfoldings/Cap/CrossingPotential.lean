module

public import Unfoldings.Cap.SectorFrameCrossings
public import Unfoldings.Topology.OrderedChanges

/-!
# A bounded actual forest-crossing curvature potential

The signed ray sum at each query is bounded by total cap curvature. Differences
between queries, and telescoped differences along a whole trace, are therefore
bounded by twice that curvature. No per-edge or per-vertex error is added.
-/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap.SectorForest

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexCap C} {t : ℝ} {origin : C.Vertex Set.univ} (M : K.SectorForest t origin)

open scoped Classical in
/-- Signed curvature of actual original parent-edge crossings of a prescribed ray. -/
def rayCurvaturePotential (L : Plane ≃ₗᵢ[ℝ] Plane) (center : Plane) (cut level : ℝ) : ℝ :=
  ∑ e : C.Vertex Set.univ, if e ∉ M.parents.roots then
    M.parentRayCrossingInFrame L center cut level e * M.subtreeCurvature e else 0

theorem abs_rayCurvaturePotential_le (positive : 0 < t) (small : t < 1)
    (L : Plane ≃ₗᵢ[ℝ] Plane) (center : Plane) (cut level : ℝ) :
    |M.rayCurvaturePotential L center cut level| ≤ C.totalInteriorAngularDefect Set.univ :=
  M.abs_weighted_parentRayCrossings_inFrame_le_totalCurvature positive small L center cut level

/-- Two actual ray queries differ by at most twice the total original cap curvature. -/
theorem abs_rayCurvaturePotential_sub_le (positive : 0 < t) (small : t < 1)
    (L : Plane ≃ₗᵢ[ℝ] Plane) (center : Plane) (first last level : ℝ) :
    |M.rayCurvaturePotential L center last level - M.rayCurvaturePotential L center first level| ≤
      2 * C.totalInteriorAngularDefect Set.univ := by
  calc
    _ ≤ |M.rayCurvaturePotential L center last level| +
        |M.rayCurvaturePotential L center first level| := abs_sub _ _
    _ ≤ C.totalInteriorAngularDefect Set.univ + C.totalInteriorAngularDefect Set.univ :=
      add_le_add (M.abs_rayCurvaturePotential_le positive small L center last level)
        (M.abs_rayCurvaturePotential_le positive small L center first level)
    _ = _ := by ring

/-- Signed corrections telescope before their absolute value is bounded. -/
theorem abs_sum_rayCurvaturePotential_changes_le (positive : 0 < t) (small : t < 1)
    (L : Plane ≃ₗᵢ[ℝ] Plane) (center : Plane) (level : ℝ) {n : ℕ}
    (query : Fin (n + 1) → ℝ) :
    |∑ i : Fin n, (M.rayCurvaturePotential L center (query i.succ) level -
      M.rayCurvaturePotential L center (query i.castSucc) level)| ≤
      2 * C.totalInteriorAngularDefect Set.univ := by
  rw [sum_fin_succ_sub (fun i => M.rayCurvaturePotential L center (query i) level)]
  exact M.abs_rayCurvaturePotential_sub_le positive small L center _ _ level

end Unfoldings.ConvexCap.SectorForest
