module

public import Unfoldings.Cap.SubtreeAngles
public import Unfoldings.Geometry.ThreeSectorCoordinates
public import Unfoldings.Geometry.LevelCrossings
public import Unfoldings.Topology.SubtreeWeights

/-!
# Actual signed section crossings of the constructed sector forest

Each original-edge root path is monotone in one ambient coordinate, giving a
signed horizontal-ray crossing count of magnitude at most one. Regrouping
nested subtree curvatures therefore bounds the total signed bank correction
by the actual total curvature, independently of mesh size and tree depth.
The counters use a half-open endpoint convention; they are not noncrossing tests.
-/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap.SectorForest

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexCap C} {t : ℝ} {origin : C.Vertex Set.univ} (M : K.SectorForest t origin)

/-- The three path labels yield upward, leftward, or downward coordinate monotonicity. -/
theorem rootPath_coordinate_monotone (nonnegative : 0 ≤ t) (small : t < 1)
    (v : C.Vertex Set.univ) :
    Monotone (fun i => (M.rootPath v).vertex i 1) ∨
      Antitone (fun i => (M.rootPath v).vertex i 0) ∨
      Antitone (fun i => (M.rootPath v).vertex i 1) := by
  have inside := M.rootPath_directions nonnegative small v
  generalize label_eq : K.sourceSectorLabel t origin v = label at inside
  fin_cases label
  · left
    apply Fin.monotone_iff_le_succ.mpr
    intro i
    have coordinate := closedThreeSector_upper_y nonnegative small
      (strictThreeSector_subset_closed _ _ (inside i))
    change 0 ≤ (M.rootPath v).vertex i.succ 1 - (M.rootPath v).vertex i.castSucc 1 at coordinate
    exact sub_nonneg.mp coordinate
  · right; left
    apply Fin.antitone_iff_succ_le.mpr
    intro i
    have coordinate := closedThreeSector_middle_x nonnegative small
      (strictThreeSector_subset_closed _ _ (inside i))
    change (M.rootPath v).vertex i.succ 0 - (M.rootPath v).vertex i.castSucc 0 ≤ 0 at coordinate
    exact sub_nonpos.mp coordinate
  · right; right
    apply Fin.antitone_iff_succ_le.mpr
    intro i
    have coordinate := closedThreeSector_lower_y nonnegative small
      (strictThreeSector_subset_closed _ _ (inside i))
    change (M.rootPath v).vertex i.succ 1 - (M.rootPath v).vertex i.castSucc 1 ≤ 0 at coordinate
    exact sub_nonpos.mp coordinate

/-- All original edges and all half-open endpoint cases are included in the signed count. -/
theorem abs_rootPath_rayCrossings_le_one (nonnegative : 0 ≤ t) (small : t < 1)
    (v : C.Vertex Set.univ) (cut level : ℝ) :
    |∑ i : Fin (M.parents.distanceToRoot v), horizontalRayCrossing
      (fun j => (M.rootPath v).vertex j 0)
      (fun j => (M.rootPath v).vertex j 1) cut level i| ≤ 1 := by
  rcases M.rootPath_coordinate_monotone nonnegative small v with up | leftward | down
  · exact abs_sum_horizontalRayCrossing_of_monotone_y _ _ up cut level
  · exact abs_sum_horizontalRayCrossing_of_antitone_x _ _ leftward cut level
  · exact abs_sum_horizontalRayCrossing_of_antitone_y _ _ down cut level

/-- The signed ray crossing of a vertex's actual original parent edge. Roots contribute zero. -/
def parentRayCrossing (cut level : ℝ) (v : C.Vertex Set.univ) : ℝ :=
  let a := K.projectedVertex v
  let b := K.projectedVertex (M.parents.parent v)
  let parameter := levelCrossingParameter (a 1) (b 1) level
  if cut < (1 - parameter) * a 0 + parameter * b 0 then
    levelIndicator level (b 1) - levelIndicator level (a 1) else 0

theorem rootPath_crossing_eq_parent (cut level : ℝ) (v : C.Vertex Set.univ)
    (i : Fin (M.parents.distanceToRoot v)) :
    horizontalRayCrossing (fun j => (M.rootPath v).vertex j 0)
      (fun j => (M.rootPath v).vertex j 1) cut level i =
      M.parentRayCrossing cut level (M.parents.parent^[i.val] v) := by
  simp only [horizontalRayCrossing, levelCrossingPosition, parentRayCrossing, rootPath,
    Fin.val_succ, Fin.val_castSucc, Function.iterate_succ_apply']

open scoped Classical in
/-- No descendant curvature is charged more than once after the actual signed crossings cancel. -/
theorem abs_weighted_parentRayCrossings_le_totalCurvature (nonnegative : 0 ≤ t) (small : t < 1)
    (cut level : ℝ) :
    |∑ e : C.Vertex Set.univ, if e ∉ M.parents.roots then
      M.parentRayCrossing cut level e * M.subtreeCurvature e else 0| ≤
        C.totalInteriorAngularDefect Set.univ := by
  classical
  apply M.parents.abs_sum_subtree_weights_le
    (fun v => C.interiorAngularDefect Set.univ v) (M.parentRayCrossing cut level)
    K.interiorCurvature_nonneg
  intro v
  simpa only [M.rootPath_crossing_eq_parent cut level] using
    M.abs_rootPath_rayCrossings_le_one nonnegative small v cut level

end Unfoldings.ConvexCap.SectorForest
