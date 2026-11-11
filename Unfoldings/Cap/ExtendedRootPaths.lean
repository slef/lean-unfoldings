module

public import Unfoldings.Cap.RimTails
public import Unfoldings.Geometry.ChainAppend

/-! Original root paths and their complete outward continuations retain one strict acute wedge. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap.SectorForest

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexCap C} {t : ℝ} {origin : C.Vertex Set.univ} (M : K.SectorForest t origin)

/-- Append the entire projected continuation to an arbitrary point beyond the original rim. -/
def extendedRootPath (w : C.Vertex Set.univ) (a : ℝ) :
    PolygonalChain Plane (M.parents.distanceToRoot w + 1) :=
  (M.rootPath w).snoc (M.projectedRimTail (M.parents.root w) a)

theorem extendedRootPath_last_edge (w : C.Vertex Set.univ) (a : ℝ) :
    (M.extendedRootPath w a).edge (Fin.last (M.parents.distanceToRoot w)) =
      (a - 1) • (K.projectedVertex (M.parents.root w) - K.projectedVertex origin) := by
  rw [extendedRootPath, PolygonalChain.snoc_edge_last, M.rootPath_end]
  unfold projectedRimTail
  module

/-- No new angle budget is consumed by appending the whole radial continuation. -/
theorem extendedRootPath_angleMonotone (positive : 0 < t) (small : t < 1)
    (origin_internal : ¬ C.IsBoundaryVertex Set.univ origin)
    (w : C.Vertex Set.univ) (internal : ¬ C.IsBoundaryVertex Set.univ w)
    {a : ℝ} (beyond : 1 ≤ a) :
    (M.extendedRootPath w a).AngleMonotone
      (threeSectorWidth t (K.sourceSectorLabel t origin w)) := by
  let i := K.sourceSectorLabel t origin w
  have banks := threeSector_banks_inner_pos positive small i
  have old_directions : ∀ j, InDirectionWedge (threeSectorRay t i.castSucc)
      (threeSectorRay t i.succ) ((M.rootPath w).edge j) := fun j =>
    inDirectionWedge_of_closedThreeSector positive.le small i
      (strictThreeSector_subset_closed t i (M.rootPath_directions positive.le small w j))
  have radial := (M.root_radial_direction positive.le small origin_internal w internal).1
  have scaled : (a - 1) •
      (K.projectedVertex (M.parents.root w) - K.projectedVertex origin) ∈
        closedThreeSector t i := by
    change 0 ≤ threeSectorCoordinates t i ((a - 1) •
      (K.projectedVertex (M.parents.root w) - K.projectedVertex origin)) 0 ∧
        0 ≤ threeSectorCoordinates t i ((a - 1) •
          (K.projectedVertex (M.parents.root w) - K.projectedVertex origin)) 1
    rw [map_smul]
    exact ⟨mul_nonneg (sub_nonneg.mpr beyond) radial.1,
      mul_nonneg (sub_nonneg.mpr beyond) radial.2⟩
  have final : InDirectionWedge (threeSectorRay t i.castSucc) (threeSectorRay t i.succ)
      (M.projectedRimTail (M.parents.root w) a -
        (M.rootPath w).vertex (Fin.last (M.parents.distanceToRoot w))) := by
    have equal := M.extendedRootPath_last_edge w a
    rw [extendedRootPath, PolygonalChain.snoc_edge_last] at equal
    rw [equal]
    exact inDirectionWedge_of_closedThreeSector positive.le small i scaled
  refine ⟨threeSectorRay t i.castSucc, threeSectorRay t i.succ, ?_, ?_, le_rfl,
    (M.rootPath w).snoc_directions old_directions final⟩
  · intro zero
    rw [zero, inner_zero_left] at banks
    exact lt_irrefl _ banks
  · intro zero
    rw [zero, inner_zero_right] at banks
    exact lt_irrefl _ banks

/-- All earlier points, rather than only the original source, see a radially monotone path. -/
theorem extendedRootPath_globallyRadiallyMonotone (positive : 0 < t) (small : t < 1)
    (origin_internal : ¬ C.IsBoundaryVertex Set.univ origin)
    (w : C.Vertex Set.univ) (internal : ¬ C.IsBoundaryVertex Set.univ w)
    {a : ℝ} (beyond : 1 ≤ a) : (M.extendedRootPath w a).GloballyRadiallyMonotone := by
  have radial := (M.extendedRootPath_angleMonotone positive small origin_internal w internal
    beyond).radiallyMonotone (M.extendedRootPath w a)
      (threeSectorWidth_lt_pi_div_two positive small _).le
  exact radial.globallyRadiallyMonotone

end Unfoldings.ConvexCap.SectorForest
