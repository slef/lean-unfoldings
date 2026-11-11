module

public import Unfoldings.Cap.GeometricSectorPositions
public import Unfoldings.Cap.GeometricTailLeaves
public import Unfoldings.Geometry.RayStrip

/-! Actual component sector choices and exact enclosing strips for their geometric tails. -/

@[expose] public section

noncomputable section

namespace Unfoldings

namespace AcuteWedgeFrame

variable {u v : Plane} (B : AcuteWedgeFrame u v)

theorem quadrant_self {x : Plane} (inside : InDirectionWedge u v x) (nonzero : x ≠ 0) :
    0 < (B.place x).re ∧ 0 < (B.place x).im := by
  have genuine : B.place x ≠ 0 := by simpa only [map_zero] using B.place.injective.ne nonzero
  exact B.quadrant_of_angle_close inside nonzero
    (by rw [InnerProductGeometry.angle_self genuine]; exact B.positive)

theorem quadrant_nonneg {x : Plane} (inside : InDirectionWedge u v x) :
    0 ≤ (B.place x).re ∧ 0 ≤ (B.place x).im := by
  by_cases zero : x = 0
  · simp [zero]
  · exact ⟨(B.quadrant_self inside zero).1.le, (B.quadrant_self inside zero).2.le⟩

def enclosingStrip : MonotoneStrip :=
  let first := B.quadrant_self (x := u) ⟨1, 0, by norm_num, le_rfl, by simp⟩ B.first_ne
  let last := B.quadrant_self (x := v) ⟨0, 1, le_rfl, by norm_num, by simp⟩ B.last_ne
  MonotoneStrip.rayStrip (B.place u) (B.place v) first.1 first.2 last.1 last.2

theorem enclosingStrip_source : B.enclosingStrip.lower.coordinate 0 = 0 ∧
    B.enclosingStrip.upper.coordinate 0 = 0 := MonotoneStrip.rayStrip_source _ _ _ _ _ _

theorem enclosingStrip_mem {x : Plane} (inside : InDirectionWedge u v x) :
    B.place x ∈ B.enclosingStrip.carrier :=
  MonotoneStrip.rayStrip_of_cone _ _ _ _ _ _
    (inside.map B.place.toLinearEquiv.toLinearMap)

end AcuteWedgeFrame

namespace ConvexCap.SectorForest

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexCap C} {t : ℝ} {origin : C.Vertex Set.univ} (M : K.SectorForest t origin)
  {Z : ℝ} (F : K.SkirtTailFamily Z (K.projectedVertex origin))
  (covered : ∀ w : C.Vertex Set.univ, C.IsBoundaryVertex Set.univ w →
    K.projectedVertex w ∈ ⋃ c : F.Component, (F.componentTail c).carrier)
  (positive : 0 < t) (small : t < 1) (lower : Z < 0)

/-- Choose sectors from the proved geometry, retaining both positional and directional bounds. -/
structure GeometricComponentSector (c : F.Component) where
  sector : FiveSector
  positions : ∀ w : F.GeometricVertex, M.geometricComponent F covered w = c →
    F.geometricPosition w - K.projectedVertex origin ∈ closedFiveSector t sector
  directions : ∀ w : F.GeometricVertex,
    w ∉ (M.geometricParents F covered positive small lower).roots →
    M.geometricComponent F covered w = c →
      F.geometricPosition (M.geometricParent F covered w) - F.geometricPosition w ∈
        closedFiveSector t sector

def geometricComponentSector (c : F.Component) :
    M.GeometricComponentSector F covered positive small lower c :=
  Classical.choice (by
    obtain ⟨i, positions, directions⟩ :=
      M.exists_geometric_component_sector_positions F covered positive small lower c
    exact ⟨⟨i, positions, directions⟩⟩)

def GeometricSectorLeaf (i : FiveSector) :=
  {w : F.GeometricVertex //
    w ∉ (M.geometricParents F covered positive small lower).roots ∧
      (∀ child ∉ (M.geometricParents F covered positive small lower).roots,
        M.geometricParent F covered child ≠ w) ∧
      (M.geometricComponentSector F covered positive small lower
        (M.geometricComponent F covered w)).sector = i}

instance geometricSectorLeafFinite (i : FiveSector) :
    Finite (M.GeometricSectorLeaf F covered positive small lower i) := by
  unfold GeometricSectorLeaf
  infer_instance

namespace GeometricSectorLeaf

variable {M F covered positive small lower} {i : FiveSector}
  (w : M.GeometricSectorLeaf F covered positive small lower i)

theorem component_positions (z : F.GeometricVertex)
    (same : M.geometricComponent F covered z = M.geometricComponent F covered w.val) :
    F.geometricPosition z - K.projectedVertex origin ∈ closedFiveSector t i := by
  rw [← w.property.2.2]
  exact (M.geometricComponentSector F covered positive small lower _).positions z same

theorem component_directions (z : F.GeometricVertex)
    (nonroot : z ∉ (M.geometricParents F covered positive small lower).roots)
    (same : M.geometricComponent F covered z = M.geometricComponent F covered w.val) :
    F.geometricPosition (M.geometricParent F covered z) - F.geometricPosition z ∈
      closedFiveSector t i := by
  rw [← w.property.2.2]
  exact (M.geometricComponentSector F covered positive small lower _).directions z nonroot same

def tailGraph : M.SectorTailGraph F covered positive small lower i w.val :=
  M.sectorTailGraph F covered positive small lower (M.geometricComponent F covered w.val) i
    w.component_directions w.val rfl

def point : ℂ := (fiveSectorFrame t positive small i).place
  (F.geometricPosition w.val - K.projectedVertex origin)

theorem point_nonnegative : 0 ≤ w.point.re ∧ 0 ≤ w.point.im :=
  (fiveSectorFrame t positive small i).quadrant_nonneg (w.component_positions w.val rfl)

theorem tailGraph_target : w.tailGraph.graph.coordinate (w.point.re + w.point.im) = w.point.re :=
  w.tailGraph.vertices 0

/-- Every intermediate graph point is on an actual whole edge inside the enclosing sector. -/
theorem tailGraph_mem_strip {h : ℝ}
    (start : w.point.re + w.point.im ≤ h)
    (finish : h < M.geometricTailEndHeight F covered positive small lower i w.val) :
    w.tailGraph.graph.point h ∈ (fiveSectorFrame t positive small i).enclosingStrip.carrier := by
  let B := fiveSectorFrame t positive small i
  let P := M.geometricRootPath F covered positive small lower B.place w.val
  have vertices : ∀ j, InDirectionWedge (B.place (fiveSectorFirst t i))
      (B.place (fiveSectorLast t i)) (P.vertex j) := by
    intro j
    exact (w.component_positions _
      (M.geometricComponent_iterate F covered w.val j.val)).map B.place.toLinearEquiv.toLinearMap
  obtain ⟨j, s, equal⟩ := P.heightGraph_point_on_chain w.tailGraph.graph w.tailGraph.pieces
    (fun j => add_pos (w.tailGraph.positive_steps j).1 (w.tailGraph.positive_steps j).2) h
    start finish
  rw [equal]
  have on_segment : P.point j s ∈ segment ℝ (P.vertex j.castSucc) (P.vertex j.succ) :=
    lineMap_mem_segment ℝ _ _ s.property
  have in_cone := (convex_inDirectionWedge (B.place (fiveSectorFirst t i))
    (B.place (fiveSectorLast t i))).segment_subset (vertices j.castSucc) (vertices j.succ)
    on_segment
  exact MonotoneStrip.rayStrip_of_cone _ _ _ _ _ _ in_cone

end GeometricSectorLeaf
end ConvexCap.SectorForest
end Unfoldings
