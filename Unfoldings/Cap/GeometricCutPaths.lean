module

public import Unfoldings.Cap.GeometricCutLabels
public import Unfoldings.Cap.ExtendedCutEmbedding
public import Unfoldings.Geometry.FiveSectorFrames
public import Unfoldings.Geometry.ChainHeightGraph

/-! Exact monotone height graphs for all complete geometric cut paths. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap.SectorForest

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexCap C} {t : ℝ} {origin : C.Vertex Set.univ} (M : K.SectorForest t origin)
  {Z : ℝ} (F : K.SkirtTailFamily Z (K.projectedVertex origin))
  (covered : ∀ w : C.Vertex Set.univ, C.IsBoundaryVertex Set.univ w →
    K.projectedVertex w ∈ ⋃ c : F.Component, (F.componentTail c).carrier)
  (positive : 0 < t) (small : t < 1) (lower : Z < 0)

def geometricRootPath (frame : Plane ≃ₗᵢ[ℝ] ℂ) (w : F.GeometricVertex) :
    PolygonalChain ℂ ((M.geometricParents F covered positive small lower).distanceToRoot w) where
  vertex j := frame (F.geometricPosition
    ((M.geometricParent F covered)^[j.val] w) - K.projectedVertex origin)

theorem geometricRootPath_edge (frame : Plane ≃ₗᵢ[ℝ] ℂ) (w : F.GeometricVertex)
    (j : Fin ((M.geometricParents F covered positive small lower).distanceToRoot w)) :
    (M.geometricRootPath F covered positive small lower frame w).edge j =
      frame (F.geometricPosition
        (M.geometricParent F covered ((M.geometricParent F covered)^[j.val] w)) -
          F.geometricPosition ((M.geometricParent F covered)^[j.val] w)) := by
  change frame (F.geometricPosition ((M.geometricParent F covered)^[j.val + 1] w) -
    K.projectedVertex origin) - frame (F.geometricPosition
      ((M.geometricParent F covered)^[j.val] w) - K.projectedVertex origin) = _
  rw [← map_sub, Function.iterate_succ_apply']
  congr 1
  abel

/-- Strict projection quadrant increments hold along every whole path, including independent
skirt components. The sector is constant along the actual parent orbit. -/
theorem exists_geometricRootPath_positive_coordinates (w : F.GeometricVertex) :
    ∃ i : FiveSector, ∀ j,
      0 < ((M.geometricRootPath F covered positive small lower
        (fiveSectorFrame t positive small i).place w).edge j).re ∧
      0 < ((M.geometricRootPath F covered positive small lower
        (fiveSectorFrame t positive small i).place w).edge j).im := by
  let P := M.geometricParents F covered positive small lower
  obtain ⟨i, directions⟩ := M.exists_geometric_component_sector F covered positive small lower
    (M.geometricComponent F covered w)
  refine ⟨i, fun j => ?_⟩
  let z := (M.geometricParent F covered)^[j.val] w
  have nonroot : z ∉ P.roots := P.iterate_lt_distanceToRoot_not_mem w j.isLt
  have component : M.geometricComponent F covered z = M.geometricComponent F covered w :=
    M.geometricComponent_iterate F covered w j.val
  let direction := F.geometricPosition (M.geometricParent F covered z) - F.geometricPosition z
  have inside : direction ∈ closedFiveSector t i := directions z nonroot component
  have genuine : direction ≠ 0 := by
    intro zero
    have equal := F.geometricPosition_injective lower (sub_eq_zero.mp zero)
    have ascending := P.ascending z nonroot
    change P.height z < P.height (M.geometricParent F covered z) at ascending
    rw [equal] at ascending
    exact lt_irrefl _ ascending
  let B := fiveSectorFrame t positive small i
  have frame_ne : B.place direction ≠ 0 := by
    simpa only [map_zero] using B.place.injective.ne genuine
  have close : InnerProductGeometry.angle (B.place direction) (B.place direction) < B.margin := by
    rw [InnerProductGeometry.angle_self frame_ne]
    exact B.positive
  have quadrant := B.quadrant_of_angle_close inside genuine close
  rw [M.geometricRootPath_edge]
  exact quadrant

/-- Preserve all original and radial path segments in one exact height graph. These are
geometric paths, before any auxiliary face subdivision or strip connector is chosen. -/
theorem exists_geometricRootPath_heightGraph (w : F.GeometricVertex) :
    ∃ i : FiveSector, ∃ G : MonotoneHeightGraph,
      let P := M.geometricRootPath F covered positive small lower
        (fiveSectorFrame t positive small i).place w
      (∀ j, G.coordinate ((P.vertex j).re + (P.vertex j).im) = (P.vertex j).re) ∧
      ∀ j (s : unitInterval),
        G.coordinate ((P.point j s).re + (P.point j s).im) = (P.point j s).re := by
  obtain ⟨i, directions⟩ := M.exists_geometricRootPath_positive_coordinates F covered positive
    small lower w
  obtain ⟨G, vertices, points⟩ :=
    (M.geometricRootPath F covered positive small lower (fiveSectorFrame t positive small i).place
      w).exists_heightGraph (fun j => ⟨(directions j).1.le, (directions j).2.le⟩)
        (fun j => add_pos (directions j).1 (directions j).2)
  exact ⟨i, G, vertices, points⟩

end Unfoldings.ConvexCap.SectorForest
