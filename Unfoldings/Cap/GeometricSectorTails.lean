module

public import Unfoldings.Cap.GeometricTailGraphs
public import Unfoldings.Cap.GeometricSectorNetwork

/-! Common-sector networks control actual tails from different geometric components. -/

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

/-- The covering network depends only on the fixed sector, allowing comparison of distinct
components. The represented graph agrees with every actual vertex and whole parent segment. -/
theorem exists_sector_tail_heightGraph (c : F.Component) (i : FiveSector)
    (directions : ∀ z : F.GeometricVertex,
      z ∉ (M.geometricParents F covered positive small lower).roots →
      M.geometricComponent F covered z = c →
        F.geometricPosition (M.geometricParent F covered z) - F.geometricPosition z ∈
          closedFiveSector t i)
    (w : F.GeometricVertex) (component : M.geometricComponent F covered w = c) :
    ∃ G : MonotoneHeightGraph,
      let P := M.geometricRootPath F covered positive small lower
        (fiveSectorFrame t positive small i).place w
      (∀ j, G.coordinate ((P.vertex j).re + (P.vertex j).im) = (P.vertex j).re) ∧
      (∀ j (s : unitInterval),
        G.coordinate ((P.point j s).re + (P.point j s).im) = (P.point j s).re) ∧
      ∀ h : ℝ, (P.vertex 0).re + (P.vertex 0).im ≤ h →
        h < (P.vertex (Fin.last _)).re + (P.vertex (Fin.last _)).im →
        G.point h ∈ (M.sectorHeightNetwork F covered positive small lower i).carrier := by
  let Q := M.geometricParents F covered positive small lower
  let B := fiveSectorFrame t positive small i
  let N := M.sectorHeightNetwork F covered positive small lower i
  let P := M.geometricRootPath F covered positive small lower B.place w
  have quadrant := M.geometricRootPath_coordinates_of_component_sector F covered positive small
    lower c i directions w component
  obtain ⟨G, vertices, representation⟩ := P.exists_heightGraph
    (fun j => ⟨(quadrant j).1.le, (quadrant j).2.le⟩)
    (fun j => add_pos (quadrant j).1 (quadrant j).2)
  refine ⟨G, vertices, representation, fun h start finish => ?_⟩
  obtain ⟨j, s, point⟩ := P.heightGraph_point_on_chain G representation
    (fun j => add_pos (quadrant j).1 (quadrant j).2) h start finish
  rw [point]
  let z := (M.geometricParent F covered)^[j.val] w
  have nonroot : z ∉ Q.roots := Q.iterate_lt_distanceToRoot_not_mem w j.isLt
  have label : M.geometricComponent F covered z = c :=
    (M.geometricComponent_iterate F covered w j.val).trans component
  let e : M.GeometricSectorEdge F covered positive small lower i :=
    ⟨z, nonroot, directions z nonroot label⟩
  refine Set.mem_iUnion.mpr ⟨e, ?_⟩
  have first : N.first e = P.vertex j.castSucc :=
    centeredPlaneFrame_apply (K.projectedVertex origin) B.place (F.geometricPosition z)
  have last : N.last e = P.vertex j.succ := by
    calc
      N.last e = B.place (F.geometricPosition (M.geometricParent F covered z) -
          K.projectedVertex origin) := centeredPlaneFrame_apply _ _ _
      _ = P.vertex j.succ := by
        change B.place (F.geometricPosition (M.geometricParent F covered z) -
          K.projectedVertex origin) = B.place
            (F.geometricPosition ((M.geometricParent F covered)^[j.val + 1] w) -
              K.projectedVertex origin)
        rw [Function.iterate_succ_apply']
  rw [first, last]
  exact lineMap_mem_segment ℝ _ _ s.property

end Unfoldings.ConvexCap.SectorForest
