module

public import Unfoldings.Roof.GeometricTailCoalescence
public import Unfoldings.Roof.GeometricSectorData
public import Unfoldings.Geometry.HeightNetworkLocalGraph

/-! Actual regular tail points avoid network vertices and retain a local physical edge graph. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof.SectorForest

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexRoof C} {t : ℝ} {origin : Plane} (M : K.SectorForest t origin)
  {outer : Set Plane} (F : K.SkirtTailFamily outer (origin))
  (covered : ∀ w : C.Vertex Set.univ, C.IsBoundaryVertex Set.univ w →
    K.projectedVertex w ∈ ⋃ c : F.Component, (F.componentTail c).carrier)
  (positive : 0 < t) (small : t < 1)

theorem sectorHeightNetwork_coordinate_steps (i : FiveSector)
    (e : M.GeometricSectorEdge F covered positive small i) :
    let N := M.sectorHeightNetwork F covered positive small i
    (N.first e).re ≤ (N.last e).re ∧ (N.first e).im ≤ (N.last e).im := by
  let B := fiveSectorFrame t positive small i
  let N := M.sectorHeightNetwork F covered positive small i
  have movement : N.last e - N.first e =
      B.place (F.geometricPosition (M.geometricParent F covered e.val) -
        F.geometricPosition e.val) := by
    change centeredPlaneFrame _ _ _ - centeredPlaneFrame _ _ _ = _
    rw [centeredPlaneFrame_apply, centeredPlaneFrame_apply, ← B.place.map_sub]
    congr 1
    abel
  have quadrant := B.quadrant_nonneg e.property.2
  rw [← movement, Complex.sub_re, Complex.sub_im] at quadrant
  exact ⟨sub_nonneg.mp quadrant.1, sub_nonneg.mp quadrant.2⟩

end Unfoldings.ConvexRoof.SectorForest
