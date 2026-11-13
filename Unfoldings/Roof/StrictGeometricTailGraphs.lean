module

public import Unfoldings.Cap.StrictGeometricTailGraphs

public import Unfoldings.Roof.GeometricSectorData
public import Unfoldings.Geometry.ChainStrictHeightGraph

/-! Actual geometric cut tails and enclosing sector walls progress in both coordinates. -/

@[expose] public section

noncomputable section

namespace Unfoldings

namespace ConvexRoof.SectorForest.SectorTailGraph

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexRoof C} {t : ℝ} {origin : Plane} {M : K.SectorForest t origin}
  {outer : Set Plane} {F : K.SkirtTailFamily outer (origin)}
  {covered : ∀ w : C.Vertex Set.univ, C.IsBoundaryVertex Set.univ w →
    K.projectedVertex w ∈ ⋃ c : F.Component, (F.componentTail c).carrier}
  {positive : 0 < t} {small : t < 1} {i : FiveSector}
  {w : F.GeometricVertex}

/-- Strictness follows from the represented whole-edge geometry, rather than being assumed
of an arbitrarily chosen height-graph extension. -/
theorem strictCoordinatesOn (G : M.SectorTailGraph F covered positive small i w)
    {a b : ℝ}
    (start : M.geometricTailStartHeight F covered positive small i w ≤ a)
    (finish : b < M.geometricTailEndHeight F covered positive small i w) :
    G.graph.StrictCoordinatesOn (Set.Icc a b) := by
  let P := M.geometricRootPath F covered positive small
    (fiveSectorFrame t positive small i).place w
  exact (P.heightGraph_strictCoordinatesOn G.graph G.pieces G.positive_steps).mono
    (fun _ member => ⟨start.trans member.1, member.2.trans_lt finish⟩)

end ConvexRoof.SectorForest.SectorTailGraph
end Unfoldings
