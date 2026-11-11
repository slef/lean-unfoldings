module

public import Unfoldings.Cap.GeometricSectorData
public import Unfoldings.Geometry.ChainStrictHeightGraph

/-! Actual geometric cut tails and enclosing sector walls progress in both coordinates. -/

@[expose] public section

noncomputable section

namespace Unfoldings

namespace AcuteWedgeFrame

variable {u v : Plane} (B : AcuteWedgeFrame u v)

theorem enclosingStrip_strictCoordinatesOn (s : Set ℝ) :
    B.enclosingStrip.lower.StrictCoordinatesOn s ∧
      B.enclosingStrip.upper.StrictCoordinatesOn s :=
  MonotoneStrip.rayStrip_strictCoordinatesOn _ _ _ _ _ _ s

end AcuteWedgeFrame

namespace ConvexCap.SectorForest.SectorTailGraph

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexCap C} {t : ℝ} {origin : C.Vertex Set.univ} {M : K.SectorForest t origin}
  {Z : ℝ} {F : K.SkirtTailFamily Z (K.projectedVertex origin)}
  {covered : ∀ w : C.Vertex Set.univ, C.IsBoundaryVertex Set.univ w →
    K.projectedVertex w ∈ ⋃ c : F.Component, (F.componentTail c).carrier}
  {positive : 0 < t} {small : t < 1} {lower : Z < 0} {i : FiveSector}
  {w : F.GeometricVertex}

/-- Strictness follows from the represented whole-edge geometry, rather than being assumed
of an arbitrarily chosen height-graph extension. -/
theorem strictCoordinatesOn (G : M.SectorTailGraph F covered positive small lower i w)
    {a b : ℝ}
    (start : M.geometricTailStartHeight F covered positive small lower i w ≤ a)
    (finish : b < M.geometricTailEndHeight F covered positive small lower i w) :
    G.graph.StrictCoordinatesOn (Set.Icc a b) := by
  let P := M.geometricRootPath F covered positive small lower
    (fiveSectorFrame t positive small i).place w
  exact (P.heightGraph_strictCoordinatesOn G.graph G.pieces G.positive_steps).mono
    (fun _ member => ⟨start.trans member.1, member.2.trans_lt finish⟩)

end ConvexCap.SectorForest.SectorTailGraph
end Unfoldings
