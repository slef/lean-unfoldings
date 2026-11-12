module

public import Unfoldings.Cap.GeometricTailCoalescence
public import Unfoldings.Cap.GeometricCutIncidence
public import Unfoldings.Cap.GeometricTailPieces

/-! A geometric vertex on an actual tail is an ancestor in that same cut component. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap.SectorForest.SectorTailGraph

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexCap C} {t : ℝ} {origin : C.Vertex Set.univ} {M : K.SectorForest t origin}
  {Z : ℝ} {F : K.SkirtTailFamily Z (K.projectedVertex origin)}
  {covered : ∀ w : C.Vertex Set.univ, C.IsBoundaryVertex Set.univ w →
    K.projectedVertex w ∈ ⋃ c : F.Component, (F.componentTail c).carrier}
  {positive : 0 < t} {small : t < 1} {lower : Z < 0} {i : FiveSector}
  {w z : F.GeometricVertex}

theorem vertex_ancestor_of_point (G : M.SectorTailGraph F covered positive small lower i w)
    {h : ℝ} (start : M.geometricTailStartHeight F covered positive small lower i w ≤ h)
    (finish : h < M.geometricTailEndHeight F covered positive small lower i w)
    (at_vertex : G.graph.point h = (fiveSectorFrame t positive small i).place
      (F.geometricPosition z - K.projectedVertex origin)) :
    (M.geometricParents F covered positive small lower).Ancestor w z := by
  obtain ⟨v, nonroot, ancestor, member⟩ := G.exists_parent_edge_at_point start finish at_vertex
  rcases M.geometric_vertex_on_parent_endpoint F covered positive small lower z v nonroot member
      with first | last
  · exact first.symm ▸ ancestor
  · exact ancestor.trans (M.geometricParents F covered positive small lower) ⟨1, last.symm⟩

theorem vertex_component_of_point (G : M.SectorTailGraph F covered positive small lower i w)
    {h : ℝ} (start : M.geometricTailStartHeight F covered positive small lower i w ≤ h)
    (finish : h < M.geometricTailEndHeight F covered positive small lower i w)
    (at_vertex : G.graph.point h = (fiveSectorFrame t positive small i).place
      (F.geometricPosition z - K.projectedVertex origin)) :
    M.geometricComponent F covered z = M.geometricComponent F covered w := by
  obtain ⟨n, equal⟩ := G.vertex_ancestor_of_point start finish at_vertex
  rw [← equal]
  exact M.geometricComponent_iterate F covered w n

end Unfoldings.ConvexCap.SectorForest.SectorTailGraph
