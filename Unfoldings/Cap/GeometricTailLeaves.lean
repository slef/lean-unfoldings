module

public import Unfoldings.Cap.GeometricTailCoalescence
public import Unfoldings.Cap.GeometricLeafAvoidance
public import Unfoldings.Cap.GeometricTailVertices

/-! A new geometric leaf is strictly separated from every distinct existing tail at its height. -/

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
  {leaf z : F.GeometricVertex}

/-- At the insertion height a distinct leaf is not on an already active actual tail. -/
theorem leaf_coordinate_ne (G : M.SectorTailGraph F covered positive small lower i z)
    (leaf_nonroot : leaf ∉ (M.geometricParents F covered positive small lower).roots)
    (childless : ∀ child ∉ (M.geometricParents F covered positive small lower).roots,
      M.geometricParent F covered child ≠ leaf) (different : z ≠ leaf)
    (start : M.geometricTailStartHeight F covered positive small lower i z ≤
      M.geometricTailStartHeight F covered positive small lower i leaf)
    (finish : M.geometricTailStartHeight F covered positive small lower i leaf <
      M.geometricTailEndHeight F covered positive small lower i z) :
    G.graph.coordinate (M.geometricTailStartHeight F covered positive small lower i leaf) ≠
      ((fiveSectorFrame t positive small i).place
        (F.geometricPosition leaf - K.projectedVertex origin)).re := by
  intro same
  let B := fiveSectorFrame t positive small i
  let Q := M.geometricParents F covered positive small lower
  let x := B.place (F.geometricPosition leaf - K.projectedVertex origin)
  let h := M.geometricTailStartHeight F covered positive small lower i leaf
  have height : x.re + x.im = h := rfl
  have at_leaf : G.graph.point h = x := by
    have point := G.graph.point_eq_of_coordinate x (height.symm ▸ same)
    rwa [height] at point
  have reaches := G.vertex_ancestor_of_point start finish at_leaf
  exact different ((Q.ancestor_childless_iff leaf_nonroot childless z).mp reaches)

end Unfoldings.ConvexCap.SectorForest.SectorTailGraph
