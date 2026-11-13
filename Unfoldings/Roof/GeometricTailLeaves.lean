module

public import Unfoldings.Roof.GeometricTailCoalescence
public import Unfoldings.Roof.GeometricLeafAvoidance
public import Unfoldings.Roof.GeometricTailVertices

/-! A new geometric leaf is strictly separated from every distinct existing tail at its height. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof.SectorForest.SectorTailGraph

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexRoof C} {t : ℝ} {origin : Plane} {M : K.SectorForest t origin}
  {outer : Set Plane} {F : K.SkirtTailFamily outer (origin)}
  {covered : ∀ w : C.Vertex Set.univ, C.IsBoundaryVertex Set.univ w →
    K.projectedVertex w ∈ ⋃ c : F.Component, (F.componentTail c).carrier}
  {positive : 0 < t} {small : t < 1} {i : FiveSector}
  {leaf z : F.GeometricVertex}

/-- At the insertion height a distinct leaf is not on an already active actual tail. -/
theorem leaf_coordinate_ne (G : M.SectorTailGraph F covered positive small i z)
    (leaf_nonroot : leaf ∉ (M.geometricParents F covered positive small).roots)
    (childless : ∀ child ∉ (M.geometricParents F covered positive small).roots,
      M.geometricParent F covered child ≠ leaf) (different : z ≠ leaf)
    (start : M.geometricTailStartHeight F covered positive small i z ≤
      M.geometricTailStartHeight F covered positive small i leaf)
    (finish : M.geometricTailStartHeight F covered positive small i leaf <
      M.geometricTailEndHeight F covered positive small i z) :
    G.graph.coordinate (M.geometricTailStartHeight F covered positive small i leaf) ≠
      ((fiveSectorFrame t positive small i).place
        (F.geometricPosition leaf - origin)).re := by
  intro same
  let B := fiveSectorFrame t positive small i
  let Q := M.geometricParents F covered positive small
  let x := B.place (F.geometricPosition leaf - origin)
  let h := M.geometricTailStartHeight F covered positive small i leaf
  have height : x.re + x.im = h := rfl
  have at_leaf : G.graph.point h = x := by
    have point := G.graph.point_eq_of_coordinate x (height.symm ▸ same)
    rwa [height] at point
  have reaches := G.vertex_ancestor_of_point start finish at_leaf
  exact different ((Q.ancestor_childless_iff leaf_nonroot childless z).mp reaches)

end Unfoldings.ConvexRoof.SectorForest.SectorTailGraph
