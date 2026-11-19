module

public import Unfoldings.Polyhedron.BoundaryChainGeometry
public import Unfoldings.Polyhedron.ContourParentBankMetric
public import Unfoldings.Complex.RootwardChainLabels

/-! Original parent labels determine the full spatial interpolation of each source-bank edge. -/

@[expose] public section

namespace Unfoldings.SpatialFolding

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  (F : SpatialFolding C) {P : AscendingParents (C.Vertex Set.univ)}
  {retain : Set C.Seam} {m : ℕ} (chain : (C.boundarySystem retain).Chain m)
  (source : C.Vertex Set.univ) (span : P.distanceToRoot source = m + 1)
  (labels : ∀ k, C.vertexForgetCuts (Set.subset_univ _)
    (C.boundaryEndVertex _ (chain.point k)) = P.parent^[k.val] source)
  (terminal : C.vertexForgetCuts (Set.subset_univ _)
    (C.boundaryEndVertex _ (C.boundaryTurn _ chain.last)) = P.root source)

include span labels terminal

/-- Every original closed-edge parameter agrees with the original parent-edge interpolation. -/
theorem boundarySpatialChain_rootward_point (k : Fin (m + 1)) (t : unitInterval) :
    (F.boundarySpatialChain chain).point k t =
      AffineMap.lineMap
        (F.toSpace Set.univ (C.vertexPoint Set.univ (P.parent^[k.val] source)))
        (F.toSpace Set.univ (C.vertexPoint Set.univ (P.parent (P.parent^[k.val] source))))
        t.val := by
  rw [F.boundarySpatialChain_point, F.directedBoundaryPath_position,
    F.germDirection_boundary_positions]
  simp only [F.boundaryPosition_original_vertex]
  rw [labels k, C.rootwardChain_finish_original chain source span labels terminal k,
    Function.iterate_succ_apply', AffineMap.lineMap_apply_module']
  exact add_comm _ _

end Unfoldings.SpatialFolding
