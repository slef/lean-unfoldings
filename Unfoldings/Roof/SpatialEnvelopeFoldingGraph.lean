module

public import Unfoldings.Roof.SpatialEnvelopeBoundaryChains

/-! Every retained physical bank point is the original whole roof graph point. -/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialEnvelope.Triangulation

universe u

variable {I : Type u} [Fintype I] [Nonempty I] {family : I → SpatialPlane} {Z : ℝ}
  (T : Triangulation family Z)

local instance foldingGraphIndexFintype : Fintype T.Index := @Fintype.ofFinite _ T.finite

/-- Restoring any subset of original seams keeps the exact whole spatial graph point. -/
theorem toSpace_eq_point (retain : Set T.pairedComplex.Seam)
    (x : T.pairedComplex.Realization retain) :
    T.pairedFolding.toSpace retain x =
      point family (Cap.horizontal (T.pairedFolding.toSpace retain x)) := by
  obtain ⟨⟨f, p⟩, rfl⟩ :=
    MetricGluing.point_surjective T.pairedComplex.Cell (T.pairedComplex.glue retain) x
  change T.placement f p.val = point family (Cap.horizontal (T.placement f p.val))
  rw [T.placement_eq_point f p.property, horizontal_point]

variable {retain : Set T.pairedComplex.Seam} {n : ℕ}
  (chain : (T.pairedComplex.boundarySystem retain).Chain n)

/-- Each actual boundary bank has the exact original whole roof coordinate at every point. -/
theorem boundarySpatialChain_point_eq_graph (i : Fin (n + 1)) (t : unitInterval) :
    (T.pairedFolding.boundarySpatialChain chain).point i t =
      point family ((T.projectedBoundaryChain chain).point i t) := by
  change _ = point family
    (((T.pairedFolding.boundarySpatialChain chain).affineMap Cap.horizontal.toAffineMap).point i t)
  rw [PolygonalChain.affineMap_point, T.pairedFolding.boundarySpatialChain_point]
  exact T.toSpace_eq_point retain _

/-- In particular, every original endpoint copy retains its complete spatial roof coordinate. -/
theorem boundarySpatialChain_vertex_eq_graph (j : Fin (n + 2)) :
    (T.pairedFolding.boundarySpatialChain chain).vertex j =
      point family ((T.projectedBoundaryChain chain).vertex j) := by
  refine Fin.lastCases ?_ (fun k => ?_) j
  · have endpoint := T.boundarySpatialChain_point_eq_graph chain (Fin.last n) 1
    simpa only [PolygonalChain.point_one, Fin.succ_last] using endpoint
  · have endpoint := T.boundarySpatialChain_point_eq_graph chain k 0
    simpa only [PolygonalChain.point_zero] using endpoint

end Unfoldings.SpatialEnvelope.Triangulation
