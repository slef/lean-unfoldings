module

public import Unfoldings.Complex.BoundaryCycles
public import Unfoldings.Complex.Folding
public import Unfoldings.Topology.GraphEmbedding
public import Unfoldings.Topology.GraphDrawing

/-!
# Actual bank cycles in planar embeddings are Jordan curves

The prescribed maps are the actual metric bank parametrizations, transported
through a continuous injection of the cut surface into the plane. The proved
cycle-to-Jordan theorem applies to these precise curves. Disk topology and
nonoverlap are not assumptions.
-/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialFolding

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  (F : SpatialFolding C) (retain : Set C.Seam)

include F

theorem boundaryGraph_edge_injective (bank : C.BoundaryBank retain) :
    Function.Injective ((C.boundaryGraph retain).edge bank) := by
  intro s t equal
  have cell := (F.faceMap_isometry retain bank.val.face).injective equal
  have edge := ((C.triangle bank.val.face).edgeMap_isometry bank.val.edge).injective cell
  exact C.bankParameter_injective retain bank edge

theorem exists_boundaryJordanThroughBank (f : C(C.Realization retain, Plane))
    (injective : Function.Injective f) (bank : C.BoundaryBank retain) :
    ∃ (u v : C.BoundaryVertex retain) (detour : List (C.BoundaryBank retain)),
      (C.boundaryGraph retain).graph.IsCycleThrough bank u v detour ∧
        Schoenflies.IsJordanCurve (Graph.edgesCover
          ((C.boundaryGraph retain).mapEmbedding f injective).drawing (bank :: detour)) := by
  obtain ⟨u, v, detour, cycle⟩ := C.boundaryGraph_bank_liesOnCycle retain bank
  refine ⟨u, v, detour, cycle, ?_⟩
  exact ((C.boundaryGraph retain).mapEmbedding f injective).cycle_isJordanCurve
    (fun edge => injective.comp (F.boundaryGraph_edge_injective retain edge)) cycle

end Unfoldings.SpatialFolding
