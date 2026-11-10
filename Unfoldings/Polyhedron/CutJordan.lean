module

public import Unfoldings.Polyhedron.CutPlanar
public import Unfoldings.Polyhedron.Closedness
public import Unfoldings.Complex.BoundaryCycleCarrier

/-! A primal cut tree gives one Jordan curve for the entire actual cut boundary. -/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialFolding.ConvexBoundary

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {F : SpatialFolding C} (P : F.ConvexBoundary)

include P

theorem exists_Jordan_bankBoundary_of_cutTree (retain : Set C.Seam)
    (forest : (C.cutSeamGraph retain).IsAcyclic) (connected : (C.cutSeamGraph retain).Connected) :
    ∃ (f : C(C.Realization retain, Plane)), Topology.IsClosedEmbedding f ∧
      Schoenflies.IsJordanCurve (f '' C.bankBoundary retain) := by
  obtain ⟨n, cycle, closes, covers⟩ :=
    C.exists_boundaryCycle_cover retain P.not_isBoundaryEdge forest connected
  let bank := (C.boundaryEndEquiv retain cycle.first).1
  have cut : (C.bankBoundary retain).Nonempty :=
    ⟨C.bankMap retain bank (C.bankParameter retain bank 0),
      C.bankMap_mem_bankBoundary retain bank _⟩
  obtain ⟨f, embedded⟩ := P.exists_planarCutEmbedding retain cut
  have actual := ((C.boundaryGraph retain).mapEmbedding f embedded.injective).cycle_isJordanCurve
    (fun edge => embedded.injective.comp (F.boundaryGraph_edge_injective retain edge))
    (C.boundaryCycle_isCycleThrough retain cycle closes)
  rw [C.boundaryCycle_edgesCover_eq retain cycle covers f embedded.injective] at actual
  exact ⟨f, embedded, actual⟩

end Unfoldings.SpatialFolding.ConvexBoundary
