module

public import Unfoldings.Complex.HalfPlaneBoundary
public import Unfoldings.Cone.BoundaryTopology
public import Unfoldings.Geometry.EdgeCoordinates

/-!
# Actual cut banks admit an intrinsic half-plane boundary atlas

Both nonvertex bank points and boundary vertex copies have constructed local
charts. Intrinsic boundary identification proves that every chart carries
exactly the actual bank set to the boundary line. Finite local inward pushes
therefore embed the whole compact cut surface into its bank complement.
-/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialFolding

open PlanarTopology

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  (F : SpatialFolding C) (retain : Set C.Seam)

include F

theorem exists_boundaryVertexChart (v : C.Vertex retain) (boundary : C.IsBoundaryVertex retain v) :
    Nonempty (HalfPlaneBoundaryChart (C.bankBoundary retain) (C.vertexPoint retain v)) := by
  obtain ⟨r, positive, V, open_V, e, center⟩ :=
    F.exists_boundaryVertexHalfPlaneChart retain v boundary
  refine ⟨⟨Metric.eball (C.vertexPoint retain v) (ENNReal.ofReal r), Metric.isOpen_eball,
    Metric.mem_eball_self (ENNReal.ofReal_pos.mpr positive), V, open_V, e, center, ?_⟩⟩
  intro p
  exact F.bankBoundary_iff_halfPlane_snd_eq_zero retain Metric.isOpen_eball open_V e p

theorem exists_nonvertexBankChart (bank : C.BoundaryBank retain)
    (x : (C.triangle bank.val.face).Edge bank.val.edge)
    (nonvertex : ¬ (C.triangle bank.val.face).IsVertex x) :
    Nonempty (HalfPlaneBoundaryChart (C.bankBoundary retain) (C.bankMap retain bank x)) := by
  obtain ⟨N⟩ := C.exists_boundaryChart retain bank x nonvertex
  let T := C.triangle bank.val.face
  let U := Metric.eball (C.bankMap retain bank x) (ENNReal.ofReal N.radius)
  let V : Set closedHalfPlane := Subtype.val ⁻¹' (T.edgeCoordinates bank.val.edge x ''
    Metric.ball x.val N.radius)
  have open_V : IsOpen V := T.edgeHalfBallHomeomorph_open_target bank.val.edge x N.radius
  let e : U ≃ₜ V := N.chart.symm.toHomeomorph.trans
    (T.edgeHalfBallHomeomorph bank.val.edge x N.radius)
  refine ⟨⟨U, Metric.isOpen_eball, Metric.mem_eball_self (ENNReal.ofReal_pos.mpr N.positive),
    V, open_V, e, ?_, ?_⟩⟩
  · apply Subtype.ext
    change T.edgeCoordinates bank.val.edge x
      (N.chart.symm ⟨C.bankMap retain bank x,
        Metric.mem_eball_self (ENNReal.ofReal_pos.mpr N.positive)⟩).val = (0, 0)
    rw [TriangleComplex.BoundaryChart.center_coordinates C N, T.edgeCoordinates_center]
  · intro p
    exact F.bankBoundary_iff_halfPlane_snd_eq_zero retain Metric.isOpen_eball open_V e p

theorem exists_bankBoundaryChart (p : C.Realization retain) (boundary : p ∈ C.bankBoundary retain) :
    Nonempty (HalfPlaneBoundaryChart (C.bankBoundary retain) p) := by
  obtain ⟨bank, x, rfl⟩ := Set.mem_iUnion.mp boundary
  by_cases vertex : (C.triangle bank.val.face).IsVertex x
  · rcases ((C.triangle bank.val.face).edge_vertex_iff bank.val.edge x).mp vertex with left | right
    · have point : C.bankMap retain bank x =
          C.vertexPoint retain (C.vertexOfCorner retain (bank.val.face, bank.val.edge)) := by
        rw [C.vertexPoint_vertexOfCorner]
        exact congrArg (C.faceMap retain bank.val.face) (Subtype.ext left)
      rw [point]
      exact F.exists_boundaryVertexChart retain _ (C.bank_start_isBoundaryVertex retain bank)
    · have point : C.bankMap retain bank x = C.vertexPoint retain
          (C.vertexOfCorner retain (bank.val.face, Triangle.next bank.val.edge)) := by
        rw [C.vertexPoint_vertexOfCorner]
        exact congrArg (C.faceMap retain bank.val.face) (Subtype.ext right)
      rw [point]
      exact F.exists_boundaryVertexChart retain _ (C.bank_finish_isBoundaryVertex retain bank)
  · exact F.exists_nonvertexBankChart retain bank x vertex

/-- Construct an inward embedding, without assuming disk topology or nonoverlap. -/
theorem exists_inwardEmbedding :
    ∃ f : C(C.Realization retain, C.Realization retain), Topology.IsClosedEmbedding f ∧
      Set.range f ⊆ (C.bankBoundary retain)ᶜ := by
  exact exists_inward_embedding_of_halfPlaneCharts (C.bankBoundary retain)
    (C.isCompact_bankBoundary retain) (F.exists_bankBoundaryChart retain)

/-- Every cut surface embeds back into the original surface away from the cut graph. -/
theorem exists_cutEmbedding {small large : Set C.Seam} (inclusion : small ⊆ large) :
    ∃ f : C(C.Realization small, C.Realization large), Topology.IsClosedEmbedding f ∧
      Set.range f ⊆ (C.forgetCuts inclusion '' C.bankBoundary small)ᶜ := by
  exact (C.forgetCutsBoundaryQuotient inclusion).exists_embedding_avoiding_boundaryImage
    (C.isCompact_bankBoundary small) (F.exists_bankBoundaryChart small)

end Unfoldings.SpatialFolding
