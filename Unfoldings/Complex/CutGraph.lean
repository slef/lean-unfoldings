module

public import Unfoldings.Complex.BoundaryQuotient
public import Unfoldings.Complex.Folding
public import Unfoldings.Geometry.SegmentGraph

/-! The spatial image of all cut banks is an exact finite embedded straight graph. -/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialFolding

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (F : SpatialFolding C)

def bankSegments (retain : Set C.Seam) : Set (Space × Space) :=
  Set.range (fun bank : C.BoundaryBank retain =>
    (F.place bank.val.face ((C.triangle bank.val.face).vertex bank.val.edge),
      F.place bank.val.face ((C.triangle bank.val.face).vertex (Triangle.next bank.val.edge))))

theorem finite_bankSegments (retain : Set C.Seam) : (F.bankSegments retain).Finite := by
  let := C.finite_boundaryBank retain
  exact Set.finite_range _

theorem bankMap_spatial_image (retain : Set C.Seam) (bank : C.BoundaryBank retain) :
    F.toSpace retain '' Set.range (C.bankMap retain bank) =
      segment ℝ (F.place bank.val.face ((C.triangle bank.val.face).vertex bank.val.edge))
        (F.place bank.val.face
          ((C.triangle bank.val.face).vertex (Triangle.next bank.val.edge))) := by
  have image : F.toSpace retain '' Set.range (C.bankMap retain bank) =
      F.place bank.val.face '' (C.triangle bank.val.face).edge bank.val.edge := by
    ext z
    constructor
    · rintro ⟨_, ⟨x, rfl⟩, equal⟩
      exact ⟨x.val, x.property, equal⟩
    · rintro ⟨x, member, equal⟩
      exact ⟨C.bankMap retain bank ⟨x, member⟩, ⟨⟨x, member⟩, rfl⟩, equal⟩
  rw [image, Triangle.edge]
  exact image_segment ℝ (F.place bank.val.face).toAffineMap _ _

theorem segmentCarrier_bankSegments (retain : Set C.Seam) :
    segmentCarrier (F.bankSegments retain) = F.toSpace retain '' C.bankBoundary retain := by
  ext z
  constructor
  · intro member
    obtain ⟨_, ⟨bank, rfl⟩, on_segment⟩ := Set.mem_iUnion₂.mp member
    rw [← F.bankMap_spatial_image retain bank] at on_segment
    obtain ⟨x, hx, image⟩ := on_segment
    exact ⟨x, Set.mem_iUnion.mpr ⟨bank, hx⟩, image⟩
  · rintro ⟨x, member, image⟩
    obtain ⟨bank, hx⟩ := Set.mem_iUnion.mp member
    apply Set.mem_iUnion₂.mpr
    refine ⟨_, ⟨bank, rfl⟩, ?_⟩
    rw [← F.bankMap_spatial_image retain bank]
    exact ⟨x, hx, image⟩

theorem exists_bank_boundary_graph (retain : Set C.Seam) :
    ∃ (Vertex Edge : Type) (G : FiniteEmbeddedGraph Vertex Edge Space),
      G.IsStraight ∧ G.graph.Simple ∧
        G.carrier = F.toSpace retain '' C.bankBoundary retain ∧
        ∀ e : Edge, ∃ bank : C.BoundaryBank retain,
          Set.range (G.edge e) ⊆ F.toSpace retain '' Set.range (C.bankMap retain bank) := by
  obtain ⟨Vertex, Edge, G, straight, carrier, parents⟩ :=
    exists_finite_embedded_straight_segment_graph (F.bankSegments retain)
      (F.finite_bankSegments retain)
  refine ⟨Vertex, Edge, G, straight, straight.graph_simple,
    carrier.trans (F.segmentCarrier_bankSegments retain), ?_⟩
  intro e
  obtain ⟨_, ⟨bank, rfl⟩, included⟩ := parents e
  exact ⟨bank, (F.bankMap_spatial_image retain bank).symm ▸ included⟩

end Unfoldings.SpatialFolding
