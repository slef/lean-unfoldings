module

public import Unfoldings.Complex.CollapsedCutGraph
public import Unfoldings.Complex.DiskBoundaryQuotient

/-! The collapsed cut graph has exactly the collapsed bank image as its carrier. -/

@[expose] public section

noncomputable section

namespace Unfoldings.TriangleComplex

universe u v

variable {Face : Type u} [Fintype Face] (C : TriangleComplex.{u, v} Face)
  {small large : Set C.Seam} (inclusion : small ⊆ large)

theorem relativeCutBank_mem_seamRange (s : C.RelativeCutSeam small large) (side : Bool)
    (y : (C.triangle (C.seamSide s.val side).face).Edge (C.seamSide s.val side).edge) :
    C.forgetCuts inclusion (C.bankMap small (C.relativeCutBank small large s side) y) ∈
      Set.range (C.relativeSeamMap inclusion s) := by
  cases side
  · obtain ⟨t, rfl⟩ := C.bankParameter_surjective small (C.relativeCutBank small large s false) y
    exact ⟨t, rfl⟩
  · obtain ⟨t, equal⟩ := C.bankParameter_surjective small
      (C.relativeCutBank small large s false) ((C.identify s.val).symm y)
    refine ⟨t, ?_⟩
    change C.faceMap large (C.left s.val).face
        ((C.triangle (C.left s.val).face).edgeMap (C.left s.val).edge _) = _
    rw [equal, C.seam_identified large s.val s.property.1]
    change C.faceMap large (C.right s.val).face
      ((C.triangle (C.right s.val).face).edgeMap (C.right s.val).edge
        ((C.identify s.val) ((C.identify s.val).symm y))) =
      C.faceMap large (C.right s.val).face
        ((C.triangle (C.right s.val).face).edgeMap (C.right s.val).edge y)
    exact congrArg (fun z => C.faceMap large (C.right s.val).face
      ((C.triangle (C.right s.val).face).edgeMap (C.right s.val).edge z))
      ((C.identify s.val).apply_symm_apply y)

theorem relativeCutVertex_mem_bankImage (s : C.RelativeCutSeam small large) (b : Bool) :
    C.vertexPoint large (C.relativeCutVertex small large s b) ∈
      C.forgetCuts inclusion '' C.bankBoundary small := by
  let bank := C.relativeCutBank small large s false
  let p := if b then (C.boundaryGraph small).edge bank 1 else (C.boundaryGraph small).edge bank 0
  have boundary : p ∈ C.bankBoundary small := by
    cases b <;> exact C.bankMap_mem_bankBoundary small bank _
  refine ⟨p, boundary, ?_⟩
  cases b
  · exact C.relativeSeamMap_zero inclusion s
  · exact C.relativeSeamMap_one inclusion s

end Unfoldings.TriangleComplex

namespace Unfoldings.SpatialFolding

universe u v w

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (F : SpatialFolding C)
  {small large : Set C.Seam} (inclusion : small ⊆ large) {X : Type w} [TopologicalSpace X]
  (q : C(C.Realization large, X))
  (fibers : ∀ x y, q x = q y ↔ x = y ∨ (x ∈ C.bankBoundary large ∧ y ∈ C.bankBoundary large))

theorem collapsedCutGraph_carrier :
    (F.collapsedCutGraph inclusion q fibers).carrier =
      q '' (C.forgetCuts inclusion '' C.bankBoundary small) := by
  let G := F.collapsedCutGraph inclusion q fibers
  ext x
  constructor
  · intro inside
    obtain ⟨cell, member⟩ := Set.mem_iUnion.mp inside
    cases cell with
    | inl vertex =>
      have same : x = vertex.val := member
      rw [same]
      obtain ⟨v, active, equal⟩ := vertex.property
      rw [← equal]
      have boundary_image : C.vertexPoint large v ∈
          C.forgetCuts inclusion '' C.bankBoundary small := by
        rcases active with old | ⟨s, b, rfl⟩
        · obtain ⟨p, equal⟩ := C.forgetCuts_surjective inclusion (C.vertexPoint large v)
          refine ⟨p, C.bankBoundary_preimage_forgetCuts inclusion ?_, equal⟩
          change C.forgetCuts inclusion p ∈ C.bankBoundary large
          rw [equal]
          exact (C.vertexPoint_mem_bankBoundary_iff large v).mpr old
        · exact C.relativeCutVertex_mem_bankImage inclusion s b
      exact Set.mem_image_of_mem q boundary_image
    | inr s =>
      obtain ⟨t, rfl⟩ := member
      exact ⟨C.relativeSeamMap inclusion s t,
        ⟨(C.boundaryGraph small).edge (C.relativeCutBank small large s false) t,
          C.bankMap_mem_bankBoundary small _ _, rfl⟩, rfl⟩
  · rintro ⟨y, ⟨p, boundary, rfl⟩, rfl⟩
    obtain ⟨bank, z, rfl⟩ := Set.mem_iUnion.mp boundary
    rcases C.relativeBank_cases small large bank with old | ⟨s, side, rfl⟩
    · let oldBank : C.BoundaryBank large := ⟨bank.val, old⟩
      let v := ((C.boundaryGraph large).left oldBank).val
      have active : v ∈ (C.relativeCutGraph small large).vertexSet :=
        Or.inl ((C.boundaryGraph large).left oldBank).property
      let vertex : C.collapsedCutVertices small large q :=
        ⟨q (C.vertexPoint large v), v, active, rfl⟩
      have equal : q (C.forgetCuts inclusion (C.bankMap small bank z)) = vertex.val := by
        apply (fibers _ _).mpr
        exact Or.inr ⟨C.bankMap_mem_bankBoundary large oldBank z,
          C.vertexPoint_mem_bankBoundary large ((C.boundaryGraph large).left oldBank)⟩
      rw [equal]
      exact G.mem_carrier_vertex vertex
    · obtain ⟨t, equal⟩ := C.relativeCutBank_mem_seamRange inclusion s side z
      exact (congrArg q equal) ▸ G.mem_carrier_edge s t

theorem collapsedCutGraph_map_vertex :
    (F.collapsedCutGraph inclusion q fibers).graph.map Subtype.val =
      (C.relativeCutGraph small large).map (fun v => q (C.vertexPoint large v)) := by
  let G := F.collapsedCutGraph inclusion q fibers
  apply Graph.ext
  · change Subtype.val '' Set.univ = C.collapsedCutVertices small large q
    rw [Set.image_univ, Subtype.range_coe]
  · intro s a b
    constructor
    · rintro ⟨u, v, link, first, last⟩
      rcases link with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ⟨C.relativeCutVertex small large s false, C.relativeCutVertex small large s true,
          Or.inl ⟨rfl, rfl⟩, first, last⟩
      · exact ⟨C.relativeCutVertex small large s true, C.relativeCutVertex small large s false,
          Or.inr ⟨rfl, rfl⟩, first, last⟩
    · rintro ⟨u, v, link, first, last⟩
      rcases link with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ⟨G.left s, G.right s, Or.inl ⟨rfl, rfl⟩, first, last⟩
      · exact ⟨G.right s, G.left s, Or.inr ⟨rfl, rfl⟩, first, last⟩

end Unfoldings.SpatialFolding
