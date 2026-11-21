module

public import Unfoldings.Polyhedron.SelectedFaceBoundary
public import Unfoldings.Polyhedron.TriangulationDuality
public import Unfoldings.Combinatorics.ActiveGraphComponents

/-! Disk-shaped label components give a connected cut graph on its active vertices. -/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialFolding.ConvexBoundary

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {F : SpatialFolding C} (P : F.ConvexBoundary)

/-- Retaining exactly the seams between equally labeled triangles. -/
def retainLabelSeams {L : Type*} (label : Face → L) : Set C.Seam :=
  {s | label (C.left s).face = label (C.right s).face}

/-- The original vertices lying at some endpoint of a differently labeled seam. -/
def labelCutVertex {L : Type*} (label : Face → L) (v : C.Vertex Set.univ) : Prop :=
  ∃ (s : C.Seam) (b : Bool), s ∉ retainLabelSeams (C := C) label ∧ v = C.seamVertex s b

open Classical in
include P in
/-- When all same-label components are disks, the union of their original
boundary images is the connected carrier of the original cut edges. -/
theorem isConnected_labeledCutCarrier {L : Type*} (label : Face → L)
    (disks : ∀ c : (C.labeledSeamGraph label).ConnectedComponent, C.RestrictionIsDisk c.supp) :
    IsConnected (C.forgetCuts (Set.subset_univ (retainLabelSeams (C := C) label)) ''
      C.bankBoundary (retainLabelSeams (C := C) label)) := by
  let G := C.labeledSeamGraph label
  let comp (f : Face) := (G.connectedComponentMk f).supp
  let B (f : Face) := C.selectedFaceBoundary (comp f)
  let keep := retainLabelSeams (C := C) label
  let inclusion : keep ⊆ (Set.univ : Set C.Seam) := Set.subset_univ _
  let : Nonempty Face := by
    let := P.connectedSpace
    obtain ⟨x⟩ := (inferInstance : Nonempty (C.Realization Set.univ))
    obtain ⟨a, _⟩ := MetricGluing.point_surjective C.Cell (C.glue Set.univ) x
    exact ⟨a.1⟩
  have boundary_connected (f : Face) : IsConnected (B f) :=
    F.isConnected_selectedFaceBoundary _ (Classical.choice (disks (G.connectedComponentMk f)))
  have own (f : Face) : f ∈ comp f := rfl
  have labels {f g : Face} (member : g ∈ comp f) : label g = label f :=
    C.label_eq_of_labeledSeamGraph_reachable label (SimpleGraph.ConnectedComponent.exact member)
  have same_component (s : C.Seam) (same : s ∈ keep) :
      G.connectedComponentMk (C.left s).face = G.connectedComponentMk (C.right s).face := by
    by_cases loop : (C.left s).face = (C.right s).face
    · rw [loop]
    · exact SimpleGraph.ConnectedComponent.sound
        ((show G.Adj (C.left s).face (C.right s).face from
          ⟨loop, same, s, Or.inl ⟨rfl, rfl⟩⟩).reachable)
  have boundary_meet (s : C.Seam) : (B (C.left s).face ∩ B (C.right s).face).Nonempty := by
    by_cases same : s ∈ keep
    · have eq : B (C.left s).face = B (C.right s).face := by
        change C.selectedFaceBoundary (G.connectedComponentMk (C.left s).face).supp =
          C.selectedFaceBoundary (G.connectedComponentMk (C.right s).face).supp
        rw [same_component s same]
      rw [← eq, Set.inter_self]
      exact (boundary_connected _).nonempty
    · have excluded_r : (C.right s).face ∉ comp (C.left s).face := fun h => same (labels h).symm
      have excluded_l : (C.left s).face ∉ comp (C.right s).face := fun h => same (labels h)
      let e := C.left s
      let y : (C.triangle e.face).Edge e.edge := (C.triangle e.face).endpoint e.edge false
      have paired := C.seam_identified Set.univ s (Set.mem_univ s) y
      refine ⟨_, C.seamSide_mem_selectedFaceBoundary _ s false (own _) excluded_r y, ?_⟩
      change C.faceMap Set.univ (C.left s).face
        ((C.triangle (C.left s).face).edgeMap (C.left s).edge y) ∈ B (C.right s).face
      rw [paired]
      exact C.seamSide_mem_selectedFaceBoundary _ s true (own _) excluded_l (C.identify s y)
  have union_connected : IsConnected (⋃ f, B f) := by
    apply IsConnected.iUnion_of_reflTransGen boundary_connected
    intro f g
    let D := endpointGraph (fun s => (C.left s).face) (fun s => (C.right s).face)
    have chain := (D.reachable_iff_reflTransGen f g).mp (P.original_faces_reachable f g)
    have meets (a b : Face) (edge : D.Adj a b) : (B a ∩ B b).Nonempty := by
      change (SimpleGraph.fromRel _).Adj a b at edge
      rcases ((SimpleGraph.fromRel_adj _ _ _).mp edge).2 with ⟨s, rfl, rfl⟩ | ⟨s, rfl, rfl⟩
      · exact boundary_meet s
      · rw [Set.inter_comm]
        exact boundary_meet s
    induction chain with
    | refl => exact .refl
    | tail _ edge ih => exact .tail ih (meets _ _ edge)
  have union_eq : (⋃ f, B f) = C.forgetCuts inclusion '' C.bankBoundary keep := by
    ext p
    constructor
    · intro hp
      obtain ⟨f, z, hz, rfl⟩ := Set.mem_iUnion.mp hp
      obtain ⟨bank, y, rfl⟩ := Set.mem_iUnion.mp hz
      obtain ⟨s, b, selected, excluded, rfl⟩ :=
        C.exists_original_seam_of_selected_boundary_bank (comp f) P bank
      have cut : s ∉ keep := by
        intro same
        apply excluded
        cases b
        · exact (same_component s same).symm.trans selected
        · exact (same_component s same).trans selected
      exact ⟨C.bankMap keep (C.cutBank keep ⟨s, cut⟩ b) y,
        C.bankMap_mem_bankBoundary keep _ _, rfl⟩
    · rintro ⟨z, hz, rfl⟩
      obtain ⟨bank, y, rfl⟩ := Set.mem_iUnion.mp hz
      rcases C.relativeBank_cases keep Set.univ bank with outside | ⟨s, b, rfl⟩
      · exact (P.not_isBoundaryEdge bank.val outside).elim
      · let f := (C.seamSide s.val b).face
        have excluded : (C.seamSide s.val (!b)).face ∉ comp f := by
          intro member
          apply s.property.2
          cases b
          · exact (labels member).symm
          · exact labels member
        exact Set.mem_iUnion.mpr ⟨f, C.seamSide_mem_selectedFaceBoundary _ s.val b
          (own f) excluded y⟩
  rwa [← union_eq]

set_option maxHeartbeats 800000 in
-- The maps compare the cut, original, and embedded graph vertex types.
open Classical in
include P in
/-- If the selected components are disks, the cut graph has a nonempty
connected component containing all vertices incident to cut seams. -/
theorem labelCutGraph_connected_on_cutVertices {L : Type*} (label : Face → L)
    (disks : ∀ c : (C.labeledSeamGraph label).ConnectedComponent, C.RestrictionIsDisk c.supp) :
    (∃ v, labelCutVertex (C := C) label v) ∧
      ∀ v w : C.Vertex Set.univ, labelCutVertex label v → labelCutVertex label w →
        (labelCutGraph (C := C) label).Reachable v w := by
  let keep := retainLabelSeams (C := C) label
  let inclusion : keep ⊆ (Set.univ : Set C.Seam) := Set.subset_univ _
  have no_root (v : C.Vertex Set.univ) : v ∉ C.relativeCutRoots Set.univ := by
    rintro ⟨e, boundary, _⟩
    exact P.not_isBoundaryEdge e boundary
  have no_bank (x : C.Realization Set.univ) : x ∉ C.bankBoundary Set.univ := by
    intro h
    obtain ⟨bank, _⟩ := Set.mem_iUnion.mp h
    exact P.not_isBoundaryEdge bank.val bank.property
  let q : C(C.Realization Set.univ, C.Realization Set.univ) := ContinuousMap.id _
  have fibers : ∀ x y, q x = q y ↔
      x = y ∨ (x ∈ C.bankBoundary Set.univ ∧ y ∈ C.bankBoundary Set.univ) := by
    intro x y
    exact ⟨Or.inl, fun h => h.elim id fun b => (no_bank _ b.1).elim⟩
  let G := F.collapsedCutGraph inclusion q fibers
  have connected : G.adjacencyGraph.Connected := by
    apply G.connected_of_isConnected
    rw [F.collapsedCutGraph_carrier inclusion q fibers]
    change IsConnected (id '' _)
    rw [Set.image_id]
    exact P.isConnected_labeledCutCarrier label disks
  let original (p : C.collapsedCutVertices keep Set.univ q) := p.property.choose
  have active (p : C.collapsedCutVertices keep Set.univ q) :
      labelCutVertex label (original p) := by
    have member := p.property.choose_spec.1
    rcases member with old | ⟨s, b, eq⟩
    · exact (no_root _ old).elim
    · exact ⟨s.val, b, s.property.2, eq⟩
  have point_eq (p : C.collapsedCutVertices keep Set.univ q) :
      C.vertexPoint Set.univ (original p) = p.val := p.property.choose_spec.2
  let point (v : C.Vertex Set.univ) (hv : labelCutVertex label v) :
      C.collapsedCutVertices keep Set.univ q :=
    ⟨C.vertexPoint Set.univ v, v, Or.inr (by
      obtain ⟨s, b, cut, eq⟩ := hv
      exact ⟨⟨s, Set.mem_univ _, cut⟩, b, eq⟩), rfl⟩
  have point_original (v : C.Vertex Set.univ) (hv : labelCutVertex label v) :
      original (point v hv) = v := C.vertexPoint_injective _ (point_eq _)
  have original_left (s : C.RelativeCutSeam keep Set.univ) :
      original (G.left s) = C.seamVertex s.val false :=
    C.vertexPoint_injective _ (point_eq _)
  have original_right (s : C.RelativeCutSeam keep Set.univ) :
      original (G.right s) = C.seamVertex s.val true :=
    C.vertexPoint_injective _ (point_eq _)
  let project : G.adjacencyGraph →g labelCutGraph label :=
    { toFun := original
      map_rel' := by
        intro u v edge
        obtain ⟨different, s, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ := edge
        · have neq : original (G.left s) ≠ original (G.right s) := by
            intro eq
            apply different
            apply Subtype.ext
            rw [← point_eq (G.left s), ← point_eq (G.right s), eq]
          exact (SimpleGraph.fromRel_adj _ _ _).mpr
            ⟨neq, Or.inl ⟨⟨s.val, s.property.2⟩, (original_left s).symm, (original_right s).symm⟩⟩
        · have neq : original (G.right s) ≠ original (G.left s) := by
            intro eq
            apply different
            apply Subtype.ext
            rw [← point_eq (G.right s), ← point_eq (G.left s), eq]
          exact (SimpleGraph.fromRel_adj _ _ _).mpr
            ⟨neq, Or.inr ⟨⟨s.val, s.property.2⟩, (original_left s).symm, (original_right s).symm⟩⟩ }
  constructor
  · obtain ⟨p⟩ := connected.nonempty
    exact ⟨original p, active p⟩
  · intro v w hv hw
    have h := (connected.preconnected (point v hv) (point w hw)).map project
    change (labelCutGraph label).Reachable (original (point v hv)) (original (point w hw)) at h
    rwa [point_original v hv, point_original w hw] at h

open Classical in
include P in
/-- Disk components give one active cut component and one component for
each vertex that is not on a cut. -/
theorem card_labelCutGraph_components_of_disks {L : Type*} (label : Face → L)
    (disks : ∀ c : (C.labeledSeamGraph label).ConnectedComponent, C.RestrictionIsDisk c.supp) :
    Nat.card (labelCutGraph (C := C) label).ConnectedComponent =
      1 + Nat.card {v : C.Vertex Set.univ // ¬ labelCutVertex label v} := by
  obtain ⟨nonempty, connected⟩ := P.labelCutGraph_connected_on_cutVertices label disks
  apply card_components_eq_one_add_card_inactive _ _ _ nonempty connected
  intro v w adj
  change (SimpleGraph.fromRel _).Adj v w at adj
  rcases ((SimpleGraph.fromRel_adj _ _ _).mp adj).2 with ⟨s, rfl, rfl⟩ | ⟨s, rfl, rfl⟩
  · exact ⟨s.val, false, s.property, rfl⟩
  · exact ⟨s.val, true, s.property, rfl⟩

end Unfoldings.SpatialFolding.ConvexBoundary
