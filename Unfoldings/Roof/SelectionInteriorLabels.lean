module

public import Unfoldings.Roof.SelectionComponents
public import Unfoldings.Topology.ClosedCoverValues

/-! Component labels agree throughout every connected region inside a selected roof. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexRoof C)

theorem projected_interior_disjoint_carrier {f g : Face} (different : f ≠ g) :
    Disjoint (interior (K.projectedTriangle f).carrier) (K.projectedTriangle g).carrier := by
  have separated := (K.projectedTriangles_nonoverlapping different).closure_right isOpen_interior
  have regular :=
    (K.projectedTriangle g).convex_carrier.closure_interior_eq_closure_of_nonempty_interior
    (K.projectedTriangle g).interior_nonempty
  rw [(K.projectedTriangle g).compact_carrier.isClosed.closure_eq] at regular
  rw [← regular]
  exact separated

/-- Every face containing an interior point of the selected union is itself selected. -/
theorem selected_of_mem_interior_selectedCarrier {slopes : Set Plane} {p : Plane}
    (inside : p ∈ interior (K.selectedCarrier slopes)) (f : Face)
    (member : p ∈ (K.projectedTriangle f).carrier) : K.normalSlope f ∈ slopes := by
  by_contra omitted
  have separated : Disjoint (interior (K.projectedTriangle f).carrier)
      (K.selectedCarrier slopes) := by
    apply Set.disjoint_left.mpr
    intro q in_face in_union
    obtain ⟨g, selected, in_g⟩ := K.mem_selectedCarrier.mp in_union
    have different : f ≠ g := fun same => omitted (same ▸ selected)
    exact Set.disjoint_left.mp (K.projected_interior_disjoint_carrier different) in_face in_g
  have closed_separation := (separated.mono_right interior_subset).closure_left isOpen_interior
  have regular :=
    (K.projectedTriangle f).convex_carrier.closure_interior_eq_closure_of_nonempty_interior
    (K.projectedTriangle f).interior_nonempty
  rw [(K.projectedTriangle f).compact_carrier.isClosed.closure_eq] at regular
  rw [regular] at closed_separation
  exact Set.disjoint_left.mp closed_separation member inside

theorem selectionGraph_adj_seam {slopes : Set Plane} (s : C.Seam)
    (first : K.normalSlope (C.left s).face ∈ slopes)
    (last : K.normalSlope (C.right s).face ∈ slopes) :
    (K.selectionGraph slopes).Adj (C.left s).face (C.right s).face :=
  ⟨first, last, K.folding.incident_faces_ne s, (C.left s).edge, (C.right s).edge,
    K.projected_seam_edges_eq s⟩

theorem projectFace_eq_of_related {a b : C.Total}
    (related : Relation.EqvGen (C.glue Set.univ) a b) :
    K.projectFace a.1 a.2.val = K.projectFace b.1 b.2.val := by
  have equal := (C.faceMap_eq_iff Set.univ a.1 b.1 a.2 b.2).mpr related
  exact congrArg (fun x => Cap.horizontal (K.folding.toSpace Set.univ x)) equal

/-- At a regular contact, any two selected face copies have the same component label. -/
theorem selection_label_eq_of_regular_contact {slopes : Set Plane} {a b : C.Total}
    (first : K.normalSlope a.1 ∈ slopes) (last : K.normalSlope b.1 ∈ slopes)
    (regular : ¬ C.IsVertex a)
    (same : K.projectFace a.1 a.2.val = K.projectFace b.1 b.2.val) :
    (K.selectionGraph slopes).connectedComponentMk a.1 =
      (K.selectionGraph slopes).connectedComponentMk b.1 := by
  have related := (C.faceMap_eq_iff Set.univ a.1 b.1 a.2 b.2).mp (K.projection_injective same)
  rcases (C.eqvGen_iff_of_regular Set.univ regular).mp related with equal | crossing
  · exact congrArg (fun x => (K.selectionGraph slopes).connectedComponentMk x.1) equal
  · obtain ⟨s, _, side, x, at_first, at_last⟩ := crossing
    have face_first := congrArg Sigma.fst at_first
    have face_last := congrArg Sigma.fst at_last
    rw [face_first] at first
    rw [face_last] at last
    rw [face_first, face_last]
    cases side
    · exact SimpleGraph.ConnectedComponent.sound (K.selectionGraph_adj_seam s first last).reachable
    · exact SimpleGraph.ConnectedComponent.sound
        (K.selectionGraph_adj_seam s last first).reachable.symm

/-- Vertex contacts in the interior of the selected union also preserve the component label. -/
theorem selection_label_eq_of_related_at_interior {slopes : Set Plane} {p : Plane}
    (inside : p ∈ interior (K.selectedCarrier slopes)) {a b : C.Total}
    (related : Relation.EqvGen (C.glue Set.univ) a b)
    (at_a : K.projectFace a.1 a.2.val = p) :
    (K.selectionGraph slopes).connectedComponentMk a.1 =
      (K.selectionGraph slopes).connectedComponentMk b.1 := by
  have selected (c : C.Total) (at_c : K.projectFace c.1 c.2.val = p) :
      K.normalSlope c.1 ∈ slopes := by
    apply K.selected_of_mem_interior_selectedCarrier inside c.1
    rw [projectedTriangle, Triangle.affineImage_carrier]
    exact ⟨c.2.val, c.2.property, at_c⟩
  induction related with
  | rel a b joined =>
    obtain ⟨s, _, x, rfl, rfl⟩ := joined
    have at_b := (K.projectedTriangle_joined s x).symm.trans at_a
    exact SimpleGraph.ConnectedComponent.sound
      (K.selectionGraph_adj_seam s
        (selected (C.edgePoint (C.left s) x) at_a)
        (selected (C.edgePoint (C.right s) (C.identify s x)) at_b)).reachable
  | refl a => rfl
  | symm a b related ih =>
    exact (ih ((K.projectFace_eq_of_related related).trans at_a)).symm
  | trans a b c first _ ih_first ih_last =>
    exact (ih_first at_a).trans (ih_last ((K.projectFace_eq_of_related first).symm.trans at_a))

/-- All face labels present at one selected interior point agree, including original vertices. -/
theorem selection_label_eq_at_interior {slopes : Set Plane} {p : Plane}
    (inside : p ∈ interior (K.selectedCarrier slopes)) {f g : Face}
    (first : p ∈ (K.projectedTriangle f).carrier)
    (last : p ∈ (K.projectedTriangle g).carrier) :
    (K.selectionGraph slopes).connectedComponentMk f =
      (K.selectionGraph slopes).connectedComponentMk g := by
  rw [projectedTriangle, Triangle.affineImage_carrier] at first last
  obtain ⟨x, hx, at_x⟩ := first
  obtain ⟨y, hy, at_y⟩ := last
  have equal : C.faceMap Set.univ f ⟨x, hx⟩ = C.faceMap Set.univ g ⟨y, hy⟩ :=
    K.projection_injective (at_x.trans at_y.symm)
  exact K.selection_label_eq_of_related_at_interior inside
    ((C.faceMap_eq_iff Set.univ f g ⟨x, hx⟩ ⟨y, hy⟩).mp equal) at_x

open Classical in
/-- A connected region inside the selection belongs to a single whole-edge component. -/
theorem region_subset_selectionComponent {slopes Ω : Set Plane}
    (connected : IsPreconnected Ω) (included : Ω ⊆ interior (K.selectedCarrier slopes))
    (seed : Face) (touches : (Ω ∩ (K.projectedTriangle seed).carrier).Nonempty) :
    Ω ⊆ K.restrictedCarrier (K.selectionComponent slopes seed) := by
  let := Subtype.preconnectedSpace connected
  let piece := fun f : Face => {p : Ω | p.val ∈ (K.projectedTriangle f).carrier}
  have closed (f : Face) : IsClosed (piece f) :=
    (K.projectedTriangle f).compact_carrier.isClosed.preimage continuous_subtype_val
  have cover : (⋃ f, piece f) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro p
    have member := K.selectedCarrier_subset_footprint slopes (interior_subset (included p.property))
    rw [K.footprint_eq_union_projectedTriangles] at member
    obtain ⟨f, in_face⟩ := Set.mem_iUnion.mp member
    exact Set.mem_iUnion.mpr ⟨f, in_face⟩
  have compatible (f g : Face) (meeting : (piece f ∩ piece g).Nonempty) :
      (K.selectionGraph slopes).connectedComponentMk f =
        (K.selectionGraph slopes).connectedComponentMk g := by
    obtain ⟨p, first, last⟩ := meeting
    exact K.selection_label_eq_at_interior (included p.property) first last
  intro p hp
  have member := K.selectedCarrier_subset_footprint slopes (interior_subset (included hp))
  rw [K.footprint_eq_union_projectedTriangles] at member
  obtain ⟨g, in_face⟩ := Set.mem_iUnion.mp member
  have first : (piece seed).Nonempty :=
    ⟨⟨touches.choose, touches.choose_spec.1⟩, touches.choose_spec.2⟩
  have last : (piece g).Nonempty := ⟨⟨p, hp⟩, in_face⟩
  have labels := eq_of_finite_closed_cover piece closed cover
    (K.selectionGraph slopes).connectedComponentMk compatible first last
  have in_component : g ∈ K.selectionComponent slopes seed := labels.symm
  exact Set.mem_iUnion.mpr ⟨⟨g, in_component⟩, in_face⟩

end Unfoldings.ConvexRoof
