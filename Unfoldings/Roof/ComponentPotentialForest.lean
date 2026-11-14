module

public import Unfoldings.Roof.CommonPotentialForest
public import Unfoldings.Roof.SelectionIntrinsicDisk

/-! Restrict the compatible original-edge forest to each selected component and its boundary. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexRoof C)

open Classical in
theorem interior_component_of_interior_selectedCarrier {slopes : Set Plane} {x : Plane}
    (inside : x ∈ interior (K.selectedCarrier slopes)) (seed : Face)
    (member : x ∈ K.restrictedCarrier (K.selectionComponent slopes seed)) :
    x ∈ interior (K.restrictedCarrier (K.selectionComponent slopes seed)) := by
  obtain ⟨g, hg⟩ := Set.mem_iUnion.mp member
  obtain ⟨r, positive, nearby⟩ := Metric.isOpen_iff.mp isOpen_interior x inside
  have center : x ∈ Metric.ball x r := Metric.mem_ball_self positive
  have contained := K.region_subset_selectionComponent (convex_ball x r).isPreconnected nearby
    g.val ⟨x, center, hg⟩
  have same : K.selectionComponent slopes g.val = K.selectionComponent slopes seed := by
    unfold selectionComponent
    rw [show (K.selectionGraph slopes).connectedComponentMk g.val =
      (K.selectionGraph slopes).connectedComponentMk seed from g.property]
  rw [same] at contained
  exact Metric.isOpen_ball.subset_interior_iff.mpr contained center

theorem seam_link_endpoints {v w : C.Vertex Set.univ} {s : C.Seam}
    (link : C.seamGraph.IsLink s v w) :
    ∃ f, K.projectedVertex v ∈ (K.projectedTriangle f).carrier ∧
      K.projectedVertex w ∈ (K.projectedTriangle f).carrier := by
  let f := (C.left s).face
  have endpoint (b : Bool) :
      K.projectedVertex (C.seamVertex s b) ∈ (K.projectedTriangle f).carrier := by
    cases b
    · exact (K.projectedTriangle f).vertex_mem (C.left s).edge
    · exact (K.projectedTriangle f).vertex_mem (Triangle.next (C.left s).edge)
  rcases link with ⟨first, last⟩ | ⟨first, last⟩
  · exact ⟨f, first.symm ▸ endpoint false, last.symm ▸ endpoint true⟩
  · exact ⟨f, first.symm ▸ endpoint true, last.symm ▸ endpoint false⟩

namespace CommonPotentialRouting

variable {K} {slopes : Set Plane} {E : SlopeEnvelope} {a β : ℝ}
  (I : K.CommonPotentialRouting {f | K.normalSlope f ∈ slopes} E a β)

open Classical in
theorem parent_stays_component (seed : Face) {v : C.Vertex Set.univ}
    (member : K.projectedVertex v ∈ K.restrictedCarrier (K.selectionComponent slopes seed)) :
    K.projectedVertex (I.parents.parent v) ∈
      K.restrictedCarrier (K.selectionComponent slopes seed) := by
  by_cases root : v ∈ I.parents.roots
  · rwa [I.parents.fixed_root v root]
  · have inside : K.projectedVertex v ∈ interior (K.selectedCarrier slopes) := by
      by_contra outside
      exact root ((Set.ext_iff.mp I.roots_eq v).mpr outside)
    obtain ⟨f, first, last⟩ := K.seam_link_endpoints (I.selection.link ⟨v, root⟩)
    obtain ⟨g, hg⟩ := Set.mem_iUnion.mp member
    have labels := K.selection_label_eq_at_interior inside first hg
    have selected : f ∈ K.selectionComponent slopes seed := labels.trans g.property
    exact Set.mem_iUnion.mpr ⟨⟨f, selected⟩, last⟩

open Classical in
def componentParents (seed : Face) :
    AscendingParents {v : C.Vertex Set.univ //
      K.projectedVertex v ∈ K.restrictedCarrier (K.selectionComponent slopes seed)} where
  roots := {v | v.val ∈ I.parents.roots}
  parent v := ⟨I.parents.parent v.val, I.parent_stays_component seed v.property⟩
  height v := I.parents.height v.val
  fixed_root v root := Subtype.ext (I.parents.fixed_root v.val root)
  ascending v nonroot := I.parents.ascending v.val nonroot

open Classical in
/-- Each restriction is itself a forest rooted exactly once on that component's own frontier,
even when distinct selected components touch at an original vertex. -/
theorem component_rootedForest (seed : Face) (selected : K.normalSlope seed ∈ slopes) :
    (I.componentParents seed).graph.IsRootedForest
      {v | K.projectedVertex v.val ∈ frontier
        (K.restrictedCarrier (K.selectionComponent slopes seed))} := by
  have roots : (I.componentParents seed).roots =
      {v | K.projectedVertex v.val ∈ frontier
        (K.restrictedCarrier (K.selectionComponent slopes seed))} := by
    ext v
    change v.val ∈ I.parents.roots ↔ K.projectedVertex v.val ∈ frontier _
    constructor
    · intro root
      refine ⟨subset_closure v.property, ?_⟩
      intro inside
      have in_union := interior_mono (K.selectionComponent_carrier_subset selected) inside
      exact ((Set.ext_iff.mp I.roots_eq v.val).mp root) in_union
    · intro boundary
      by_contra nonroot
      have inside : K.projectedVertex v.val ∈ interior (K.selectedCarrier slopes) := by
        by_contra outside
        exact nonroot ((Set.ext_iff.mp I.roots_eq v.val).mpr outside)
      exact boundary.2 (K.interior_component_of_interior_selectedCarrier inside seed v.property)
  rw [← roots]
  exact (I.componentParents seed).graph_rootedForest

open Classical in
/-- The restricted parent edges keep their actual original seam names. -/
theorem component_parent_original_edge (seed : Face)
    (v : {v : C.Vertex Set.univ //
      K.projectedVertex v ∈ K.restrictedCarrier (K.selectionComponent slopes seed)})
    (nonroot : v ∉ (I.componentParents seed).roots) :
    ∃ s : C.Seam, C.seamGraph.IsLink s v.val ((I.componentParents seed).parent v).val :=
  ⟨I.selection.edge ⟨v.val, nonroot⟩, I.selection.link ⟨v.val, nonroot⟩⟩

end CommonPotentialRouting
end Unfoldings.ConvexRoof
