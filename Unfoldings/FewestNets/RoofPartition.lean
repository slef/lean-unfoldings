module

public import Unfoldings.Development.NetPartition
public import Unfoldings.Roof.SelectionComponents
public import Unfoldings.Roof.ProjectedSeamCompletion
public import Unfoldings.Roof.ProjectedOpening

/-! Identifying normal components with the pieces of a partition on original face labels. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof

universe u v w

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexRoof C)

/-- For original roof faces, geometric whole-edge adjacency records precisely their paired seams. -/
theorem projected_edgeAdjacent_iff_original_seam (f g : Face) :
    TriangleFamily.EdgeAdjacent K.projectedTriangle f g ↔
      f ≠ g ∧ ∃ s : C.Seam,
        ((C.left s).face = f ∧ (C.right s).face = g) ∨
          ((C.left s).face = g ∧ (C.right s).face = f) := by
  constructor
  · rintro ⟨different, e, d, same⟩
    obtain ⟨s, positions⟩ := K.exists_seam_of_projected_shared_edge
      (a := ⟨f, e⟩) (b := ⟨g, d⟩) different same
    exact ⟨different, s, positions.imp
      (fun h => ⟨congrArg EdgeRef.face h.1, congrArg EdgeRef.face h.2⟩)
      (fun h => ⟨congrArg EdgeRef.face h.1, congrArg EdgeRef.face h.2⟩)⟩
  · rintro ⟨different, s, ⟨l, r⟩ | ⟨l, r⟩⟩
    · exact ⟨different, (C.left s).edge, (C.right s).edge, by
        simpa only [l, r] using K.projected_seam_edges_eq s⟩
    · exact ⟨different, (C.right s).edge, (C.left s).edge, by
        simpa only [l, r] using (K.projected_seam_edges_eq s).symm⟩

variable {Label : Type w} (slopeCell : Label → Set Plane) (label : Face → Label)
  (assigned : ∀ f i, K.normalSlope f ∈ slopeCell i ↔ label f = i)

include assigned in
/-- Exact ownership of each input normal identifies the selected component with
its component in the labeled original seam graph. -/
theorem selectionComponent_eq_labeledSeamGraph_support (seed : Face) :
    K.selectionComponent (slopeCell (label seed)) seed =
      ((C.labeledSeamGraph label).connectedComponentMk seed).supp := by
  let G := K.selectionGraph (slopeCell (label seed))
  let H := C.labeledSeamGraph label
  have selected_adj {a b : Face} (h : G.Adj a b) : H.Adj a b := by
    obtain ⟨ha, hb, adjacent⟩ := h
    have label_a := (assigned a (label seed)).mp ha
    have label_b := (assigned b (label seed)).mp hb
    have h := (K.projected_edgeAdjacent_iff_original_seam a b).mp adjacent
    exact ⟨h.1, label_a.trans label_b.symm, h.2⟩
  have original_adj {a b : Face} (ha : label a = label seed) (h : H.Adj a b) :
      G.Adj a b := by
    refine ⟨(assigned a _).mpr ha, (assigned b _).mpr (h.2.1.symm.trans ha), ?_⟩
    exact (K.projected_edgeAdjacent_iff_original_seam a b).mpr ⟨h.1, h.2.2⟩
  ext f
  change G.connectedComponentMk f = G.connectedComponentMk seed ↔
    H.connectedComponentMk f = H.connectedComponentMk seed
  rw [SimpleGraph.ConnectedComponent.eq, SimpleGraph.ConnectedComponent.eq]
  constructor
  · intro reach
    exact (H.reachable_iff_reflTransGen f seed).mpr <|
      Relation.ReflTransGen.mono (fun _ _ h => selected_adj h)
        f seed ((G.reachable_iff_reflTransGen f seed).mp reach)
  · intro reach
    have chain := (H.reachable_iff_reflTransGen seed f).mp reach.symm
    clear reach
    have chosen : Relation.ReflTransGen G.Adj seed f ∧ label f = label seed := by
      induction chain with
      | refl => exact ⟨Relation.ReflTransGen.refl, rfl⟩
      | tail _ edge ih => exact ⟨ih.1.tail (original_adj ih.2 edge), edge.2.1.symm.trans ih.2⟩
    exact ((G.reachable_iff_reflTransGen seed f).mpr chosen.1).symm

include assigned in
/-- One original-edge net per selected component yields a partition of the
entire roof with exactly as many pieces as there are labeled seam components. -/
theorem hasNetPartition_of_slope_cells
    (nets : ∀ seed, C.HasOriginalEdgeNet (K.selectionComponent (slopeCell (label seed)) seed)) :
    C.HasNetPartition (Nat.card (C.labeledSeamGraph label).ConnectedComponent) := by
  apply C.hasNetPartition_card_labeledSeamGraph label
  intro c
  obtain ⟨f, rfl⟩ := c.exists_rep
  change C.HasOriginalEdgeNet ((C.labeledSeamGraph label).connectedComponentMk f).supp
  rw [← K.selectionComponent_eq_labeledSeamGraph_support slopeCell label assigned f]
  exact nets f

end Unfoldings.ConvexRoof
