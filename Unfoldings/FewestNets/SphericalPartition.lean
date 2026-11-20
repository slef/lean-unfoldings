module

public import Unfoldings.Polyhedron.NormalSelection
public import Unfoldings.Development.NetPartitionRestriction

/-! Assemble normal components from different hemispheres on the same original surface. -/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialFolding.ConvexBoundary

universe u v w

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {F : SpatialFolding C} (P : F.ConvexBoundary) (N : F.SupportingNormals)
  {Label : Type w} (cell : Label → Set Space) (center : Label → Space)
  (unit : ∀ i, ‖center i‖ = 1)
  (hemisphere : ∀ i, ∀ n ∈ cell i, 0 < inner ℝ (center i) n)
  (label : Face → Label) (assigned : ∀ f i, N.normal f ∈ cell i ↔ label f = i)

include assigned in
/-- The component developed in a local hemisphere contains exactly the
original input faces reached along same-label original seams. -/
theorem normalSelectionFaces_image_eq_labeled_component (seed : Face) :
    Subtype.val '' P.normalSelectionFaces N (center (label seed)) (unit (label seed))
      (cell (label seed)) (hemisphere (label seed)) seed ((assigned seed _).mpr rfl) =
      ((C.labeledSeamGraph label).connectedComponentMk seed).supp := by
  let i := label seed
  let Q := P.hemisphereRoof N (center i)
  let region := Cap.northFrame (center i) '' cell i
  let upper (f : Face) (chosen : label f = i) :=
    P.normalSelectionSeed N (center i) (unit i) (cell i) (hemisphere i) f ((assigned f i).mpr chosen)
  let seedUp := upper seed rfl
  let G := Q.selectionGraph (Cap.gnomonicRegion region)
  let H := C.labeledSeamGraph label
  have to_original {a b} (edge : G.Adj a b) : H.Adj a.val b.val := by
    obtain ⟨ha, hb, diff, seam⟩ :=
      (P.hemisphere_selectionGraph_adj_iff N (center i) (cell i) a b).mp edge
    exact ⟨fun h => diff (Subtype.ext h), ((assigned _ i).mp ha).trans ((assigned _ i).mp hb).symm, seam⟩
  have from_original {a b} (chosen : label a.val = i) (edge : H.Adj a.val b.val) :
      G.Adj a b := by
    apply (P.hemisphere_selectionGraph_adj_iff N (center i) (cell i) a b).mpr
    exact ⟨(assigned _ i).mpr chosen, (assigned _ i).mpr (edge.2.1.symm.trans chosen),
      fun h => edge.1 (congrArg Subtype.val h), edge.2.2⟩
  ext f
  constructor
  · rintro ⟨g, member, rfl⟩
    change G.connectedComponentMk g = G.connectedComponentMk seedUp at member
    change H.connectedComponentMk g.val = H.connectedComponentMk seed
    rw [SimpleGraph.ConnectedComponent.eq] at member ⊢
    have chain := (G.reachable_iff_reflTransGen g seedUp).mp member
    exact (H.reachable_iff_reflTransGen g.val seed).mpr
      (Relation.ReflTransGen.lift Subtype.val (fun _ _ h => to_original h) g seedUp chain)
  · intro member
    change H.connectedComponentMk f = H.connectedComponentMk seed at member
    rw [SimpleGraph.ConnectedComponent.eq] at member
    have chain := (H.reachable_iff_reflTransGen seed f).mp member.symm
    clear member
    have preimage : ∃ chosen : label f = i, G.Reachable seedUp (upper f chosen) := by
      induction chain with
      | refl => exact ⟨rfl, ⟨SimpleGraph.Walk.nil⟩⟩
      | tail _ edge ih =>
        obtain ⟨chosen, reach⟩ := ih
        have next := edge.2.1.symm.trans chosen
        exact ⟨next, reach.trans (from_original chosen edge).reachable⟩
    obtain ⟨chosen, reached⟩ := preimage
    refine ⟨upper f chosen, ?_, rfl⟩
    change G.connectedComponentMk (upper f chosen) = G.connectedComponentMk seedUp
    exact SimpleGraph.ConnectedComponent.eq.mpr reached.symm

include assigned in
/-- The original polyhedral surface receives exactly one net per labeled component
when all local hemisphere developments are available. -/
theorem hasNetPartition_of_normal_cells
    (net : ∀ seed,
      (N.rotate (Cap.northFrame (center (label seed)))).upperComplex.HasOriginalEdgeNet
        (P.normalSelectionFaces N (center (label seed)) (unit (label seed))
          (cell (label seed)) (hemisphere (label seed)) seed ((assigned seed _).mpr rfl))) :
    C.HasNetPartition (Nat.card (C.labeledSeamGraph label).ConnectedComponent) := by
  apply C.hasNetPartition_card_labeledSeamGraph label
  intro c
  obtain ⟨f, rfl⟩ := c.exists_rep
  change C.HasOriginalEdgeNet ((C.labeledSeamGraph label).connectedComponentMk f).supp
  rw [← P.normalSelectionFaces_image_eq_labeled_component N cell center unit hemisphere
    label assigned f]
  exact C.hasOriginalEdgeNet_of_restrictFaces _ _ (net f)

end Unfoldings.SpatialFolding.ConvexBoundary
