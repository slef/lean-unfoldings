module

public import Unfoldings.FewestNets.SphericalPartition

/-! Local upper-roof component nets descend to the literal original face labels. -/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialFolding.ConvexBoundary

universe u v w

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {F : SpatialFolding C} (P : F.ConvexBoundary) (N : F.SupportingNormals)
  {Label : Type w} (label : Face → Label) (key : Label)

/-- An arbitrary physical frame may be used for the chosen label, provided
all faces of that label are upper faces with exactly the selected slopes. -/
theorem upperRoof_selectionComponent_image_eq_labeled_component
    (frame : Space ≃ₗᵢ[ℝ] Space) {region : Set Plane}
    (selected : ∀ f : (N.rotate frame).UpperFace,
      ((P.rotate frame).upperRoof (N.rotate frame)).normalSlope f ∈ region ↔ label f.val = key)
    (upper : ∀ f, label f = key → 0 < (N.rotate frame).normal f 2)
    (seed : (N.rotate frame).UpperFace) (seed_label : label seed.val = key) :
    Subtype.val '' ((P.rotate frame).upperRoof (N.rotate frame)).selectionComponent region seed =
      ((C.labeledSeamGraph label).connectedComponentMk seed.val).supp := by
  let N' := N.rotate frame
  let roof := (P.rotate frame).upperRoof N'
  let S := roof.selectionGraph region
  let G := C.labeledSeamGraph label
  have triangles : roof.projectedTriangle = N'.upperTriangle := by
    funext f
    apply Triangle.eq_of_vertex_eq
    intro i
    rfl
  have adjacency (a b : N'.UpperFace) :
      S.Adj a b ↔ label a.val = key ∧ label b.val = key ∧ a ≠ b ∧
        ∃ s : C.Seam, ((C.left s).face = a.val ∧ (C.right s).face = b.val) ∨
          ((C.left s).face = b.val ∧ (C.right s).face = a.val) := by
    change (_ ∧ _ ∧ TriangleFamily.EdgeAdjacent roof.projectedTriangle a b) ↔ _
    rw [selected, selected, triangles, N'.upper_edgeAdjacent_iff (P.rotate frame)]
  have to_original {a b} (edge : S.Adj a b) : G.Adj a.val b.val := by
    obtain ⟨ha, hb, different, seam⟩ := (adjacency a b).mp edge
    exact ⟨fun h => different (Subtype.ext h), ha.trans hb.symm, seam⟩
  have from_original {a b : N'.UpperFace} (chosen : label a.val = key)
      (edge : G.Adj a.val b.val) : S.Adj a b :=
    (adjacency a b).mpr ⟨chosen, edge.2.1.symm.trans chosen,
      fun h => edge.1 (congrArg Subtype.val h), edge.2.2⟩
  ext f
  constructor
  · rintro ⟨a, member, rfl⟩
    change S.connectedComponentMk a = S.connectedComponentMk seed at member
    change G.connectedComponentMk a.val = G.connectedComponentMk seed.val
    rw [SimpleGraph.ConnectedComponent.eq] at member ⊢
    have chain := (S.reachable_iff_reflTransGen a seed).mp member
    exact (G.reachable_iff_reflTransGen a.val seed.val).mpr
      (Relation.ReflTransGen.lift Subtype.val (fun _ _ h => to_original h) a seed chain)
  · intro member
    change G.connectedComponentMk f = G.connectedComponentMk seed.val at member
    rw [SimpleGraph.ConnectedComponent.eq] at member
    have chain := (G.reachable_iff_reflTransGen seed.val f).mp member.symm
    clear member
    let lift (x : Face) (chosen : label x = key) : N'.UpperFace := ⟨x, upper x chosen⟩
    have preimage : ∃ chosen : label f = key, S.Reachable seed (lift f chosen) := by
      induction chain with
      | refl => exact ⟨seed_label, ⟨SimpleGraph.Walk.nil⟩⟩
      | tail _ edge ih =>
        obtain ⟨chosen, reach⟩ := ih
        have next := edge.2.1.symm.trans chosen
        exact ⟨next, reach.trans (from_original chosen edge).reachable⟩
    obtain ⟨chosen, reached⟩ := preimage
    refine ⟨lift f chosen, ?_, rfl⟩
    exact SimpleGraph.ConnectedComponent.eq.mpr reached.symm

end Unfoldings.SpatialFolding.ConvexBoundary
