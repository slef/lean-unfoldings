module

public import Unfoldings.Cap.CompletedBankChains

/-! One component sector controls the positions and directions of an actual fine bank path. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap.RadialCutForest

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexCap C} {source : Plane} {cuts : Set Plane} (N : K.RadialCutForest source cuts)

/-- Retain physical positions in the same sector as the path directions and all
curvature-carrying descendant openings. The sector comes from the actual cut component. -/
theorem exists_completedBankChain_sector_positions_of_component_cover {I A : Type*} [Finite I]
    {t : ℝ} (outward : N.Outward) (first last : I → Plane) (label : I → A)
    (cover : cuts = ⋃ j, segment ℝ (first j) (last j))
    (piece_outward : ∀ j, 0 ≤ inner ℝ (first j - source) (last j - first j))
    (compatible : ∀ j k, (segment ℝ (first j) (last j) ∩
      segment ℝ (first k) (last k)).Nonempty → label j = label k)
    (component_sector : ∀ a : A, ∃ i : FiveSector,
      (∀ j, label j = a → last j - first j ∈ closedFiveSector t i) ∧
      ∀ j, label j = a → ∀ p ∈ segment ℝ (first j) (last j),
        p - source ∈ closedFiveSector t i)
    (covered : ∀ w : C.Vertex Set.univ, 0 < C.interiorAngularDefect Set.univ w →
      K.projectedVertex w ∈ cuts)
    (w : C.Vertex Set.univ) (member : K.projectedVertex w ∈ cuts) :
    ∃ i : FiveSector,
      (∀ j : Fin (N.spanningCompletion.parents.distanceToRoot w),
        (K.projectedVertex (N.spanningCompletion.parents.parent (N.completedBankChain w j).val) -
          K.projectedVertex (N.completedBankChain w j).val ∈ closedFiveSector t i) ∧
        N.CurvedSubtreeInSector (t := t) i (N.completedBankChain w j)) ∧
      ∀ j : Fin (N.spanningCompletion.parents.distanceToRoot w + 1),
        (N.completedRootPath w).vertex j - source ∈ closedFiveSector t i := by
  let P := N.completedRootPath w
  obtain ⟨anchor, at_anchor⟩ := Set.mem_iUnion.mp (cover.subset member)
  obtain ⟨i, directions, positions⟩ := component_sector (label anchor)
  have path_cover : ∀ j : Fin (N.spanningCompletion.parents.distanceToRoot w),
      segment ℝ (P.vertex j.castSucc) (P.vertex j.succ) ⊆
      ⋃ k, segment ℝ (first k) (last k) :=
    fun j => (N.completedRootPath_edge_subset member j).trans cover.subset
  have path_directions := P.directions_of_labeled_segment_cover source (fiveSectorFirst t i)
    (fiveSectorLast t i) first last label (N.completedRootPath_outward outward member)
    piece_outward compatible path_cover anchor at_anchor directions
  refine ⟨i, fun j => ⟨?_, ?_⟩, ?_⟩
  · have direction := path_directions j
    change InDirectionWedge (fiveSectorFirst t i) (fiveSectorLast t i)
      (K.projectedVertex (N.spanningCompletion.parents.parent^[j.val + 1] w) -
        K.projectedVertex (N.spanningCompletion.parents.parent^[j.val] w)) at direction
    rw [Function.iterate_succ_apply'] at direction
    exact direction
  · obtain ⟨current, at_current⟩ := Set.mem_iUnion.mp
      (cover.subset (N.completedRootPath_vertex_mem member j.castSucc))
    have same := P.labels_eq_of_segment_cover first last label compatible path_cover anchor
      at_anchor j.castSucc current at_current
    intro child ancestor positive
    exact N.nonzero_descendant_direction_of_component_cover outward first last label cover
      piece_outward compatible covered (N.completedBankChain w j) child ancestor positive current
      at_current (fiveSectorFirst t i) (fiveSectorLast t i)
      (fun k equal => directions k (equal.trans same))
  · intro j
    obtain ⟨current, at_current⟩ := Set.mem_iUnion.mp
      (cover.subset (N.completedRootPath_vertex_mem member j))
    exact positions current (P.labels_eq_of_segment_cover first last label compatible path_cover
      anchor at_anchor j current at_current) _ at_current

end Unfoldings.ConvexCap.RadialCutForest
