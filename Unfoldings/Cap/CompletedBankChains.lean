module

public import Unfoldings.Cap.CompletedSubtreeSectors

/-! Enumerate the complete actual bank edges of an outward parent path in one common sector. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap.RadialCutForest

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexCap C} {source : Plane} {cuts : Set Plane} (N : K.RadialCutForest source cuts)

def completedBankChain (w : C.Vertex Set.univ) :
    Fin (N.spanningCompletion.parents.distanceToRoot w) →
      {v : C.Vertex Set.univ // v ∉ N.spanningCompletion.parents.roots} :=
  fun j => ⟨N.spanningCompletion.parents.parent^[j.val] w,
    N.spanningCompletion.parents.iterate_lt_distanceToRoot_not_mem w j.isLt⟩

theorem completedBankChain_parent (w : C.Vertex Set.univ)
    (j k : Fin (N.spanningCompletion.parents.distanceToRoot w)) (adjacent : k.val = j.val + 1) :
    N.spanningCompletion.parents.parent (N.completedBankChain w j).val =
      (N.completedBankChain w k).val := by
  change N.spanningCompletion.parents.parent (N.spanningCompletion.parents.parent^[j.val] w) =
    N.spanningCompletion.parents.parent^[k.val] w
  rw [adjacent, Function.iterate_succ_apply']

/-- The whole outward path and every curvature-carrying subtree along it share one sector.
All labels, directions, and parent indices are obtained from the actual covering network. -/
theorem exists_completedBankChain_sector_of_component_cover {I A : Type*} [Finite I]
    {t : ℝ} (outward : N.Outward) (first last : I → Plane) (label : I → A)
    (cover : cuts = ⋃ j, segment ℝ (first j) (last j))
    (piece_outward : ∀ j, 0 ≤ inner ℝ (first j - source) (last j - first j))
    (compatible : ∀ j k, (segment ℝ (first j) (last j) ∩
      segment ℝ (first k) (last k)).Nonempty → label j = label k)
    (component_sector : ∀ a : A, ∃ i : FiveSector,
      ∀ j, label j = a → last j - first j ∈ closedFiveSector t i)
    (covered : ∀ w : C.Vertex Set.univ, 0 < C.interiorAngularDefect Set.univ w →
      K.projectedVertex w ∈ cuts)
    (w : C.Vertex Set.univ) (member : K.projectedVertex w ∈ cuts) :
    ∃ i : FiveSector, ∀ j : Fin (N.spanningCompletion.parents.distanceToRoot w),
      (K.projectedVertex (N.spanningCompletion.parents.parent (N.completedBankChain w j).val) -
        K.projectedVertex (N.completedBankChain w j).val ∈ closedFiveSector t i) ∧
      N.CurvedSubtreeInSector (t := t) i (N.completedBankChain w j) := by
  let P := N.completedRootPath w
  obtain ⟨anchor, at_anchor⟩ := Set.mem_iUnion.mp (cover.subset member)
  obtain ⟨i, directions⟩ := component_sector (label anchor)
  have path_cover : ∀ j : Fin (N.spanningCompletion.parents.distanceToRoot w),
      segment ℝ (P.vertex j.castSucc) (P.vertex j.succ) ⊆
      ⋃ k, segment ℝ (first k) (last k) :=
    fun j => (N.completedRootPath_edge_subset member j).trans cover.subset
  have path_directions := P.directions_of_labeled_segment_cover source (fiveSectorFirst t i)
    (fiveSectorLast t i) first last label (N.completedRootPath_outward outward member)
    piece_outward compatible path_cover anchor at_anchor directions
  refine ⟨i, fun j => ⟨?_, ?_⟩⟩
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

end Unfoldings.ConvexCap.RadialCutForest
