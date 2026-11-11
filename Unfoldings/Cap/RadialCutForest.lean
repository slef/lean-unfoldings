module

public import Unfoldings.Cap.RadialCutNeighbor
public import Unfoldings.Cap.Topology
public import Unfoldings.Complex.SelectedCutRootSupport

/-! Actual boundary-rooted cut forests selected by strict source-distance increase. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexCap C)

/-- A parent forest supported on a prescribed geometric cut set. Unused flat vertices may be
isolated marked roots; every root occurring in the actual cut graph is on the original rim. -/
structure RadialCutForest (q : Plane) (cuts : Set Plane) where
  parents : AscendingParents (C.Vertex Set.univ)
  roots_eq : parents.roots =
    {w | C.IsBoundaryVertex Set.univ w ∨ K.projectedVertex w ∉ cuts}
  height_eq : parents.height = fun w => dist q (K.projectedVertex w)
  selection : parents.EdgeSelection C.seamGraph
  selected_subset : ∀ e,
    (K.projectedTriangle (C.left (selection.edge e)).face).edge
      (C.left (selection.edge e)).edge ⊆ cuts

/-- Construct the forest from actual outward seam neighbors, keeping their original names. -/
def radialCutForest (q : Plane) (cuts : Set Plane)
    (progress : ∀ w : C.Vertex Set.univ, ¬ C.IsBoundaryVertex Set.univ w →
      K.projectedVertex w ∈ cuts →
        ∃ z s, C.seamGraph.IsLink s w z ∧
          dist q (K.projectedVertex w) < dist q (K.projectedVertex z) ∧
            (K.projectedTriangle (C.left s).face).edge (C.left s).edge ⊆ cuts) :
    K.RadialCutForest q cuts := by
  classical
  let roots := {w : C.Vertex Set.univ |
    C.IsBoundaryVertex Set.univ w ∨ K.projectedVertex w ∉ cuts}
  have choose_neighbor (w : C.Vertex Set.univ) (nonroot : w ∉ roots) :=
    progress w (fun boundary => nonroot (Or.inl boundary))
      (not_not.mp (fun outside => nonroot (Or.inr outside)))
  let nextVertex (w : C.Vertex Set.univ) :=
    if nonroot : w ∉ roots then (choose_neighbor w nonroot).choose else w
  let P : AscendingParents (C.Vertex Set.univ) :=
    { roots := roots
      parent := nextVertex
      height := fun w => dist q (K.projectedVertex w)
      fixed_root := fun w root => dite_eq_right (not_not.mpr root)
      ascending := fun w nonroot => by
        simp only [nextVertex, dite_eq_left nonroot]
        exact (choose_neighbor w nonroot).choose_spec.choose_spec.2.1 }
  let S : P.EdgeSelection C.seamGraph :=
    { edge := fun w => (choose_neighbor w.val w.property).choose_spec.choose
      link := fun w => by
        have nonroot : w.val ∉ roots := w.property
        change C.seamGraph.IsLink _ w.val (nextVertex w.val)
        simp only [nextVertex, dite_eq_left nonroot]
        exact (choose_neighbor w.val w.property).choose_spec.choose_spec.1 }
  exact ⟨P, rfl, rfl, S,
    fun w => (choose_neighbor w.val w.property).choose_spec.choose_spec.2.2⟩

namespace RadialCutForest

variable {K} {q : Plane} {cuts : Set Plane} (R : K.RadialCutForest q cuts)

def retain : Set C.Seam := C.selectedRetain R.selection

/-- The actual relative cut graph has exactly one old boundary root in every component. -/
theorem rootedForest :
    (C.relativeCutGraph R.retain Set.univ).IsRootedForest (C.relativeCutRoots Set.univ) := by
  apply C.selectedCut_rootedForest_of_root_support R.selection
  · intro w boundary
    exact (Set.ext_iff.mp R.roots_eq w).mpr (Or.inl boundary)
  · intro w root incident
    rcases incident with boundary | ⟨s, b, endpoint⟩
    · exact boundary
    · obtain ⟨e, chosen⟩ := not_not.mp s.property.2
      have on_edge : K.projectedVertex w ∈
          (K.projectedTriangle (C.left s.val).face).edge (C.left s.val).edge := by
        change w = C.seamVertex s.val b at endpoint
        rw [endpoint]
        cases b
        · exact left_mem_segment ℝ _ _
        · exact right_mem_segment ℝ _ _
      have selected : (K.projectedTriangle (C.left s.val).face).edge (C.left s.val).edge ⊆ cuts :=
        chosen ▸ R.selected_subset e
      rcases (Set.ext_iff.mp R.roots_eq w).mp root with boundary | outside
      · exact boundary
      · exact (outside (selected on_edge)).elim

/-- The selected actual edges cut the supplied disk into one disk. -/
def cutDisk : C.Realization R.retain ≃ₜ Metric.closedBall (0 : Plane) 1 :=
  K.folding.cutDiskHomeomorphOfRootedForest (Set.subset_univ _) K.diskHomeomorph R.rootedForest

end RadialCutForest
end Unfoldings.ConvexCap
