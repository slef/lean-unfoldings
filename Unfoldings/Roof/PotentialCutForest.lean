module

public import Unfoldings.Roof.CurvatureCutDevelopment
public import Unfoldings.Roof.SeamEmbedding
public import Unfoldings.Geometry.LocalPotentialGrowth
public import Unfoldings.Complex.SelectedCutRootSupport

/-! Increasing potential constructs actual boundary-rooted whole-seam cuts on a roof. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexRoof C)

theorem vertex_eq_seamEndpoint_of_projected_edge (v : C.Vertex Set.univ) (s : C.Seam)
    (member : K.projectedVertex v ∈ (K.projectedTriangle (C.left s).face).edge (C.left s).edge) :
    ∃ b, v = C.seamVertex s b := by
  obtain ⟨i, at_corner⟩ := K.projected_corner_of_vertex_mem v (C.left s).face
    ((K.projectedTriangle (C.left s).face).edge_subset (C.left s).edge member)
  have vertex : (K.projectedTriangle (C.left s).face).IsVertex (K.projectedVertex v) :=
    ⟨i, at_corner⟩
  rcases ((K.projectedTriangle (C.left s).face).edge_vertex_iff (C.left s).edge
    ⟨K.projectedVertex v, member⟩).mp vertex with first | last
  · exact ⟨false, K.projectedVertex_injective first⟩
  · exact ⟨true, K.projectedVertex_injective last⟩

theorem exists_potential_ascending_seam (retain : Set C.Seam) (f : Plane → ℝ)
    (convex : ConvexOn ℝ Set.univ f) (v : C.Vertex Set.univ)
    (growth : LocalPotentialGrowth
      (⋃ s : {s : C.Seam // s ∉ retain},
        (K.projectedTriangle (C.left s.val).face).edge (C.left s.val).edge)
      f (K.projectedVertex v)) :
    ∃ w s, s ∉ retain ∧ C.seamGraph.IsLink s v w ∧
      f (K.projectedVertex v) < f (K.projectedVertex w) := by
  let first (s : {s : C.Seam // s ∉ retain}) := K.projectedVertex (C.seamVertex s.val false)
  let last (s : {s : C.Seam // s ∉ retain}) := K.projectedVertex (C.seamVertex s.val true)
  have edge_eq (s : {s : C.Seam // s ∉ retain}) :
      segment ℝ (first s) (last s) =
        (K.projectedTriangle (C.left s.val).face).edge (C.left s.val).edge := rfl
  obtain ⟨s, on_edge, larger⟩ := growth.exists_increasing_segment convex first last
    (by simp only [edge_eq]; exact Set.Subset.rfl)
  obtain ⟨b, at_endpoint⟩ :=
    K.vertex_eq_seamEndpoint_of_projected_edge v s.val ((edge_eq s).subset on_edge)
  cases b
  · refine ⟨C.seamVertex s.val true, s.val, s.property, Or.inl ⟨at_endpoint, rfl⟩, ?_⟩
    rcases larger with impossible | progress
    · exact (lt_irrefl _ (at_endpoint ▸ impossible)).elim
    · exact progress
  · refine ⟨C.seamVertex s.val false, s.val, s.property, Or.inr ⟨at_endpoint, rfl⟩, ?_⟩
    rcases larger with progress | impossible
    · exact progress
    · exact (lt_irrefl _ (at_endpoint ▸ impossible)).elim

/-- The roots away from the rim are unused vertices outside the geometric cuts. -/
structure PotentialCutForest (f : Plane → ℝ) (cuts : Set Plane) where
  parents : AscendingParents (C.Vertex Set.univ)
  roots_eq : parents.roots =
    {w | C.IsBoundaryVertex Set.univ w ∨ K.projectedVertex w ∉ cuts}
  height_eq : parents.height = fun w => f (K.projectedVertex w)
  selection : parents.EdgeSelection C.seamGraph
  selected_subset : ∀ e,
    (K.projectedTriangle (C.left (selection.edge e)).face).edge
      (C.left (selection.edge e)).edge ⊆ cuts

/-- Local growth constructs the parents and actual seams; no forest is assumed. -/
def potentialCutForest (f : Plane → ℝ) (cuts : Set Plane)
    (progress : ∀ w : C.Vertex Set.univ, ¬ C.IsBoundaryVertex Set.univ w →
      K.projectedVertex w ∈ cuts →
        ∃ z s, C.seamGraph.IsLink s w z ∧
          f (K.projectedVertex w) < f (K.projectedVertex z) ∧
            (K.projectedTriangle (C.left s).face).edge (C.left s).edge ⊆ cuts) :
    K.PotentialCutForest f cuts := by
  classical
  let roots := {w : C.Vertex Set.univ |
    C.IsBoundaryVertex Set.univ w ∨ K.projectedVertex w ∉ cuts}
  have choose_neighbor (w : C.Vertex Set.univ) (nonroot : w ∉ roots) :=
    progress w (fun boundary => nonroot (Or.inl boundary))
      (not_not.mp (fun outside => nonroot (Or.inr outside)))
  let nextVertex (w : C.Vertex Set.univ) :=
    if nonroot : w ∉ roots then (choose_neighbor w nonroot).choose else w
  let P : AscendingParents (C.Vertex Set.univ) := {
    roots := roots
    parent := nextVertex
    height := fun w => f (K.projectedVertex w)
    fixed_root := fun w root => dite_eq_right (not_not.mpr root)
    ascending := fun w nonroot => by
      simp only [nextVertex, dite_eq_left nonroot]
      exact (choose_neighbor w nonroot).choose_spec.choose_spec.2.1 }
  let S : P.EdgeSelection C.seamGraph := {
    edge := fun w => (choose_neighbor w.val w.property).choose_spec.choose
    link := fun w => by
      have nonroot : w.val ∉ roots := w.property
      change C.seamGraph.IsLink _ w.val (nextVertex w.val)
      simp only [nextVertex, dite_eq_left nonroot]
      exact (choose_neighbor w.val w.property).choose_spec.choose_spec.1 }
  exact ⟨P, rfl, rfl, S,
    fun w => (choose_neighbor w.val w.property).choose_spec.choose_spec.2.2⟩

end Unfoldings.ConvexRoof
