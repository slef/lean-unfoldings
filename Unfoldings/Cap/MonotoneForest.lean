module

public import Unfoldings.Cap.Boundary
public import Unfoldings.Cap.VertexWedge
public import Unfoldings.Complex.SeamGraph
public import Unfoldings.Topology.SelectedForest

/-!
# Construct an original-edge angle-monotone forest

Local acute-wedge progress constructs increasing parents, actual seam choices,
and a boundary-rooted spanning forest. All its outward paths use one common
wedge. This is a forest existence result; the source-centered sector assignment
needed for the cap nonoverlap proof is a further construction.
-/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexCap C)

theorem exists_monotone_seam_step (t : ℝ)
    (acute : ∀ f i, ((K.projectedTriangle f).sheared t).cornerAngle i < Real.pi / 2)
    (v : C.Vertex Set.univ) (internal : ¬ C.IsBoundaryVertex Set.univ v) :
    ∃ w s, C.seamGraph.IsLink s v w ∧
      StrictQuadrant (quadrantShear t (K.projectedVertex w - K.projectedVertex v)) := by
  have inside := (K.projectedVertex_mem_interior_iff v).mpr internal
  obtain ⟨f, i, vertex, forward⟩ := K.exists_projected_sheared_quadrant_edge t v inside acute
  have interior_corner : ¬ C.IsBoundaryVertex Set.univ (C.vertexOfCorner Set.univ (f, i)) := by
    rwa [vertex]
  have edges := C.exists_seamGraph_link_at_interior_corner f i interior_corner
  rcases forward with first | last
  · obtain ⟨s, link⟩ := edges.1
    rw [vertex] at link
    exact ⟨_, s, link, first⟩
  · obtain ⟨s, link⟩ := edges.2
    rw [vertex] at link
    exact ⟨_, s, link, last⟩

/-- Actual increasing parents and original seams with a geometric direction certificate. -/
structure MonotoneForest (t : ℝ) where
  parents : AscendingParents (C.Vertex Set.univ)
  roots_eq : parents.roots = {v | C.IsBoundaryVertex Set.univ v}
  selection : parents.EdgeSelection C.seamGraph
  direction : ∀ v ∉ parents.roots,
    StrictQuadrant (quadrantShear t (K.projectedVertex (parents.parent v) - K.projectedVertex v))

/-- Construct the forest data from acuteness, without assuming a forest or safe cuts. -/
def monotoneForest (t : ℝ)
    (acute : ∀ f i, ((K.projectedTriangle f).sheared t).cornerAngle i < Real.pi / 2) :
    K.MonotoneForest t := by
  classical
  let roots : Set (C.Vertex Set.univ) := {v | C.IsBoundaryVertex Set.univ v}
  have step (v : {v : C.Vertex Set.univ // v ∉ roots}) : ∃ w s,
      C.seamGraph.IsLink s v.val w ∧
        StrictQuadrant (quadrantShear t (K.projectedVertex w - K.projectedVertex v.val)) :=
    K.exists_monotone_seam_step t acute v.val v.property
  choose next edge linked directions using step
  let potential (v : C.Vertex Set.univ) : ℝ :=
    quadrantShear t (K.projectedVertex v) 0 + quadrantShear t (K.projectedVertex v) 1
  let P : AscendingParents (C.Vertex Set.univ) :=
    { roots := roots
      parent v := if h : v ∈ roots then v else next ⟨v, h⟩
      height := potential
      fixed_root v root := dite_eq_left root
      ascending v nonroot := by
        rw [dite_eq_right nonroot]
        have pair := directions ⟨v, nonroot⟩
        simp only [StrictQuadrant, map_sub, PiLp.sub_apply] at pair
        dsimp only [potential]
        linarith }
  let S : P.EdgeSelection C.seamGraph :=
    { edge v := edge ⟨v.val, v.property⟩
      link v := by
        have nonroot : v.val ∉ roots := v.property
        change C.seamGraph.IsLink (edge ⟨v.val, nonroot⟩) v.val
          (if h : v.val ∈ roots then v.val else next ⟨v.val, h⟩)
        rw [dite_eq_right nonroot]
        exact linked ⟨v.val, nonroot⟩ }
  refine ⟨P, rfl, S, ?_⟩
  intro v nonroot
  change StrictQuadrant (quadrantShear t
    (K.projectedVertex (if h : v ∈ roots then v else next ⟨v, h⟩) - K.projectedVertex v))
  have outside : v ∉ roots := nonroot
  rw [dite_eq_right outside]
  exact directions ⟨v, outside⟩

namespace MonotoneForest

variable {K} {t : ℝ} (M : K.MonotoneForest t)

theorem rootedForest : M.selection.graph.IsRootedForest {v | C.IsBoundaryVertex Set.univ v} := by
  rw [← M.roots_eq]
  exact M.selection.graph_rootedForest

theorem original_edges : M.selection.graph ≤ C.seamGraph := M.selection.graph_le rfl

theorem selected_edges_injective : Function.Injective M.selection.edge := M.selection.edge_injective

end MonotoneForest
end Unfoldings.ConvexCap
