module

public import Unfoldings.Cap.ChildBankContactFlatness
public import Unfoldings.Cap.SingleCutStar

/-! Flat proper descendant openings become a single actual intrinsic vertex after pruning. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap.SectorForest

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexCap C} {t : ℝ} {origin : C.Vertex Set.univ} (M : K.SectorForest t origin)

open Classical in
/-- If every proper descendant subtree is flat, pruning identifies all copies of the endpoint.
The endpoint's own curvature may be positive or zero. -/
theorem curved_vertex_copies_eq_of_flat_proper_descendants
    (e : {v : C.Vertex Set.univ // v ∉ M.parents.roots})
    (flat : ∀ v : C.Vertex Set.univ, M.parents.Ancestor v e.val → v ≠ e.val →
      M.subtreeCurvature v = 0)
    (a b : C.Vertex M.curvedRetain)
    (first : C.vertexForgetCuts (Set.subset_univ _) a = e.val)
    (last : C.vertexForgetCuts (Set.subset_univ _) b = e.val) : a = b := by
  have internal : ¬ C.IsBoundaryVertex Set.univ e.val := by
    simpa only [M.roots_eq, Set.mem_ofPred_eq] using e.property
  let edge := M.selection.edge e
  obtain ⟨p, pedge⟩ := exists_linkGerm_at_seam (M.selection.link e)
  have unique_cut : ∀ s ∉ M.curvedRetain, ∀ w,
      C.seamGraph.IsLink s e.val w → s = edge := by
    intro s cut w link
    obtain ⟨u, named, curved⟩ := M.curved_cut_subtree_positive cut
    have selected : M.selection.graph.IsLink s e.val w :=
      M.selection.graph_isLink_iff.mpr ⟨⟨u, named⟩, link⟩
    obtain ⟨v, named_v, endpoints⟩ := selected
    have same_name : v = u := M.selection.edge_injective (named_v.trans named.symm)
    subst v
    rcases endpoints with ⟨same, _⟩ | ⟨parent, _⟩
    · have equal : u = e := Subtype.ext same.symm
      exact named.symm.trans (congrArg M.selection.edge equal)
    · have reaches : M.parents.Ancestor u.val e.val :=
        parent ▸ M.parents.ancestor_parent u.val
      have different : u.val ≠ e.val := by
        intro equal
        have ascending := M.parents.ascending u.val u.property
        rw [← parent, equal] at ascending
        exact lt_irrefl _ ascending
      exact (curved.ne' (flat u.val reaches different)).elim
  have preserves := K.preserves_other_link_pairs_of_single_cut M.curvedRetain edge p pedge
    unique_cut
  exact (C.unique_vertex_copy_of_single_link_cut M.curvedRetain internal p preserves a first).trans
    (C.unique_vertex_copy_of_single_link_cut M.curvedRetain internal p preserves b last).symm

open Classical in
/-- A contact of the actual parent-bank child endpoints identifies one intrinsic pruned vertex. -/
theorem curved_vertex_copies_eq_of_child_bank_contact
    {positive : 0 < t} {small : t < 1} {D : FacewiseDevelopment C M.retain}
    (B : M.SectorFrameData positive small D)
    (e : {v : C.Vertex Set.univ // v ∉ M.parents.roots})
    (budget : C.totalInteriorAngularDefect Set.univ < Real.pi)
    (same : M.parentEntrancePoint D e 1 = M.parentExitPoint D e 1)
    (a b : C.Vertex M.curvedRetain)
    (first : C.vertexForgetCuts (Set.subset_univ _) a = e.val)
    (last : C.vertexForgetCuts (Set.subset_univ _) b = e.val) : a = b :=
  M.curved_vertex_copies_eq_of_flat_proper_descendants e
    ((B.child_bank_points_eq_iff_flat_proper_descendants e budget).mp same) a b first last

end Unfoldings.ConvexCap.SectorForest
