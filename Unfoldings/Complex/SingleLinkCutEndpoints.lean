module

public import Unfoldings.Complex.SingleLinkCut

/-! The two actual terminal cut germs are exactly the original opened seam pair. -/

@[expose] public section

noncomputable section

namespace Unfoldings.TriangleComplex

universe u v

variable {Face : Type u} [Fintype Face] (C : TriangleComplex.{u, v} Face)
  (retain : Set C.Seam) {v : C.Vertex Set.univ}

theorem boundary_germ_of_single_link_cut (internal : ¬ C.IsBoundaryVertex Set.univ v)
    (p : C.LinkGerm Set.univ v)
    (preserves : ∀ q r : C.LinkGerm Set.univ v, q ≠ p → q ≠ C.linkMate Set.univ v p →
      C.GermCrosses Set.univ q.val r.val → C.GermCrosses retain q.val r.val)
    {w : C.Vertex retain} (original : C.vertexForgetCuts (Set.subset_univ retain) w = v)
    (q : C.LinkGerm retain w) (fixed : C.linkMate retain w q = q) :
    q.val = p.val ∨ q.val = C.mateGerm Set.univ p.val := by
  let q' : C.LinkGerm Set.univ v := ⟨q.val, by
    have mapped := congrArg (C.vertexForgetCuts (Set.subset_univ retain)) q.property
    exact mapped.trans original⟩
  by_cases first : q' = p
  · exact Or.inl (congrArg Subtype.val first)
  by_cases last : q' = C.linkMate Set.univ v p
  · exact Or.inr (congrArg Subtype.val last)
  have free : C.linkMate Set.univ v q' ≠ q' := fun equal =>
    internal ((C.isBoundaryVertex_iff_linkMate_fixed Set.univ v).mpr ⟨q', equal⟩)
  have paired : ∃ r, C.GermCrosses Set.univ q'.val r := by
    apply (C.exists_germCrosses_iff Set.univ q'.val).mpr
    intro boundary
    apply internal
    have original_boundary := C.isBoundaryVertex_of_boundary_germ Set.univ q'.val boundary
    rwa [q'.property] at original_boundary
  obtain ⟨r, crossing⟩ := paired
  have actual : C.GermCrosses Set.univ q'.val (C.linkMate Set.univ v q').val := by
    change C.GermCrosses Set.univ q'.val (C.mateGerm Set.univ q'.val)
    rw [C.mateGerm_of_crossing crossing]
    exact crossing
  have kept := preserves q' (C.linkMate Set.univ v q') first last actual
  have equal : C.linkMate Set.univ v q' = q' := by
    apply Subtype.ext
    exact (C.mateGerm_of_crossing kept).symm.trans (congrArg Subtype.val fixed)
  exact (free equal).elim

theorem terminal_germs_mate_of_single_link_cut (internal : ¬ C.IsBoundaryVertex Set.univ v)
    (p : C.LinkGerm Set.univ v)
    (preserves : ∀ q r : C.LinkGerm Set.univ v, q ≠ p → q ≠ C.linkMate Set.univ v p →
      C.GermCrosses Set.univ q.val r.val → C.GermCrosses retain q.val r.val)
    {w : C.Vertex retain} (original : C.vertexForgetCuts (Set.subset_univ retain) w = v)
    {n : ℕ} (c : (C.linkSystem retain w).Chain n)
    (start : C.linkMate retain w c.first = c.first)
    (finish : C.linkMate retain w (C.linkTurn retain w c.last) = C.linkTurn retain w c.last) :
    (C.linkTurn retain w c.last).val = C.mateGerm Set.univ c.first.val := by
  have different : c.first.val ≠ (C.linkTurn retain w c.last).val := fun equal =>
    c.disjoint 0 (Fin.last n) (Subtype.ext equal)
  rcases C.boundary_germ_of_single_link_cut retain internal p preserves original c.first start with
    first | first <;>
    rcases C.boundary_germ_of_single_link_cut retain internal p preserves original
      (C.linkTurn retain w c.last) finish with last | last
  · exact (different (first.trans last.symm)).elim
  · rw [first]
    exact last
  · rw [first, C.mateGerm_involutive]
    exact last
  · exact (different (first.trans last.symm)).elim

end Unfoldings.TriangleComplex
