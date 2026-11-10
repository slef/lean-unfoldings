module

public import Unfoldings.Cap.ProjectedLink
public import Unfoldings.Complex.SingleLinkCut
public import Unfoldings.Complex.SeamGraph

/-! An actual single cut seam at a cap vertex opens exactly one original link pair. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexCap C)
  {v : C.Vertex Set.univ}

include K in
theorem linkGerm_eq_of_edge (p q : C.LinkGerm Set.univ v)
    (same : C.germEdge p.val = C.germEdge q.val) : p = q := by
  apply Subtype.ext
  apply C.germ_eq_of_corner_edge _ same
  have corners : (⟨p.val.1, p.property⟩ : C.CornerAt Set.univ v) = ⟨q.val.1, q.property⟩ :=
    K.cornerAt_face_injective v (congrArg EdgeRef.face same)
  exact congrArg Subtype.val corners

/-- The canonical left-side endpoint germ names an actual seam incidence. -/
theorem exists_linkGerm_at_seam {s : C.Seam} {w : C.Vertex Set.univ}
    (link : C.seamGraph.IsLink s v w) :
    ∃ p : C.LinkGerm Set.univ v, C.germEdge p.val = C.left s := by
  rcases link with ⟨first, _⟩ | ⟨first, _⟩
  · exact ⟨⟨C.germOfEndpoint (C.left s) false, first.symm⟩, C.germEdge_germOfEndpoint _ _⟩
  · exact ⟨⟨C.germOfEndpoint (C.left s) true, first.symm⟩, C.germEdge_germOfEndpoint _ _⟩

include K in
/-- Degree-one cut incidence implies preservation of every other original link pairing. -/
theorem preserves_other_link_pairs_of_single_cut (retain : Set C.Seam) (edge : C.Seam)
    (p : C.LinkGerm Set.univ v) (pedge : C.germEdge p.val = C.left edge)
    (unique_cut : ∀ s ∉ retain, ∀ w, C.seamGraph.IsLink s v w → s = edge) :
    ∀ q r : C.LinkGerm Set.univ v, q ≠ p → q ≠ C.linkMate Set.univ v p →
      C.GermCrosses Set.univ q.val r.val → C.GermCrosses retain q.val r.val := by
  intro q r qne qmate crossing
  obtain ⟨s, _, side, b, first, last⟩ := crossing
  by_cases kept : s ∈ retain
  · exact ⟨s, kept, side, b, first, last⟩
  · have original_class := q.property
    rw [first] at original_class
    have incident : ∃ w, C.seamGraph.IsLink s v w := by
      have link := C.seamGraph_side_link s side
      cases b
      · rw [original_class] at link
        exact ⟨_, link⟩
      · rw [original_class] at link
        exact ⟨_, link.symm⟩
    obtain ⟨w, link⟩ := incident
    have same := unique_cut s kept w link
    subst s
    cases side
    · have qedge : C.germEdge q.val = C.left edge := by
        rw [first, C.germEdge_germOfEndpoint]
        rfl
      exact (qne (K.linkGerm_eq_of_edge q p (qedge.trans pedge.symm))).elim
    · have redge : C.germEdge r.val = C.left edge := by
        rw [last, C.germEdge_germOfEndpoint]
        rfl
      have equal := K.linkGerm_eq_of_edge r p (redge.trans pedge.symm)
      have paired : C.linkMate Set.univ v q = r := by
        apply Subtype.ext
        exact C.mateGerm_of_crossing ⟨edge, Set.mem_univ _, true, b, first, last⟩
      have contradiction : q = C.linkMate Set.univ v p := by
        calc
          q = C.linkMate Set.univ v (C.linkMate Set.univ v q) :=
            (C.linkMate_involutive Set.univ v q).symm
          _ = C.linkMate Set.univ v p := congrArg _ (paired.trans equal)
      exact (qmate contradiction).elim

end Unfoldings.ConvexCap
