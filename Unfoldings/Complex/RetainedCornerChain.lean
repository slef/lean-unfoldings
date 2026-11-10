module

public import Unfoldings.Complex.LinkSteps

/-! A retained spanning corner chain gives one actual cut vertex copy. -/

@[expose] public section

noncomputable section

namespace Unfoldings.TriangleComplex

universe u v

variable {Face : Type u} [Fintype Face] (C : TriangleComplex.{u, v} Face)
  (retain : Set C.Seam) {v : C.Vertex Set.univ} {n : ℕ}
  (c : (C.linkSystem Set.univ v).Chain n)
  (crossings : ∀ k : Fin n,
    C.GermCrosses retain (C.turnGerm (c.point k.castSucc).val) (c.point k.succ).val)

include crossings in
theorem retained_chain_corner_eq (i : Fin (n + 1)) :
    C.vertexOfCorner retain (c.point i).val.1 = C.vertexOfCorner retain c.first.val.1 := by
  refine Fin.induction ?_ (fun k previous => ?_) i
  · rfl
  · have same := (crossings k).vertex_eq
    exact same.symm.trans previous

include crossings in
/-- Every original corner at this vertex belongs to the same actual cut class. -/
theorem full_cut_star_of_retained_chain (covers : ∀ p, c.Visited p) (a : C.Corner)
    (original : C.vertexOfCorner Set.univ a = v) :
    C.vertexOfCorner retain a = C.vertexOfCorner retain c.first.val.1 := by
  let p : C.LinkGerm Set.univ v := ⟨(a, false), original⟩
  obtain ⟨i, equal | equal⟩ := covers p
  · have corners := congrArg (fun q : C.LinkGerm Set.univ v => q.val.1) equal
    change a = (c.point i).val.1 at corners
    rw [corners]
    exact C.retained_chain_corner_eq retain c crossings i
  · have corners := congrArg (fun q : C.LinkGerm Set.univ v => q.val.1) equal
    change a = (c.point i).val.1 at corners
    rw [corners]
    exact C.retained_chain_corner_eq retain c crossings i

include crossings in
/-- Cutting only at the two ends of this corner chain preserves the complete intrinsic angle. -/
theorem totalAngle_of_retained_chain (covers : ∀ p, c.Visited p) :
    C.totalAngle retain (C.vertexOfCorner retain c.first.val.1) = C.totalAngle Set.univ v := by
  classical
  have equivalence (a : C.Corner) :
      C.vertexOfCorner retain a = C.vertexOfCorner retain c.first.val.1 ↔
        C.vertexOfCorner Set.univ a = v := by
    constructor
    · intro same
      have original := congrArg (C.vertexForgetCuts (Set.subset_univ retain)) same
      rw [C.vertexForgetCuts_vertexOfCorner, C.vertexForgetCuts_vertexOfCorner] at original
      exact original.trans c.first.property
    · exact C.full_cut_star_of_retained_chain retain c crossings covers a
  simp only [totalAngle, equivalence]

include crossings in
/-- No additional copy of this original vertex is hidden elsewhere in the cut realization. -/
theorem unique_vertex_copy_of_retained_chain (covers : ∀ p, c.Visited p)
    (w : C.Vertex retain) (original : C.vertexForgetCuts (Set.subset_univ retain) w = v) :
    w = C.vertexOfCorner retain c.first.val.1 := by
  obtain ⟨a, rfl⟩ := C.vertexOfCorner_surjective retain w
  exact C.full_cut_star_of_retained_chain retain c crossings covers a original

end Unfoldings.TriangleComplex
