module

public import Unfoldings.Complex.ContourChildVisits
public import Unfoldings.Complex.RestoredVertexSeams
public import Unfoldings.Complex.EdgeReverseGerm
public import Unfoldings.Complex.IncidentSeamFans

/-! Restoring an original child edge joins the two contour copies at its parent. -/

@[expose] public section

noncomputable section

namespace Unfoldings.TriangleComplex

universe u v

variable {Face : Type u} [Fintype Face] (C : TriangleComplex.{u, v} Face)
  {P : AscendingParents (C.Vertex Set.univ)} (S : P.EdgeSelection C.seamGraph)
  (Q : C.BoundaryContour (C.selectedRetain S))
  (roots : C.relativeCutRoots Set.univ ⊆ P.roots)
  (starts : C.contourOriginalVertex S Q 0 ∈ P.roots)

local notation "Retain" => C.selectedRetain S
local notation "E" => C.boundaryEndEquiv Retain
local notation "Orig" => (C.vertexForgetCuts (Set.subset_univ Retain) ∘ C.boundaryEndVertex Retain)

private theorem germ_eq_of_original_endpoint (p q : C.Germ)
    (edge : C.germEdge p = C.germEdge q)
    (original : C.vertexOfCorner Set.univ p.1 = C.vertexOfCorner Set.univ q.1)
    (distinct : C.vertexOfCorner Set.univ (C.edgeReverseGerm q).1 ≠
      C.vertexOfCorner Set.univ q.1) : p = q := by
  have named : p = C.germOfEndpoint (C.germEdge q) p.2 :=
    (C.germOfEndpoint_germEdge p).symm.trans
      (congrArg (fun e => C.germOfEndpoint e p.2) edge)
  have ends : p.2 = q.2 ∨ p.2 = !q.2 := by cases p.2 <;> cases q.2 <;> simp
  rcases ends with same | reverse
  · exact named.trans ((congrArg (C.germOfEndpoint (C.germEdge q)) same).trans
      (C.germOfEndpoint_germEdge q))
  · have equal : p = C.edgeReverseGerm q := named.trans
      (congrArg (C.germOfEndpoint (C.germEdge q)) reverse)
    exact (distinct ((congrArg (fun p : C.Germ => C.vertexOfCorner Set.univ p.1)
      equal).symm.trans original)).elim

/-- The entry and exit at the parent are opposite germs of the same original child seam. -/
theorem contourChild_parent_germ_crosses (child : C.Vertex Set.univ) (nonroot : child ∉ P.roots)
    {large : Set C.Seam} (restored : S.edge ⟨child, nonroot⟩ ∈ large) :
    let data := C.contourParentInterval S Q roots starts child nonroot
    C.GermCrosses large (Q.cycle.point data.enter).val
      (C.boundaryTurn Retain (Q.cycle.point data.leave)).val := by
  let data := C.contourParentInterval S Q roots starts child nonroot
  let p := Q.cycle.point data.enter
  let q := Q.cycle.point data.leave
  let last := C.boundaryTurn Retain q
  let cut := C.selectedParentCut S child nonroot
  let s := S.edge ⟨child, nonroot⟩
  let b := p.val.2
  have edge : C.germEdge p.val = C.seamSide s data.side :=
    congrArg Subtype.val data.entry_named
  have first : p.val = C.germOfEndpoint (C.seamSide s data.side) b :=
    (C.germOfEndpoint_germEdge p.val).symm.trans
      (congrArg (fun g => C.germOfEndpoint g b) edge)
  let other := C.relativeCutBank Retain Set.univ cut (!data.side)
  let mate := (E).symm (other, C.acrossEndpoint s data.side b)
  have mate_cross : C.GermCrosses Set.univ p.val mate.val :=
    ⟨s, Set.mem_univ _, data.side, b, first, rfl⟩
  have compatible : Orig mate = P.parent child :=
    mate_cross.vertex_eq.symm.trans
      (C.contourParentInterval_entry_original S Q roots starts child nonroot).1
  have labels : (E mate).1 = (E last).1 := by
    have first_tag : (E mate).1 = other := congrArg Prod.fst ((E).apply_symm_apply _)
    have last_tag : (E last).1 = other := by
      change (E ((E).symm ((E q).1, !(E q).2))).1 = other
      exact (congrArg Prod.fst ((E).apply_symm_apply _)).trans data.exit_named
    exact first_tag.trans last_tag.symm
  have mate_eq : mate = last := by
    rcases (C.boundaryEnd_bank_eq_iff Retain mate last).mp labels with aligned | reverse
    · exact aligned
    · have turn_q : C.boundaryTurn Retain last = q := C.boundaryTurn_involutive Retain q
      have original_child : Orig q = child :=
        (C.contourParentInterval_exit_original S Q roots starts child nonroot).1
      have same : P.parent child = child := compatible.symm.trans
        ((congrArg Orig (reverse.trans turn_q)).trans original_child)
      exact ((ne_of_gt (P.ascending child nonroot)) (congrArg P.height same)).elim
  exact ⟨s, restored, data.side, b, first, (congrArg Subtype.val mate_eq).symm⟩

/-- Restoring that seam connects the parent copies before and after the corresponding excursion. -/
theorem contourChild_restored_parent_seam (child : C.Vertex Set.univ) (nonroot : child ∉ P.roots)
    {large : Set C.Seam} (restored : S.edge ⟨child, nonroot⟩ ∈ large) :
    let data := C.contourParentInterval S Q roots starts child nonroot
    let back := finRotate (Q.length + 1) data.leave
    C.RestoredVertexSeam Retain large
      (C.boundaryEndVertex Retain (Q.cycle.point data.enter))
      (C.boundaryEndVertex Retain (Q.cycle.point back)) := by
  let data := C.contourParentInterval S Q roots starts child nonroot
  let s := S.edge ⟨child, nonroot⟩
  let p := Q.cycle.point data.enter
  let q := C.boundaryTurn Retain (Q.cycle.point data.leave)
  have named := C.contourChild_parent_germ_crosses S Q roots starts child nonroot restored
  obtain ⟨seam, in_large, side, b, hp, hq⟩ := named
  have edge : C.germEdge p.val = C.seamSide s data.side :=
    congrArg Subtype.val data.entry_named
  have seam_eq : seam = s := by
    have equality : C.seamSide seam side = C.seamSide s data.side :=
      (C.germEdge_germOfEndpoint _ _).symm.trans ((congrArg C.germEdge hp).symm.trans edge)
    exact congrArg Prod.fst (C.seamSide_injective (a₁ := (seam, side)) (a₂ := (s, data.side)) equality)
  have cut : s ∉ Retain := (C.selectedParentCut S child nonroot).property.2
  have lower : C.boundaryEndVertex Retain q =
      C.boundaryEndVertex Retain (Q.cycle.point (finRotate (Q.length + 1) data.leave)) :=
    congrArg Subtype.val (C.boundaryCycle_next_vertex Retain Q.cycle Q.closes data.leave)
  exact ⟨seam, ⟨in_large, seam_eq.symm ▸ cut⟩, side, b,
    congrArg (fun p : C.Germ => C.vertexOfCorner Retain p.1) hp,
    lower.symm.trans (congrArg (fun p : C.Germ => C.vertexOfCorner Retain p.1) hq)⟩


/-- At a nonroot with its outgoing edge still cut, every restored incident seam is
a child excursion and joins precisely the two contour copies at its ends. -/
theorem exists_child_of_restoredVertexSeam
    (parent : C.Vertex Set.univ) (nonroot : parent ∉ P.roots)
    {large : Set C.Seam} (outgoing_cut : S.edge ⟨parent, nonroot⟩ ∉ large)
    (x y : C.Vertex Retain) (original : C.vertexForgetCuts (Set.subset_univ Retain) x = parent)
    (step : C.RestoredVertexSeam Retain large x y) :
    ∃ (child : C.Vertex Set.univ) (fresh : child ∉ P.roots),
      P.parent child = parent ∧ S.edge ⟨child, fresh⟩ ∈ large ∧
      let data := C.contourParentInterval S Q roots starts child fresh
      let before := C.boundaryEndVertex Retain (Q.cycle.point data.enter)
      let after := C.boundaryEndVertex Retain (Q.cycle.point (finRotate (Q.length + 1) data.leave))
      (x = before ∧ y = after) ∨ (x = after ∧ y = before) := by
  classical
  obtain ⟨s, kept, side, b, hx, hy⟩ := step
  let p := C.germOfEndpoint (C.seamSide s side) b
  let q := C.germOfEndpoint (C.seamSide s (!side)) (C.acrossEndpoint s side b)
  obtain ⟨child', named⟩ : ∃ c : {v : C.Vertex Set.univ // v ∉ P.roots}, S.edge c = s := by
    by_contra none
    exact kept.2 (fun h => none h)
  let child := child'.val
  have fresh := child'.property
  have s_eq : s = S.edge ⟨child, fresh⟩ := named.symm
  have in_large : S.edge ⟨child, fresh⟩ ∈ large := s_eq ▸ kept.1
  have at_parent : C.vertexOfCorner Set.univ p.1 = parent :=
    (congrArg (C.vertexForgetCuts (Set.subset_univ Retain)) hx).symm.trans original
  obtain ⟨other, linked⟩ := C.seamGraph_exists_link_of_germEdge s side p
    (C.germEdge_germOfEndpoint _ _)
  have endpoints := S.link child'
  rw [named] at endpoints
  have p_at : P.parent child = parent := by
    rcases linked.eq_and_eq_or_eq_and_eq endpoints with child_at | parent_at
    · have wrong : child = parent := child_at.1.symm.trans at_parent
      have seam : S.edge ⟨parent, nonroot⟩ = s :=
        (congrArg S.edge (Subtype.ext wrong)).symm.trans named
      exact (outgoing_cut (seam.symm ▸ kept.1)).elim
    · exact parent_at.1.symm.trans at_parent
  let data := C.contourParentInterval S Q roots starts child fresh
  let u := Q.cycle.point data.enter
  let v := C.boundaryTurn Retain (Q.cycle.point data.leave)
  have crossing : C.GermCrosses large p q := ⟨s, kept.1, side, b, rfl, rfl⟩
  have canonical : C.GermCrosses large u.val v.val :=
    C.contourChild_parent_germ_crosses S Q roots starts child fresh in_large
  have u_edge : C.germEdge u.val = C.seamSide s data.side :=
    (congrArg Subtype.val data.entry_named).trans (congrArg (C.seamSide · data.side) s_eq.symm)
  have v_edge : C.germEdge v.val = C.seamSide s (!data.side) := by
    have reverse := C.edgeReverseGerm_edge (Q.cycle.point data.leave).val
    exact reverse.trans ((congrArg Subtype.val data.exit_named).trans
      (congrArg (C.seamSide · (!data.side)) s_eq.symm))
  obtain ⟨root_entry, first⟩ := C.contourParentInterval_entry_original S Q roots starts child fresh
  obtain ⟨last, root_exit⟩ := C.contourParentInterval_exit_original S Q roots starts child fresh
  have child_ne : child ≠ P.parent child :=
    fun eq => (ne_of_lt (P.ascending child fresh)) (congrArg P.height eq)
  have u_original : C.vertexOfCorner Set.univ u.val.1 = P.parent child := root_entry
  have v_original : C.vertexOfCorner Set.univ v.val.1 = P.parent child := root_exit
  have u_distinct : C.vertexOfCorner Set.univ (C.edgeReverseGerm u.val).1 ≠
      C.vertexOfCorner Set.univ u.val.1 := by
    change C.vertexOfCorner Set.univ (C.boundaryTurn Retain u).val.1 ≠ _
    exact fun eq => child_ne (first.symm.trans (eq.trans u_original))
  have v_distinct : C.vertexOfCorner Set.univ (C.edgeReverseGerm v.val).1 ≠
      C.vertexOfCorner Set.univ v.val.1 := by
    have itself : C.boundaryTurn Retain v = Q.cycle.point data.leave :=
      C.boundaryTurn_involutive Retain _
    change C.vertexOfCorner Set.univ (C.boundaryTurn Retain v).val.1 ≠ _
    exact fun eq => child_ne (last.symm.trans
      ((congrArg Orig itself).symm.trans (eq.trans v_original)))
  have actual : C.vertexOfCorner Set.univ p.1 = P.parent child :=
    at_parent.trans p_at.symm
  have v_copy : C.boundaryEndVertex Retain v =
      C.boundaryEndVertex Retain (Q.cycle.point (finRotate (Q.length + 1) data.leave)) :=
    congrArg Subtype.val (C.boundaryCycle_next_vertex Retain Q.cycle Q.closes data.leave)
  refine ⟨child, fresh, p_at, in_large, ?_⟩
  have flags : side = data.side ∨ side = !data.side := by
    cases side <;> cases data.side <;> simp
  rcases flags with positive | negative
  · have pe : p = u.val := germ_eq_of_original_endpoint C _ _
      ((C.germEdge_germOfEndpoint _ _).trans ((congrArg (C.seamSide s) positive).trans u_edge.symm))
      (actual.trans u_original.symm) u_distinct
    have qe : q = v.val := GermCrosses.unique C (pe ▸ crossing) canonical
    exact Or.inl ⟨hx.trans (congrArg (fun g : C.Germ => C.vertexOfCorner Retain g.1) pe),
      hy.trans ((congrArg (fun g : C.Germ => C.vertexOfCorner Retain g.1) qe).trans v_copy)⟩
  · have pe : p = v.val := germ_eq_of_original_endpoint C _ _
      ((C.germEdge_germOfEndpoint _ _).trans ((congrArg (C.seamSide s) negative).trans v_edge.symm))
      (actual.trans v_original.symm) v_distinct
    have qe : q = u.val := GermCrosses.unique C (pe ▸ crossing) canonical.symm
    exact Or.inr ⟨hx.trans ((congrArg (fun g : C.Germ => C.vertexOfCorner Retain g.1) pe).trans
      v_copy), hy.trans (congrArg (fun g : C.Germ => C.vertexOfCorner Retain g.1) qe)⟩

end Unfoldings.TriangleComplex
