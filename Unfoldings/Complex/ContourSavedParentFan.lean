module

public import Unfoldings.Complex.ContourRestoredChildSeams

/-! The actual saved outgoing fan is a suffix of the final contour's parent copies. -/

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
local notation "Visit[" j "]" => C.contourOriginalVertex S Q j
local notation "Copy[" j "]" => C.boundaryEndVertex Retain (Q.cycle.point j)
local notation "Interval[" v "," h "]" => C.contourParentInterval S Q roots starts v h
local notation "Stage[" i "]" => C.processedParentRetain S (C.contourFrontier S Q i)

/-- The original seam of a nonroot is still retained through its first visit. -/
theorem contour_parent_seam_retained_iff (w : C.Vertex Set.univ) (nonroot : w ∉ P.roots)
    (stage : Fin (Q.length + 1)) :
    S.edge ⟨w, nonroot⟩ ∈ Stage[stage] ↔ stage.val ≤ (Interval[w,nonroot]).enter.val + 1 := by
  have retained : S.edge ⟨w, nonroot⟩ ∈ Stage[stage] ↔
      w ∉ (C.contourFrontier S Q stage).processed := by
    constructor
    · exact fun cut processed => cut ⟨w, nonroot⟩ processed rfl
    · intro fresh e processed eq
      have same : e = ⟨w, nonroot⟩ := S.edge_injective eq
      exact fresh (Eq.mp (congrArg (fun x : {v : C.Vertex Set.univ // v ∉ P.roots} =>
        x.val ∈ (C.contourFrontier S Q stage).processed) same) processed)
  rw [retained, C.mem_contourFrontier_processed_iff_enter S Q roots starts w nonroot stage]
  exact not_lt

-- The rightmost original visit is the parent's literal rootward exit bank.
private theorem contour_visit_le_exit (parent : C.Vertex Set.univ) (nonroot : parent ∉ P.roots)
    (i : Fin (Q.length + 1)) (visit : Visit[i] = parent) :
    i.val ≤ (Interval[parent,nonroot]).leave.val :=
  (((Interval[parent,nonroot]).subtree i).mp (visit.symm ▸ P.ancestor_refl parent)).2

/-- Once its outgoing seam is cut, the saved outgoing fan of a nonroot is precisely
the final parent copies after the processed child excursions. -/
theorem contourSavedParentFan_forget_eq_iff
    (parent : C.Vertex Set.univ) (nonroot : parent ∉ P.roots)
    (stage : Fin (Q.length + 1))
    (cut : S.edge ⟨parent, nonroot⟩ ∉ Stage[stage]) (i : Fin (Q.length + 1)) :
    let exit := (Interval[parent,nonroot]).leave
    let inc := C.selectedRetain_subset_processed S (C.contourFrontier S Q stage)
    C.vertexForgetCuts inc Copy[i] = C.vertexForgetCuts inc Copy[exit] ↔
      Visit[i] = parent ∧ (i = exit ∨ stage.val ≤ i.val + 1) := by
  classical
  let exit := (Interval[parent,nonroot]).leave
  let inc := C.selectedRetain_subset_processed S (C.contourFrontier S Q stage)
  let original := C.vertexForgetCuts (Set.subset_univ Retain)
  have exit_at : Visit[exit] = parent :=
    (C.contourParentInterval_exit_original S Q roots starts parent nonroot).1
  let Valid (v : C.Vertex Retain) := ∃ j : Fin (Q.length + 1), v = Copy[j] ∧
    Visit[j] = parent ∧ (j = exit ∨ stage.val ≤ j.val + 1)
  have advance {x y : C.Vertex Retain}
      (step : C.RestoredVertexSeam Retain Stage[stage] x y) (ok : Valid x) : Valid y := by
    obtain ⟨j, exact_copy, at_parent, _⟩ := ok
    have orig : original x = parent := (congrArg original exact_copy).trans at_parent
    obtain ⟨child, fresh, parent_eq, retained, names⟩ :=
      C.exists_child_of_restoredVertexSeam S Q roots starts parent nonroot cut x y orig step
    let old := Interval[child,fresh]
    let back := finRotate (Q.length + 1) old.leave
    obtain ⟨returned, at_left, at_right, _⟩ :=
      C.contourChild_consecutive_parent_visits S Q roots starts child fresh (parent_eq.symm ▸ nonroot)
    have threshold : stage.val ≤ old.enter.val + 1 :=
      (C.contour_parent_seam_retained_iff S Q roots starts child fresh stage).mp retained
    have later : old.enter.val + 1 ≤ back.val := by
      change back.val = old.leave.val + 1 at returned
      have ordered := old.ordered
      omega
    rcases names with exit_edge | entry_edge
    · exact ⟨back, exit_edge.2, at_right.trans parent_eq, Or.inr (threshold.trans (later.trans (Nat.le_succ _)))⟩
    · exact ⟨old.enter, entry_edge.2, at_left.trans parent_eq, Or.inr threshold⟩
  have closed {x y : C.Vertex Retain}
      (chain : Relation.EqvGen (C.RestoredVertexSeam Retain Stage[stage]) x y) :
      Valid x ↔ Valid y := by
    induction chain with
    | rel _ _ step => exact ⟨advance step, advance (RestoredVertexSeam.symm C step)⟩
    | refl => rfl
    | symm _ _ _ ih => exact ih.symm
    | trans _ _ _ _ _ left right => exact left.trans right
  constructor
  · intro equal
    have chain := (C.vertexForgetCuts_eq_iff_restoredVertexSeams inc Copy[i] Copy[exit]).mp equal
    obtain ⟨j, copy, original_eq, bound⟩ := (closed chain).mpr ⟨exit, rfl, exit_at, Or.inl rfl⟩
    have same : i = j := C.boundaryCycle_vertices_injective Retain Q.cycle Q.closes copy
    exact same.symm ▸ ⟨original_eq, bound⟩
  · rintro ⟨visit, at_exit | active⟩
    · exact congrArg (fun j => C.vertexForgetCuts inc Copy[j]) at_exit
    · have reaches (j : Fin (Q.length + 1)) (here : Visit[j] = parent)
          (later : stage.val ≤ j.val + 1) :
          C.vertexForgetCuts inc Copy[j] = C.vertexForgetCuts inc Copy[exit] := by
        suffices all : ∀ n : ℕ, ∀ k : Fin (Q.length + 1), exit.val - k.val = n →
          Visit[k] = parent → stage.val ≤ k.val + 1 →
          C.vertexForgetCuts inc Copy[k] = C.vertexForgetCuts inc Copy[exit] from
            all _ j rfl here later
        intro n
        induction n using Nat.strong_induction_on with
        | h n ih =>
          intro k measure visit cutoff
          have before : k.val ≤ exit.val := contour_visit_le_exit C S Q roots starts
            parent nonroot k visit
          by_cases same : k = exit
          · exact congrArg (fun t => C.vertexForgetCuts inc Copy[t]) same
          · have different : k.val < exit.val :=
              before.lt_of_ne (fun h => same (Fin.ext h))
            let options := Finset.univ.filter (fun t : Fin (Q.length + 1) =>
              k.val < t.val ∧ Visit[t] = parent)
            have present : exit ∈ options := Finset.mem_filter.mpr
              ⟨Finset.mem_univ _, different, exit_at⟩
            let next := options.min' ⟨exit, present⟩
            have next_mem : next ∈ options := Finset.min'_mem _ _
            have next_pred : k.val < next.val ∧ Visit[next] = parent :=
              (Finset.mem_filter.mp next_mem).2
            have cross : ∀ t : Fin (Q.length + 1), k.val < t.val → t.val < next.val →
                Visit[t] ≠ parent := by
              intro t after before equal
              have t_mem : t ∈ options := Finset.mem_filter.mpr ⟨Finset.mem_univ _, after, equal⟩
              exact (not_lt_of_ge (options.min'_le t t_mem)) before
            obtain ⟨child, fresh, _, entrance, return_at⟩ :=
              C.exists_child_of_consecutive_contour_visits S Q roots starts parent nonroot
                k next next_pred.1 visit next_pred.2 cross
            have kept : S.edge ⟨child, fresh⟩ ∈ Stage[stage] :=
              (C.contour_parent_seam_retained_iff S Q roots starts child fresh stage).mpr
                (entrance.symm ▸ cutoff)
            have link : C.RestoredVertexSeam Retain Stage[stage] Copy[k] Copy[next] :=
              entrance ▸ return_at ▸ C.contourChild_restored_parent_seam S Q roots starts child
                fresh kept
            have joined := (C.vertexForgetCuts_eq_iff_restoredVertexSeams inc _ _).mpr
              (Relation.EqvGen.rel _ _ link)
            have decrease : exit.val - next.val < n := by
              have step := next_pred.1
              have le_exit := contour_visit_le_exit C S Q roots starts parent nonroot
                next next_pred.2
              omega
            exact joined.trans (ih _ decrease next rfl next_pred.2
              (cutoff.trans (Nat.add_le_add_right next_pred.1.le _)))
      exact reaches i visit active

end Unfoldings.TriangleComplex
