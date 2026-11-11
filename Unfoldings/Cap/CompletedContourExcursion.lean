module

public import Unfoldings.Cap.CompletedBranchDisplacements
public import Unfoldings.Topology.CyclicRegionPairing

/-! Exact displacement for a partial contour excursion between copies of one original vertex. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap.RadialCutForest

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexCap C} {source : Plane} {cuts : Set Plane} (N : K.RadialCutForest source cuts)
  (D : FacewiseDevelopment C N.completedRetain)

/-- An actual oriented portion of the contour, inside a nonroot descendant subtree.
Its endpoint copies lie above the same original vertex. -/
structure ContourExcursion
    (e : {v : C.Vertex Set.univ // v ∉ N.spanningCompletion.parents.roots}) where
  region : Fin (N.completedContour.length + 1) → Prop
  first : Fin (N.completedContour.length + 1)
  last : Fin (N.completedContour.length + 1)
  different : first ≠ last
  enters : ¬ region first ∧ region (finRotate (N.completedContour.length + 1) first)
  leaves : region last ∧ ¬ region (finRotate (N.completedContour.length + 1) last)
  stable : ∀ i, i ≠ first → i ≠ last →
    (region (finRotate (N.completedContour.length + 1) i) ↔ region i)
  inside : ∀ i, region i →
    C.SubtreeBoundaryInside N.spanningCompletion.selection N.completedContour.cycle e.val i
  same_vertex :
    C.vertexForgetCuts (Set.subset_univ _) (C.boundaryEndVertex N.completedRetain
      (N.completedContour.cycle.point (finRotate (N.completedContour.length + 1) first))) =
    C.vertexForgetCuts (Set.subset_univ _) (C.boundaryEndVertex N.completedRetain
      (N.completedContour.cycle.point (finRotate (N.completedContour.length + 1) last)))

namespace ContourExcursion

variable {N}
  {e : {v : C.Vertex Set.univ // v ∉ N.spanningCompletion.parents.roots}}
  (E : N.ContourExcursion e)

/-- Every original selected seam occurs with both named banks, or with neither. -/
theorem selected_pair (v : {w : C.Vertex Set.univ // w ∉ N.spanningCompletion.parents.roots}) :
    E.region (N.parentBankOpening D v).enter ↔ E.region (N.parentBankOpening D v).leave := by
  let O := N.parentBankOpening D v
  apply cyclic_region_crossings_paired (finRotate (N.completedContour.length + 1)) E.region
    (C.SubtreeBoundaryInside N.spanningCompletion.selection N.completedContour.cycle v.val)
    E.first E.last O.enter O.leave E.different O.enter_ne_leave E.enters E.leaves E.stable
    O.enters O.leaves O.stable
  change N.spanningCompletion.parents.Ancestor (C.vertexForgetCuts (Set.subset_univ _)
      (C.boundaryEndVertex N.completedRetain
        (N.completedContour.cycle.point (finRotate (N.completedContour.length + 1) E.first))))
        v.val ↔
    N.spanningCompletion.parents.Ancestor (C.vertexForgetCuts (Set.subset_univ _)
      (C.boundaryEndVertex N.completedRetain
        (N.completedContour.cycle.point (finRotate (N.completedContour.length + 1) E.last))))
        v.val
  rw [E.same_vertex]

theorem selected_descendant
    (v : {w : C.Vertex Set.univ // w ∉ N.spanningCompletion.parents.roots})
    (selected : E.region (N.parentBankOpening D v).enter) :
    N.spanningCompletion.parents.Ancestor v.val e.val := by
  have member := E.inside _ ((E.selected_pair D v).mp selected)
  change N.spanningCompletion.parents.Ancestor (C.vertexForgetCuts (Set.subset_univ _)
    (C.boundaryEndVertex N.completedRetain
      (N.completedContour.cycle.point (N.parentBankOpening D v).leave))) e.val at member
  rwa [(N.parentBankOpening D v).exit_vertex] at member

open scoped Classical in
/-- A partial excursion contains entire sibling openings, with their actual developed vectors. -/
theorem displacement :
    D.boundaryPosition (N.completedContour.cycle.point
        (finRotate (N.completedContour.length + 1) E.last)) -
      D.boundaryPosition (N.completedContour.cycle.point
        (finRotate (N.completedContour.length + 1) E.first)) =
      ∑ v : {w : C.Vertex Set.univ // w ∉ N.spanningCompletion.parents.roots},
        if E.region (N.parentBankOpening D v).enter then
          N.parentExitVector D v - N.parentEntryVector D v else 0 := by
  classical
  let weight (i : Fin (N.completedContour.length + 1)) : Plane :=
    if E.region i then D.boundaryRay (N.completedContour.cycle.point i) else 0
  have old_zero (i : Fin (N.completedContour.length + 1))
      (old : C.IsBoundaryEdge Set.univ
        (C.boundaryEndEquiv N.completedRetain (N.completedContour.cycle.point i)).1.val) :
      weight i = 0 := by
    apply ite_eq_right
    intro member
    exact N.spanningCompletion.parents.descendant_nonroot e.property (E.inside i member)
      (N.original_bank_start_root i old)
  have paired (v : {w : C.Vertex Set.univ // w ∉ N.spanningCompletion.parents.roots}) :
      weight (N.parentBankOpening D v).enter + weight (N.parentBankOpening D v).leave =
        if E.region (N.parentBankOpening D v).enter then
          N.parentExitVector D v - N.parentEntryVector D v else 0 := by
    simp only [weight]
    rw [← E.selected_pair D v, (N.parentBankOpening D v).entrance_ray,
      (N.parentBankOpening D v).exit_ray]
    simp only [parentEntryVector, parentExitVector]
    split_ifs <;> abel
  have sum := C.sum_selected_bank_weights N.spanningCompletion.selection N.completedContour.cycle
    N.completedContour.covers weight old_zero
    (fun v => (N.parentBankOpening D v).enter) (fun v => (N.parentBankOpening D v).leave)
    (fun v => (N.parentBankOpening D v).side)
    (fun v => (N.parentBankOpening D v).first_named)
    (fun v => (N.parentBankOpening D v).last_named)
  simp_rw [paired] at sum
  have cancellation := displacement_of_two_region_exits
    (finRotate (N.completedContour.length + 1)) E.region
    (fun i => D.boundaryPosition (N.completedContour.cycle.point i)) E.first E.last E.different
    E.enters E.leaves E.stable
  have total : (∑ i, weight i) =
      D.boundaryPosition (N.completedContour.cycle.point
        (finRotate (N.completedContour.length + 1) E.last)) -
      D.boundaryPosition (N.completedContour.cycle.point
        (finRotate (N.completedContour.length + 1) E.first)) := by
    simpa only [weight, D.boundaryRay_eq_cycle_displacement N.completedContour.cycle
      N.completedContour.closes] using cancellation
  exact total.symm.trans sum

end ContourExcursion
end Unfoldings.ConvexCap.RadialCutForest
