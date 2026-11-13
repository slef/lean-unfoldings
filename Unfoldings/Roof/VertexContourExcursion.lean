module

public import Unfoldings.Roof.BranchDisplacements
public import Unfoldings.Topology.CyclicRegionPairing
public import Unfoldings.Roof.RootSubtreeContour

/-! Exact displacement for a partial contour excursion between copies of one original vertex. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof.SectorForest

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexRoof C} {t : ℝ} {origin : Plane} (M : K.SectorForest t origin)
  (D : FacewiseDevelopment C M.retain)

/-- An actual oriented portion of the contour inside a descendant subtree.
Its endpoints are copies of the top vertex, which may lie on the original rim. -/
structure VertexContourExcursion
    (e : C.Vertex Set.univ) where
  region : Fin (M.projectionContour.length + 1) → Prop
  first : Fin (M.projectionContour.length + 1)
  last : Fin (M.projectionContour.length + 1)
  different : first ≠ last
  enters : ¬ region first ∧ region (finRotate (M.projectionContour.length + 1) first)
  leaves : region last ∧ ¬ region (finRotate (M.projectionContour.length + 1) last)
  stable : ∀ i, i ≠ first → i ≠ last →
    (region (finRotate (M.projectionContour.length + 1) i) ↔ region i)
  inside : ∀ i, region i →
    C.SubtreeBoundaryInside M.selection M.projectionContour.cycle e i
  first_vertex :
    C.vertexForgetCuts (Set.subset_univ _) (C.boundaryEndVertex M.retain
      (M.projectionContour.cycle.point (finRotate (M.projectionContour.length + 1) first))) = e
  last_vertex :
    C.vertexForgetCuts (Set.subset_univ _) (C.boundaryEndVertex M.retain
      (M.projectionContour.cycle.point (finRotate (M.projectionContour.length + 1) last))) = e

namespace VertexContourExcursion

variable {M}
  {e : C.Vertex Set.univ}
  (E : M.VertexContourExcursion e)

/-- No original rim bank occurs inside an excursion returning to its top vertex. -/
theorem no_original_bank (i : Fin (M.projectionContour.length + 1)) (member : E.region i) :
    ¬ C.IsBoundaryEdge Set.univ
      (C.boundaryEndEquiv M.retain (M.projectionContour.cycle.point i)).1.val := by
  intro old
  let p := M.projectionContour.cycle.point i
  let q : C.BoundaryEnd Set.univ := ⟨p.val, old⟩
  let next := finRotate (M.projectionContour.length + 1)
  let original (j : Fin (M.projectionContour.length + 1)) :=
    C.vertexForgetCuts (Set.subset_univ M.retain)
      (C.boundaryEndVertex M.retain (M.projectionContour.cycle.point j))
  have start : original i = C.boundaryEndVertex Set.univ q := rfl
  have after : original (next i) =
      C.boundaryEndVertex Set.univ (C.boundaryTurn Set.univ q) := by
    have step := congrArg Subtype.val (C.boundaryCycle_next_vertex M.retain
      M.projectionContour.cycle M.projectionContour.closes i)
    change C.boundaryEndVertex M.retain (C.boundaryTurn M.retain p) =
      C.boundaryEndVertex M.retain (M.projectionContour.cycle.point (next i)) at step
    change C.vertexForgetCuts (Set.subset_univ M.retain)
      (C.boundaryEndVertex M.retain (M.projectionContour.cycle.point (next i))) = _
    rw [← step]
    rfl
  have first_root : original i ∈ M.parents.roots :=
    start ▸ (M.roots_eq.symm ▸ (C.boundaryEndAsVertex Set.univ q).property)
  have last_root : original (next i) ∈ M.parents.roots :=
    after ▸ (M.roots_eq.symm ▸
      (C.boundaryEndAsVertex Set.univ (C.boundaryTurn Set.univ q)).property)
  have at_top : original i = e :=
    (M.root_descendant_iff first_root).mp (E.inside i member)
  have next_at_top : original (next i) = e := by
    by_cases last : i = E.last
    · subst i
      exact E.last_vertex
    · have not_first : i ≠ E.first := fun equal => E.enters.1 (equal ▸ member)
      exact (M.root_descendant_iff last_root).mp
        (E.inside _ ((E.stable i not_first last).mpr member))
  apply K.folding.boundaryEndVertex_ne_turn Set.univ q
  exact start.symm.trans (at_top.trans (next_at_top.symm.trans after))

/-- Every original selected seam occurs with both named banks, or with neither. -/
theorem selected_pair (v : {w : C.Vertex Set.univ // w ∉ M.parents.roots}) :
    E.region (M.parentBankOpening D v).enter ↔ E.region (M.parentBankOpening D v).leave := by
  let O := M.parentBankOpening D v
  apply cyclic_region_crossings_paired (finRotate (M.projectionContour.length + 1)) E.region
    (C.SubtreeBoundaryInside M.selection M.projectionContour.cycle v.val)
    E.first E.last O.enter O.leave E.different O.enter_ne_leave E.enters E.leaves E.stable
    O.enters O.leaves O.stable
  change M.parents.Ancestor (C.vertexForgetCuts (Set.subset_univ _)
      (C.boundaryEndVertex M.retain
        (M.projectionContour.cycle.point (finRotate (M.projectionContour.length + 1) E.first))))
        v.val ↔
    M.parents.Ancestor (C.vertexForgetCuts (Set.subset_univ _)
      (C.boundaryEndVertex M.retain
        (M.projectionContour.cycle.point (finRotate (M.projectionContour.length + 1) E.last))))
        v.val
  rw [E.first_vertex, E.last_vertex]

theorem selected_descendant
    (v : {w : C.Vertex Set.univ // w ∉ M.parents.roots})
    (selected : E.region (M.parentBankOpening D v).enter) :
    M.parents.Ancestor v.val e := by
  have member := E.inside _ ((E.selected_pair D v).mp selected)
  change M.parents.Ancestor (C.vertexForgetCuts (Set.subset_univ _)
    (C.boundaryEndVertex M.retain
      (M.projectionContour.cycle.point (M.parentBankOpening D v).leave))) e at member
  rwa [(M.parentBankOpening D v).exit_vertex] at member

open scoped Classical in
/-- A partial excursion contains entire sibling openings, with their actual developed vectors. -/
theorem displacement :
    D.boundaryPosition (M.projectionContour.cycle.point
        (finRotate (M.projectionContour.length + 1) E.last)) -
      D.boundaryPosition (M.projectionContour.cycle.point
        (finRotate (M.projectionContour.length + 1) E.first)) =
      ∑ v : {w : C.Vertex Set.univ // w ∉ M.parents.roots},
        if E.region (M.parentBankOpening D v).enter then
          M.parentExitVector D v - M.parentEntryVector D v else 0 := by
  classical
  let weight (i : Fin (M.projectionContour.length + 1)) : Plane :=
    if E.region i then D.boundaryRay (M.projectionContour.cycle.point i) else 0
  have old_zero (i : Fin (M.projectionContour.length + 1))
      (old : C.IsBoundaryEdge Set.univ
        (C.boundaryEndEquiv M.retain (M.projectionContour.cycle.point i)).1.val) :
      weight i = 0 := by
    apply ite_eq_right
    intro member
    exact E.no_original_bank i member old
  have paired (v : {w : C.Vertex Set.univ // w ∉ M.parents.roots}) :
      weight (M.parentBankOpening D v).enter + weight (M.parentBankOpening D v).leave =
        if E.region (M.parentBankOpening D v).enter then
          M.parentExitVector D v - M.parentEntryVector D v else 0 := by
    simp only [weight]
    rw [← E.selected_pair D v, (M.parentBankOpening D v).entrance_ray,
      (M.parentBankOpening D v).exit_ray]
    simp only [parentEntryVector, parentExitVector]
    split_ifs <;> abel
  have sum := C.sum_selected_bank_weights M.selection M.projectionContour.cycle
    M.projectionContour.covers weight old_zero
    (fun v => (M.parentBankOpening D v).enter) (fun v => (M.parentBankOpening D v).leave)
    (fun v => (M.parentBankOpening D v).side)
    (fun v => (M.parentBankOpening D v).first_named)
    (fun v => (M.parentBankOpening D v).last_named)
  simp_rw [paired] at sum
  have cancellation := displacement_of_two_region_exits
    (finRotate (M.projectionContour.length + 1)) E.region
    (fun i => D.boundaryPosition (M.projectionContour.cycle.point i)) E.first E.last E.different
    E.enters E.leaves E.stable
  have total : (∑ i, weight i) =
      D.boundaryPosition (M.projectionContour.cycle.point
        (finRotate (M.projectionContour.length + 1) E.last)) -
      D.boundaryPosition (M.projectionContour.cycle.point
        (finRotate (M.projectionContour.length + 1) E.first)) := by
    simpa only [weight, D.boundaryRay_eq_cycle_displacement M.projectionContour.cycle
      M.projectionContour.closes] using cancellation
  exact total.symm.trans sum

end VertexContourExcursion
end Unfoldings.ConvexRoof.SectorForest
