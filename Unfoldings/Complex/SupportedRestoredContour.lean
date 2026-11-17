module

public import Unfoldings.Complex.SupportedSubtreeContour
public import Unfoldings.Complex.PrunedContourStep

/-! Restored original contour excursions preserve actual successors with unused roots. -/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialFolding

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (F : SpatialFolding C)
  {P : AscendingParents (C.Vertex Set.univ)} (S : P.EdgeSelection C.seamGraph)
  (boundary_roots : C.relativeCutRoots Set.univ ⊆ P.roots)
  (Q : C.BoundaryContour (C.selectedRetain S))
  {retain : Set C.Seam} (inclusion : C.selectedRetain S ⊆ retain)

include F boundary_roots in
/-- An original contour excursion with equal original endpoint labels closes in the actual
restored cut whenever none of its banks survives. Original positive curvature is allowed;
no development, flatness or endpoint-matching certificate in the current cut is assumed. -/
theorem restored_contour_excursion_endpoints_eq_of_boundary_roots (region : Fin (Q.length + 1) →
  Prop)
    (a b : Fin (Q.length + 1)) (different : a ≠ b)
    (enters : ¬ region a ∧ region (finRotate (Q.length + 1) a))
    (leaves : region b ∧ ¬ region (finRotate (Q.length + 1) b))
    (stable : ∀ i, i ≠ a → i ≠ b →
      (region (finRotate (Q.length + 1) i) ↔ region i))
    (same_original : C.vertexForgetCuts (Set.subset_univ _)
        (C.boundaryEndVertex (C.selectedRetain S)
          (Q.cycle.point (finRotate (Q.length + 1) a))) =
      C.vertexForgetCuts (Set.subset_univ _)
        (C.boundaryEndVertex (C.selectedRetain S)
          (Q.cycle.point (finRotate (Q.length + 1) b))))
    (restored : ∀ i, region i →
      ¬ C.IsBoundaryEdge retain (C.germEdge (Q.cycle.point i).val)) :
    C.vertexForgetCuts inclusion (C.boundaryEndVertex (C.selectedRetain S)
        (Q.cycle.point (finRotate (Q.length + 1) b))) =
      C.vertexForgetCuts inclusion (C.boundaryEndVertex (C.selectedRetain S)
        (Q.cycle.point (finRotate (Q.length + 1) a))) := by
  classical
  let next := finRotate (Q.length + 1)
  let vertex (i : Fin (Q.length + 1)) := C.vertexForgetCuts inclusion
    (C.boundaryEndVertex (C.selectedRetain S) (Q.cycle.point i))
  let position (i : Fin (Q.length + 1)) : ℤ := if vertex i = vertex (next a) then 1 else 0
  let weight (i : Fin (Q.length + 1)) : ℤ :=
    if region i then position (next i) - position i else 0
  choose enter leave distinct entry_data exit_data unchanged using
    (fun e : {w : C.Vertex Set.univ // w ∉ P.roots} =>
      C.exists_oriented_subtree_exits_of_boundary_roots S boundary_roots Q.cycle Q.closes
        Q.covers e.val e.property)
  choose side first_named last_named using
    (fun e : {w : C.Vertex Set.univ // w ∉ P.roots} =>
      C.opposite_parent_banks_of_exits_of_boundary_roots S boundary_roots Q e.val e.property
        (enter e) (leave e) (distinct e) (entry_data e) (exit_data e))
  have pair_membership (e : {w : C.Vertex Set.univ // w ∉ P.roots}) :
      region (enter e) ↔ region (leave e) := by
    apply cyclic_region_crossings_paired next region (C.SubtreeBoundaryInside S Q.cycle e.val)
      a b (enter e) (leave e) different (distinct e) enters leaves stable
      (entry_data e) (exit_data e) (unchanged e)
    change P.Ancestor _ e.val ↔ P.Ancestor _ e.val
    rw [same_original]
  have old_zero (i : Fin (Q.length + 1))
      (old : C.IsBoundaryEdge Set.univ
        (C.boundaryEndEquiv (C.selectedRetain S) (Q.cycle.point i)).1.val) : weight i = 0 := by
    apply ite_eq_right
    intro member
    exact restored i member (C.isBoundaryEdge_antitone (Set.subset_univ retain) old)
  have next_vertex (i : Fin (Q.length + 1)) :
      C.boundaryEndVertex (C.selectedRetain S)
        (C.boundaryTurn (C.selectedRetain S) (Q.cycle.point i)) =
      C.boundaryEndVertex (C.selectedRetain S) (Q.cycle.point (next i)) :=
    congrArg Subtype.val (C.boundaryCycle_next_vertex (C.selectedRetain S) Q.cycle Q.closes i)
  have turn_bank (i : Fin (Q.length + 1)) :
      (C.boundaryEndEquiv (C.selectedRetain S)
        (C.boundaryTurn (C.selectedRetain S) (Q.cycle.point i))).1 =
      (C.boundaryEndEquiv (C.selectedRetain S) (Q.cycle.point i)).1 := by
    simp only [TriangleComplex.boundaryTurn, Equiv.apply_symm_apply]
  have paired (e : {w : C.Vertex Set.univ // w ∉ P.roots}) :
      weight (enter e) + weight (leave e) = 0 := by
    dsimp only [weight]
    rw [← pair_membership e]
    by_cases selected : region (enter e)
    · simp only [selected, ite_true]
      have kept : S.edge e ∈ retain := by
        by_contra cut
        apply restored (enter e) selected
        have raw := congrArg
          (fun bank : C.BoundaryBank (C.selectedRetain S) => bank.val) (first_named e)
        change C.germEdge (Q.cycle.point (enter e)).val = C.seamSide (S.edge e) (side e) at raw
        rw [raw]
        cases side e
        · exact (C.isBoundaryEdge_left_iff retain _).mpr cut
        · exact (C.isBoundaryEdge_right_iff retain _).mpr cut
      have entry := C.selected_parent_bank_enters S e.val e.property (Q.cycle.point (enter e))
        (side e) (first_named e) (entry_data e).1
      have exit := C.selected_parent_bank_leaves S e.val e.property (Q.cycle.point (leave e))
        (!(side e)) (last_named e) (exit_data e).1
      have child : vertex (next (enter e)) = vertex (leave e) := by
        dsimp only [vertex]
        rw [← next_vertex]
        exact F.boundary_end_forgetCuts_eq_of_restored_seam inclusion
          (C.selectedParentCut S e.val e.property) kept _ _ (side e)
          ((turn_bank _).trans (first_named e)) (last_named e) (entry.2.trans exit.1.symm)
      have parent : vertex (next (leave e)) = vertex (enter e) := by
        dsimp only [vertex]
        rw [← next_vertex]
        apply F.boundary_end_forgetCuts_eq_of_restored_seam inclusion
          (C.selectedParentCut S e.val e.property) kept _ _ (!(side e))
        · exact (turn_bank _).trans (last_named e)
        · simpa only [Bool.not_not] using first_named e
        · exact exit.2.trans entry.1.symm
      simp only [position, child, parent]
      abel
    · simp only [selected, ite_false, add_zero]
  have sum := C.sum_selected_bank_weights S Q.cycle Q.covers weight old_zero
    enter leave side first_named last_named
  simp only [paired, Finset.sum_const_zero] at sum
  have cancellation := displacement_of_two_region_exits next region position a b different
    enters leaves stable
  have equal : position (next b) = position (next a) :=
    sub_eq_zero.mp (cancellation.symm.trans sum)
  change vertex (next b) = vertex (next a)
  by_contra different
  simp only [position, different, ite_false, ite_true] at equal
  norm_num at equal


include F boundary_roots inclusion in
/-- After deleting a restored excursion, the two surviving banks are adjacent in the actual
current cut boundary. Their meeting is derived intrinsically; no current endpoint equality
or successor premise is assumed. -/
theorem pruned_contour_boundary_step_of_boundary_roots (region : Fin (Q.length + 1) → Prop)
    (a b : Fin (Q.length + 1)) (different : a ≠ b)
    (enters : ¬ region a ∧ region (finRotate (Q.length + 1) a))
    (leaves : region b ∧ ¬ region (finRotate (Q.length + 1) b))
    (stable : ∀ i, i ≠ a → i ≠ b →
      (region (finRotate (Q.length + 1) i) ↔ region i))
    (same_original : C.vertexForgetCuts (Set.subset_univ _)
        (C.boundaryEndVertex (C.selectedRetain S)
          (Q.cycle.point (finRotate (Q.length + 1) a))) =
      C.vertexForgetCuts (Set.subset_univ _)
        (C.boundaryEndVertex (C.selectedRetain S)
          (Q.cycle.point (finRotate (Q.length + 1) b))))
    (restored : ∀ i, region i →
      ¬ C.IsBoundaryEdge retain (C.germEdge (Q.cycle.point i).val))
    (incoming : C.IsBoundaryEdge retain (C.germEdge (Q.cycle.point a).val))
    (outgoing : C.IsBoundaryEdge retain
      (C.germEdge (Q.cycle.point (finRotate (Q.length + 1) b)).val)) :
    C.boundaryMate retain
        (C.boundaryTurn retain (C.survivingBoundaryEnd (Q.cycle.point a) incoming)) =
      C.survivingBoundaryEnd (Q.cycle.point (finRotate (Q.length + 1) b)) outgoing := by
  have equal := F.restored_contour_excursion_endpoints_eq_of_boundary_roots S boundary_roots Q
    inclusion region a b
    different enters leaves stable same_original restored
  let p := C.boundaryTurn retain (C.survivingBoundaryEnd (Q.cycle.point a) incoming)
  let q := C.survivingBoundaryEnd (Q.cycle.point (finRotate (Q.length + 1) b)) outgoing
  have next := congrArg Subtype.val
    (C.boundaryCycle_next_vertex (C.selectedRetain S) Q.cycle Q.closes a)
  change C.boundaryEndVertex (C.selectedRetain S)
    (C.boundaryTurn (C.selectedRetain S) (Q.cycle.point a)) =
    C.boundaryEndVertex (C.selectedRetain S)
      (Q.cycle.point (finRotate (Q.length + 1) a)) at next
  have same : C.boundaryEndVertex retain q = C.boundaryEndVertex retain p := by
    change C.vertexForgetCuts inclusion
      (C.boundaryEndVertex (C.selectedRetain S)
        (Q.cycle.point (finRotate (Q.length + 1) b))) =
      C.vertexForgetCuts inclusion
        (C.boundaryEndVertex (C.selectedRetain S)
          (C.boundaryTurn (C.selectedRetain S) (Q.cycle.point a)))
    rw [next]
    exact equal
  have distinct : q ≠ p := by
    intro same_end
    apply Q.cycle.disjoint (finRotate (Q.length + 1) b) a
    apply Subtype.ext
    exact congrArg (fun e : C.BoundaryEnd retain => e.val) same_end
  exact ((C.exists_unique_other_boundaryEnd retain p).unique ⟨distinct, same⟩
    (C.boundaryMate_spec retain p)).symm


end Unfoldings.SpatialFolding
