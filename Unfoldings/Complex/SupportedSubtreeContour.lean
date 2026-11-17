module

public import Unfoldings.Complex.SupportedContourNeighbors
public import Unfoldings.Complex.LinearSubtreeBanks

/-! Depth-first original subtree intervals allow unused isolated roots. -/

@[expose] public section

noncomputable section

namespace Unfoldings.TriangleComplex

universe u v

variable {Face : Type u} [Fintype Face] (C : TriangleComplex.{u, v} Face)
  {P : AscendingParents (C.Vertex Set.univ)} (S : P.EdgeSelection C.seamGraph)
  (boundary_roots : C.relativeCutRoots Set.univ ⊆ P.roots)

include boundary_roots in
/-- The two parent banks are exactly the actual boundary exits of the subtree. -/
theorem subtreeCrossingBank_iff_of_boundary_roots (e : C.Vertex Set.univ) (nonroot : e ∉ P.roots)
    (bank : C.BoundaryBank (C.selectedRetain S)) :
    C.SubtreeCrossingBank S e bank ↔
      ∃ side, bank = C.relativeCutBank (C.selectedRetain S) Set.univ
        (C.selectedParentCut S e nonroot) side := by
  rcases C.relativeBank_cases (C.selectedRetain S) Set.univ bank with old | ⟨s, side, rfl⟩
  · have left_root : C.relativeBoundaryVertex (Set.subset_univ _)
        ((C.boundaryGraph (C.selectedRetain S)).left bank) ∈ P.roots :=
      boundary_roots <| C.relativeBoundaryVertex_old_left (Set.subset_univ _) bank old
    have right_root : C.relativeBoundaryVertex (Set.subset_univ _)
        ((C.boundaryGraph (C.selectedRetain S)).right bank) ∈ P.roots :=
      boundary_roots <| C.relativeBoundaryVertex_old_right (Set.subset_univ _) bank old
    have no_crossing : ¬ C.SubtreeCrossingBank S e bank := by
      rintro (⟨inside, _⟩ | ⟨inside, _⟩)
      · exact P.descendant_nonroot nonroot inside left_root
      · exact P.descendant_nonroot nonroot inside right_root
    have no_parent : ¬ ∃ side, bank = C.relativeCutBank (C.selectedRetain S) Set.univ
        (C.selectedParentCut S e nonroot) side := by
      rintro ⟨side, rfl⟩
      exact C.relativeCutBank_not_old (C.selectedParentCut S e nonroot) side old
    exact iff_of_false no_crossing no_parent
  · have selected := C.selectedCut_to_selection_link S
      (C.relativeCutGraph_bank_link (Set.subset_univ _) s side)
    change C.SubtreeCrossingBank S e
      (C.relativeCutBank (C.selectedRetain S) Set.univ s side) ↔ _
    have crossing := S.crosses_descendants_iff nonroot selected
    change C.SubtreeCrossingBank S e
      (C.relativeCutBank (C.selectedRetain S) Set.univ s side) ↔
        s.val = S.edge ⟨e, nonroot⟩ at crossing
    rw [crossing]
    constructor
    · intro same
      have seams : s = C.selectedParentCut S e nonroot := Subtype.ext same
      exact ⟨side, congrArg (fun r => C.relativeCutBank (C.selectedRetain S) Set.univ r side)
        seams⟩
    · rintro ⟨other, equal⟩
      have seams := congrArg (fun p : C.RelativeCutSeam (C.selectedRetain S) Set.univ × Bool =>
        p.1.val) (C.relativeCutBank_injective (C.selectedRetain S) Set.univ
          (a₁ := (s, side)) (a₂ := (C.selectedParentCut S e nonroot, other)) equal)
      exact seams

/-- These two actual exits retain the two distinct bank labels of the original parent seam. -/
def subtreeCrossingBankEquiv_of_boundary_roots (e : C.Vertex Set.univ) (nonroot : e ∉ P.roots) :
    Bool ≃ {bank : C.BoundaryBank (C.selectedRetain S) // C.SubtreeCrossingBank S e bank} :=
  Equiv.ofBijective (fun side =>
    ⟨C.relativeCutBank (C.selectedRetain S) Set.univ (C.selectedParentCut S e nonroot) side,
      (C.subtreeCrossingBank_iff_of_boundary_roots S boundary_roots e nonroot _).mpr ⟨side,
        rfl⟩⟩) ⟨by
    intro a b equal
    have banks := congrArg Subtype.val equal
    exact congrArg Prod.snd
      (C.relativeCutBank_injective (C.selectedRetain S) Set.univ
        (a₁ := (C.selectedParentCut S e nonroot, a))
        (a₂ := (C.selectedParentCut S e nonroot, b)) banks), by
    intro bank
    obtain ⟨side, same⟩ := (C.subtreeCrossingBank_iff_of_boundary_roots S boundary_roots e
      nonroot bank.val).mp bank.property
    exact ⟨side, Subtype.ext same.symm⟩⟩

include boundary_roots in
theorem card_subtreeCrossingBank_of_boundary_roots (e : C.Vertex Set.univ) (nonroot : e ∉ P.roots) :
    Nat.card {bank : C.BoundaryBank (C.selectedRetain S) //
      C.SubtreeCrossingBank S e bank} = 2 := by
  rw [← Nat.card_congr (C.subtreeCrossingBankEquiv_of_boundary_roots S boundary_roots e nonroot)]
  exact Nat.card_eq_fintype_card


section Cyclic

variable {n : ℕ} (cycle : (C.boundarySystem (C.selectedRetain S)).Chain n)
  (closes : C.boundaryMate (C.selectedRetain S)
    (C.boundaryTurn (C.selectedRetain S) cycle.last) = cycle.first)
  (covers : ∀ p, cycle.Visited p)

/-- The two changes in contour membership are the two distinctly named parent banks. -/
def subtreeBoundaryExitEquiv_of_boundary_roots (e : C.Vertex Set.univ) (nonroot : e ∉ P.roots) :
    Bool ≃ {i : Fin (n + 1) //
      (C.SubtreeBoundaryInside S cycle e i ∧
        ¬ C.SubtreeBoundaryInside S cycle e (finRotate (n + 1) i)) ∨
      (C.SubtreeBoundaryInside S cycle e (finRotate (n + 1) i) ∧
        ¬ C.SubtreeBoundaryInside S cycle e i)} :=
  (C.subtreeCrossingBankEquiv_of_boundary_roots S boundary_roots e nonroot).trans
    (((C.boundaryCycleBankEquiv (C.selectedRetain S) cycle covers).subtypeEquiv
      (fun i => (C.subtree_boundary_change_iff S cycle closes e i).symm)).symm)

include boundary_roots closes covers in
/-- One of those banks enters the subtree and the other leaves it. -/
theorem exists_oriented_subtree_exits_of_boundary_roots (e : C.Vertex Set.univ) (nonroot : e ∉
  P.roots) :
    ∃ enter leave : Fin (n + 1), enter ≠ leave ∧
      (¬ C.SubtreeBoundaryInside S cycle e enter ∧
        C.SubtreeBoundaryInside S cycle e (finRotate (n + 1) enter)) ∧
      (C.SubtreeBoundaryInside S cycle e leave ∧
        ¬ C.SubtreeBoundaryInside S cycle e (finRotate (n + 1) leave)) ∧
      ∀ i, i ≠ enter → i ≠ leave →
        (C.SubtreeBoundaryInside S cycle e (finRotate (n + 1) i) ↔
          C.SubtreeBoundaryInside S cycle e i) := by
  classical
  let exits := C.subtreeBoundaryExitEquiv_of_boundary_roots S boundary_roots cycle closes covers
    e nonroot
  let a := (exits false).val
  let b := (exits true).val
  have different : a ≠ b := by
    intro same
    have flags : false = true := exits.injective (Subtype.ext same)
    cases flags
  apply exists_oriented_two_exits (finRotate (n + 1))
    (C.SubtreeBoundaryInside S cycle e) a b different
  intro i
  constructor
  · intro changes
    obtain ⟨side, same⟩ := exits.surjective ⟨i, changes⟩
    cases side
    · exact Or.inl (congrArg Subtype.val same).symm
    · exact Or.inr (congrArg Subtype.val same).symm
  · rintro (rfl | rfl)
    · exact (exits false).property
    · exact (exits true).property


end Cyclic

variable (Q : C.BoundaryContour (C.selectedRetain S))
  (starts : C.contourOriginalVertex S Q 0 ∈ P.roots)

include boundary_roots starts in
/-- Each nonroot subtree occupies one ordinary contiguous interval in the actual contour.
The order is derived from original parent banks and the original rim starting point. -/
theorem exists_linear_subtree_contour_interval_of_boundary_roots (vertex : C.Vertex Set.univ)
    (nonroot : vertex ∉ P.roots) :
    ∃ enter leave : Fin (Q.length + 1), enter.val < leave.val ∧
      ∀ i, P.Ancestor (C.contourOriginalVertex S Q i) vertex ↔
        enter.val < i.val ∧ i.val ≤ leave.val := by
  obtain ⟨enter, leave, _distinct, enters, leaves, stable⟩ :=
    C.exists_oriented_subtree_exits_of_boundary_roots S boundary_roots Q.cycle Q.closes Q.covers
      vertex nonroot
  have outside : ¬ C.SubtreeBoundaryInside S Q.cycle vertex 0 :=
    fun member => P.descendant_nonroot nonroot member starts
  obtain ⟨ordered, interval⟩ := finRotate_two_exits_linear_interval
    (C.SubtreeBoundaryInside S Q.cycle vertex) enter leave enters leaves stable outside
  exact ⟨enter, leave, ordered, interval⟩

include boundary_roots starts in
/-- An original descendant subtree cannot be left and then revisited in this processing order. -/
theorem contour_subtree_no_reentry_of_boundary_roots (vertex : C.Vertex Set.univ) (nonroot :
  vertex ∉ P.roots)
    (first middle last : Fin (Q.length + 1)) (before : first.val ≤ middle.val)
    (after : middle.val ≤ last.val)
    (first_inside : P.Ancestor (C.contourOriginalVertex S Q first) vertex)
    (last_inside : P.Ancestor (C.contourOriginalVertex S Q last) vertex) :
    P.Ancestor (C.contourOriginalVertex S Q middle) vertex := by
  obtain ⟨enter, leave, _, interval⟩ :=
    C.exists_linear_subtree_contour_interval_of_boundary_roots S boundary_roots Q starts vertex
      nonroot
  have first_bounds := (interval first).mp first_inside
  have last_bounds := (interval last).mp last_inside
  exact (interval middle).mpr ⟨first_bounds.1.trans_le before, after.trans last_bounds.2⟩

include boundary_roots starts in
/-- All original descendants have actually been processed at the unique exit. Thus the
constructed order has the depth-first property needed by the saved-frontier construction. -/
theorem exists_completed_subtree_exit_of_boundary_roots (vertex : C.Vertex Set.univ) (nonroot :
  vertex ∉ P.roots) :
    ∃ enter leave : Fin (Q.length + 1), enter.val < leave.val ∧
      (∀ i, P.Ancestor (C.contourOriginalVertex S Q i) vertex ↔
        enter.val < i.val ∧ i.val ≤ leave.val) ∧
      ∀ w, P.Ancestor w vertex → w ∈ (C.contourAfterPosition S Q leave).processed := by
  obtain ⟨enter, leave, ordered, interval⟩ :=
    C.exists_linear_subtree_contour_interval_of_boundary_roots S boundary_roots Q starts vertex
      nonroot
  refine ⟨enter, leave, ordered, interval, fun w descendant => ?_⟩
  obtain ⟨i, at_vertex⟩ := List.mem_ofFn.mp (C.mem_selectedContourSeeds_of_nonroot S Q w
    (P.descendant_nonroot nonroot descendant))
  change C.contourOriginalVertex S Q i = w at at_vertex
  have bounds := (interval i).mp (at_vertex.symm ▸ descendant)
  exact at_vertex ▸ C.contour_vertex_processed_after_le S Q i leave bounds.2


include boundary_roots in
/-- Orientation fixes the two distinctly named sides without a planar development. -/
theorem opposite_parent_banks_of_exits_of_boundary_roots (vertex : C.Vertex Set.univ) (nonroot :
  vertex ∉ P.roots)
    (enter leave : Fin (Q.length + 1)) (different : enter ≠ leave)
    (enters : ¬ C.SubtreeBoundaryInside S Q.cycle vertex enter ∧
      C.SubtreeBoundaryInside S Q.cycle vertex (finRotate (Q.length + 1) enter))
    (leaves : C.SubtreeBoundaryInside S Q.cycle vertex leave ∧
      ¬ C.SubtreeBoundaryInside S Q.cycle vertex (finRotate (Q.length + 1) leave)) :
    ∃ side,
      (C.boundaryEndEquiv (C.selectedRetain S) (Q.cycle.point enter)).1 =
        C.relativeCutBank (C.selectedRetain S) Set.univ
          (C.selectedParentCut S vertex nonroot) side ∧
      (C.boundaryEndEquiv (C.selectedRetain S) (Q.cycle.point leave)).1 =
        C.relativeCutBank (C.selectedRetain S) Set.univ
          (C.selectedParentCut S vertex nonroot) (!side) := by
  obtain ⟨first, named_first⟩ := (C.subtreeCrossingBank_iff_of_boundary_roots S boundary_roots
    vertex nonroot _).mp
    ((C.subtree_boundary_change_iff S Q.cycle Q.closes vertex enter).mpr
      (Or.inr ⟨enters.2, enters.1⟩))
  obtain ⟨last, named_last⟩ := (C.subtreeCrossingBank_iff_of_boundary_roots S boundary_roots
    vertex nonroot _).mp
    ((C.subtree_boundary_change_iff S Q.cycle Q.closes vertex leave).mpr (Or.inl leaves))
  have sides_different : first ≠ last := by
    intro same
    apply different
    apply C.boundaryChain_banks_injective (C.selectedRetain S) Q.cycle
    dsimp only
    rw [named_first, named_last, same]
  have opposite : last = !first := by
    cases first <;> cases last <;> first | rfl | exact (sides_different rfl).elim
  exact ⟨first, named_first, opposite ▸ named_last⟩


include boundary_roots starts in
/-- Linear order, original vertex region and original seam-side names are constructed together. -/
theorem exists_named_linear_subtree_interval_of_boundary_roots (vertex : C.Vertex Set.univ)
    (nonroot : vertex ∉ P.roots) :
    ∃ enter leave : Fin (Q.length + 1), ∃ side : Bool,
      enter.val < leave.val ∧
      (∀ i, P.Ancestor (C.contourOriginalVertex S Q i) vertex ↔
        enter.val < i.val ∧ i.val ≤ leave.val) ∧
      (C.boundaryEndEquiv (C.selectedRetain S) (Q.cycle.point enter)).1 =
        C.relativeCutBank (C.selectedRetain S) Set.univ
          (C.selectedParentCut S vertex nonroot) side ∧
      (C.boundaryEndEquiv (C.selectedRetain S) (Q.cycle.point leave)).1 =
        C.relativeCutBank (C.selectedRetain S) Set.univ
          (C.selectedParentCut S vertex nonroot) (!side) := by
  obtain ⟨enter, leave, different, enters, leaves, stable⟩ :=
    C.exists_oriented_subtree_exits_of_boundary_roots S boundary_roots Q.cycle Q.closes Q.covers
      vertex nonroot
  obtain ⟨side, first, last⟩ :=
    C.opposite_parent_banks_of_exits_of_boundary_roots S boundary_roots Q vertex nonroot enter
      leave different enters leaves
  have outside : ¬ C.SubtreeBoundaryInside S Q.cycle vertex 0 :=
    fun member => P.descendant_nonroot nonroot member starts
  obtain ⟨ordered, interval⟩ := finRotate_two_exits_linear_interval
    (C.SubtreeBoundaryInside S Q.cycle vertex) enter leave enters leaves stable outside
  exact ⟨enter, leave, side, ordered, interval, first, last⟩


end Unfoldings.TriangleComplex
