module

public import Unfoldings.Complex.SelectedSubtreeBoundary
public import Unfoldings.Topology.CyclicRegion

/-! The actual contour enters and leaves a descendant subtree through its two parent banks. -/

@[expose] public section

noncomputable section

namespace Unfoldings.TriangleComplex

universe u v

variable {Face : Type u} [Fintype Face] (C : TriangleComplex.{u, v} Face)
  {P : AscendingParents (C.Vertex Set.univ)} (S : P.EdgeSelection C.seamGraph)
  (roots : P.roots = C.relativeCutRoots Set.univ)
  {n : ℕ} (cycle : (C.boundarySystem (C.selectedRetain S)).Chain n)
  (closes : C.boundaryMate (C.selectedRetain S)
    (C.boundaryTurn (C.selectedRetain S) cycle.last) = cycle.first)
  (covers : ∀ p, cycle.Visited p)

/-- Membership is tested on the actual original vertex above each cut boundary copy. -/
def SubtreeBoundaryInside (e : C.Vertex Set.univ) (i : Fin (n + 1)) : Prop :=
  P.Ancestor (C.vertexForgetCuts (Set.subset_univ _)
    (C.boundaryEndVertex (C.selectedRetain S) (cycle.point i))) e

include closes in
theorem subtree_boundary_change_iff (e : C.Vertex Set.univ) (i : Fin (n + 1)) :
    C.SubtreeCrossingBank S e
      (C.boundaryEndEquiv (C.selectedRetain S) (cycle.point i)).1 ↔
    (C.SubtreeBoundaryInside S cycle e i ∧
      ¬ C.SubtreeBoundaryInside S cycle e (finRotate (n + 1) i)) ∨
    (C.SubtreeBoundaryInside S cycle e (finRotate (n + 1) i) ∧
      ¬ C.SubtreeBoundaryInside S cycle e i) := by
  let property (v : C.BoundaryVertex (C.selectedRetain S)) :=
    P.Ancestor (C.relativeBoundaryVertex (Set.subset_univ _) v) e
  let bank := (C.boundaryEndEquiv (C.selectedRetain S) (cycle.point i)).1
  change ((property ((C.boundaryGraph (C.selectedRetain S)).left bank) ∧
      ¬ property ((C.boundaryGraph (C.selectedRetain S)).right bank)) ∨
    (property ((C.boundaryGraph (C.selectedRetain S)).right bank) ∧
      ¬ property ((C.boundaryGraph (C.selectedRetain S)).left bank))) ↔
    ((property (C.boundaryEndAsVertex (C.selectedRetain S) (cycle.point i)) ∧
      ¬ property (C.boundaryEndAsVertex (C.selectedRetain S)
        (cycle.point (finRotate (n + 1) i)))) ∨
    (property (C.boundaryEndAsVertex (C.selectedRetain S)
      (cycle.point (finRotate (n + 1) i))) ∧
      ¬ property (C.boundaryEndAsVertex (C.selectedRetain S) (cycle.point i))))
  rw [← C.boundaryCycle_next_vertex (C.selectedRetain S) cycle closes]
  rcases C.boundaryGraph_bank_link (C.selectedRetain S) (cycle.point i) with
    ⟨first, last⟩ | ⟨first, last⟩
  · change C.boundaryEndAsVertex _ (cycle.point i) = (C.boundaryGraph _).left bank at first
    change C.boundaryEndAsVertex _ _ = (C.boundaryGraph _).right bank at last
    rw [← first, ← last]
  · change C.boundaryEndAsVertex _ (cycle.point i) = (C.boundaryGraph _).right bank at first
    change C.boundaryEndAsVertex _ _ = (C.boundaryGraph _).left bank at last
    rw [← first, ← last]
    exact or_comm

/-- The two changes in contour membership are the two distinctly named parent banks. -/
def subtreeBoundaryExitEquiv (e : C.Vertex Set.univ) (nonroot : e ∉ P.roots) :
    Bool ≃ {i : Fin (n + 1) //
      (C.SubtreeBoundaryInside S cycle e i ∧
        ¬ C.SubtreeBoundaryInside S cycle e (finRotate (n + 1) i)) ∨
      (C.SubtreeBoundaryInside S cycle e (finRotate (n + 1) i) ∧
        ¬ C.SubtreeBoundaryInside S cycle e i)} :=
  (C.subtreeCrossingBankEquiv S roots e nonroot).trans
    (((C.boundaryCycleBankEquiv (C.selectedRetain S) cycle covers).subtypeEquiv
      (fun i => (C.subtree_boundary_change_iff S cycle closes e i).symm)).symm)

include roots closes covers in
/-- One of those banks enters the subtree and the other leaves it. -/
theorem exists_oriented_subtree_exits (e : C.Vertex Set.univ) (nonroot : e ∉ P.roots) :
    ∃ enter leave : Fin (n + 1), enter ≠ leave ∧
      (¬ C.SubtreeBoundaryInside S cycle e enter ∧
        C.SubtreeBoundaryInside S cycle e (finRotate (n + 1) enter)) ∧
      (C.SubtreeBoundaryInside S cycle e leave ∧
        ¬ C.SubtreeBoundaryInside S cycle e (finRotate (n + 1) leave)) ∧
      ∀ i, i ≠ enter → i ≠ leave →
        (C.SubtreeBoundaryInside S cycle e (finRotate (n + 1) i) ↔
          C.SubtreeBoundaryInside S cycle e i) := by
  classical
  let exits := C.subtreeBoundaryExitEquiv S roots cycle closes covers e nonroot
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

end Unfoldings.TriangleComplex
