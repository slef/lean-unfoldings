module

public import Unfoldings.Complex.SelectedCuts
public import Unfoldings.Complex.RelativeBankEnumeration
public import Unfoldings.Complex.BoundaryCycleEnumeration
public import Unfoldings.Topology.SelectedSubtree

/-!
# The two actual boundary exits of a descendant subtree

For the constructed original-edge forest, a descendant subtree meets the rest
of the disk boundary through exactly the two banks of its parent's original
seam. Original rim banks cannot be exits. This is intrinsic boundary accounting
and makes no assumption about a planar development.
-/

@[expose] public section

noncomputable section

namespace Unfoldings.TriangleComplex

universe u v

variable {Face : Type u} [Fintype Face] (C : TriangleComplex.{u, v} Face)
  {P : AscendingParents (C.Vertex Set.univ)} (S : P.EdgeSelection C.seamGraph)
  (roots : P.roots = C.relativeCutRoots Set.univ)

/-- The actual selected parent seam, as a newly cut original seam. -/
def selectedParentCut (e : C.Vertex Set.univ) (nonroot : e ∉ P.roots) :
    C.RelativeCutSeam (C.selectedRetain S) Set.univ :=
  ⟨S.edge ⟨e, nonroot⟩, Set.mem_univ _, fun kept => kept ⟨⟨e, nonroot⟩, rfl⟩⟩

/-- A bank crosses the descendant separator precisely when its two ends lie on different sides. -/
def SubtreeCrossingBank (e : C.Vertex Set.univ) (bank : C.BoundaryBank (C.selectedRetain S)) :
    Prop :=
  (P.Ancestor (C.relativeBoundaryVertex (Set.subset_univ _)
      ((C.boundaryGraph (C.selectedRetain S)).left bank)) e ∧
    ¬ P.Ancestor (C.relativeBoundaryVertex (Set.subset_univ _)
      ((C.boundaryGraph (C.selectedRetain S)).right bank)) e) ∨
  (P.Ancestor (C.relativeBoundaryVertex (Set.subset_univ _)
      ((C.boundaryGraph (C.selectedRetain S)).right bank)) e ∧
    ¬ P.Ancestor (C.relativeBoundaryVertex (Set.subset_univ _)
      ((C.boundaryGraph (C.selectedRetain S)).left bank)) e)

include roots in
/-- The two parent banks are exactly the actual boundary exits of the subtree. -/
theorem subtreeCrossingBank_iff (e : C.Vertex Set.univ) (nonroot : e ∉ P.roots)
    (bank : C.BoundaryBank (C.selectedRetain S)) :
    C.SubtreeCrossingBank S e bank ↔
      ∃ side, bank = C.relativeCutBank (C.selectedRetain S) Set.univ
        (C.selectedParentCut S e nonroot) side := by
  rcases C.relativeBank_cases (C.selectedRetain S) Set.univ bank with old | ⟨s, side, rfl⟩
  · have left_root : C.relativeBoundaryVertex (Set.subset_univ _)
        ((C.boundaryGraph (C.selectedRetain S)).left bank) ∈ P.roots :=
      roots.symm ▸ C.relativeBoundaryVertex_old_left (Set.subset_univ _) bank old
    have right_root : C.relativeBoundaryVertex (Set.subset_univ _)
        ((C.boundaryGraph (C.selectedRetain S)).right bank) ∈ P.roots :=
      roots.symm ▸ C.relativeBoundaryVertex_old_right (Set.subset_univ _) bank old
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
def subtreeCrossingBankEquiv (e : C.Vertex Set.univ) (nonroot : e ∉ P.roots) :
    Bool ≃ {bank : C.BoundaryBank (C.selectedRetain S) // C.SubtreeCrossingBank S e bank} :=
  Equiv.ofBijective (fun side =>
    ⟨C.relativeCutBank (C.selectedRetain S) Set.univ (C.selectedParentCut S e nonroot) side,
      (C.subtreeCrossingBank_iff S roots e nonroot _).mpr ⟨side, rfl⟩⟩) ⟨by
    intro a b equal
    have banks := congrArg Subtype.val equal
    exact congrArg Prod.snd
      (C.relativeCutBank_injective (C.selectedRetain S) Set.univ
        (a₁ := (C.selectedParentCut S e nonroot, a))
        (a₂ := (C.selectedParentCut S e nonroot, b)) banks), by
    intro bank
    obtain ⟨side, same⟩ := (C.subtreeCrossingBank_iff S roots e nonroot bank.val).mp bank.property
    exact ⟨side, Subtype.ext same.symm⟩⟩

include roots in
theorem card_subtreeCrossingBank (e : C.Vertex Set.univ) (nonroot : e ∉ P.roots) :
    Nat.card {bank : C.BoundaryBank (C.selectedRetain S) //
      C.SubtreeCrossingBank S e bank} = 2 := by
  rw [← Nat.card_congr (C.subtreeCrossingBankEquiv S roots e nonroot)]
  exact Nat.card_eq_fintype_card

end Unfoldings.TriangleComplex
