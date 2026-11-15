module

public import Unfoldings.Complex.FutureParentBanks

/-! The surviving future banks enumerate exactly the original processed ancestor path. -/

@[expose] public section

noncomputable section

namespace Unfoldings.TriangleComplex

universe u v

variable {Face : Type u} [Fintype Face] (C : TriangleComplex.{u, v} Face)
  {P : AscendingParents (C.Vertex Set.univ)} (S : P.EdgeSelection C.seamGraph)
  (roots : P.roots = C.relativeCutRoots Set.univ)
  (Q : C.BoundaryContour (C.selectedRetain S))
  (starts : C.contourOriginalVertex S Q 0 ∈ P.roots)

/-- Upcoming original nonrim banks that are actual banks in the current cut. -/
def RootwardBank (i : Fin (Q.length + 1)) :=
  {j : Fin (Q.length + 1) // i.val ≤ j.val ∧
    C.IsBoundaryEdge (C.processedParentRetain S (C.contourFrontier S Q i))
      (C.germEdge (Q.cycle.point j).val) ∧
    ¬ C.IsBoundaryEdge Set.univ (C.germEdge (Q.cycle.point j).val)}

/-- Already processed nonroot original ancestors of the current source. -/
def RootwardAncestor (i : Fin (Q.length + 1)) :=
  {vertex : C.Vertex Set.univ // vertex ∉ P.roots ∧
    vertex ∈ (C.contourFrontier S Q i).processed ∧
    P.Ancestor (C.contourOriginalVertex S Q i) vertex}

/-- Restore precisely the original selector of the actual future bank. -/
def rootwardBankAncestor (i : Fin (Q.length + 1)) (j : C.RootwardBank S Q i) :
    C.RootwardAncestor S Q i :=
  ⟨C.contourOriginalVertex S Q j.val,
    (C.future_current_bank_rootward S roots Q starts i j.val j.property.1
      j.property.2.1 j.property.2.2).1,
    (C.future_current_bank_rootward S roots Q starts i j.val j.property.1
      j.property.2.1 j.property.2.2).2.1,
    (C.future_current_bank_rootward S roots Q starts i j.val j.property.1
      j.property.2.1 j.property.2.2).2.2.1⟩

/-- This is a bijection of actual bank indices with original path vertices: every surviving
bank occurs once, and no original nonroot ancestor is omitted. -/
def rootwardBankEquiv (i : Fin (Q.length + 1)) :
    C.RootwardBank S Q i ≃ C.RootwardAncestor S Q i :=
  Equiv.ofBijective (C.rootwardBankAncestor S roots Q starts i) ⟨by
    intro j k same
    have labels : C.contourOriginalVertex S Q j.val = C.contourOriginalVertex S Q k.val :=
      congrArg Subtype.val same
    obtain ⟨nonroot, side, first⟩ := C.future_current_bank_named S roots Q starts i j.val
      j.property.1 j.property.2.1 j.property.2.2
    obtain ⟨_, other, last⟩ := C.future_current_bank_named S roots Q starts i k.val
      k.property.1 k.property.2.1 k.property.2.2
    simp only [← labels] at last
    have data := C.future_current_bank_rootward S roots Q starts i j.val
      j.property.1 j.property.2.1 j.property.2.2
    obtain ⟨index, _property, unique⟩ := C.existsUnique_future_parent_bank S roots Q starts i
      (C.contourOriginalVertex S Q j.val) nonroot data.2.1 data.2.2.1
    exact Subtype.ext ((unique j.val ⟨j.property.1, side, first⟩).trans
      (unique k.val ⟨k.property.1, other, last⟩).symm), by
    intro vertex
    obtain ⟨j, ⟨future, side, named⟩, _unique⟩ :=
      C.existsUnique_future_parent_bank S roots Q starts i
      vertex.val vertex.property.1 vertex.property.2.1 vertex.property.2.2
    have current := (C.selected_parent_bank_current_iff S (C.contourFrontier S Q i)
      vertex.val vertex.property.1 (Q.cycle.point j) side named).mpr vertex.property.2.1
    have not_rim : ¬ C.IsBoundaryEdge Set.univ (C.germEdge (Q.cycle.point j).val) := by
      have raw := congrArg (fun b : C.BoundaryBank (C.selectedRetain S) => b.val) named
      exact fun old => C.relativeCutBank_not_old
        (C.selectedParentCut S vertex.val vertex.property.1) side (raw ▸ old)
    refine ⟨⟨j, future, current, not_rim⟩, Subtype.ext ?_⟩
    exact (C.future_processed_parent_bank S roots Q starts i j future vertex.val
      vertex.property.1 vertex.property.2.1 side named).2.1⟩

end Unfoldings.TriangleComplex
