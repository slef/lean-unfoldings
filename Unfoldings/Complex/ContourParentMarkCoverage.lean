module

public import Unfoldings.Complex.ContourParentBanks
public import Unfoldings.Complex.BoundaryChainTrace

/-! Every point on a newly cut original bank has a parent-contour mark. -/

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
local notation "Child" => {v : C.Vertex Set.univ // v ∉ P.roots}

/-- The directed contour paths run through every point of every newly cut bank. -/
theorem exists_contourParentMark_of_relativeCutBank
    (cut : C.RelativeCutSeam Retain Set.univ) (bit : Bool)
    (bank : C.BoundaryBank Retain) (named : bank = C.relativeCutBank Retain Set.univ cut bit)
    (x : (C.triangle bank.val.face).Edge bank.val.edge) :
    ∃ (v : Child) (side : Bool) (t : unitInterval),
      C.directedBoundaryPath (C.contourParentBank S Q roots starts v.val v.property side) t =
        C.bankMap Retain bank x := by
  have selected : cut.val ∈ Set.range S.edge := Classical.not_not.mp cut.property.2
  obtain ⟨v, cv⟩ := selected
  have tag : C.selectedParentCut S v.val v.property = cut := Subtype.ext cv
  let data := C.contourParentInterval S Q roots starts v.val v.property
  let parent (side : Bool) := C.contourParentBank S Q roots starts v.val v.property side
  have names : ∃ side, (C.boundaryEndEquiv Retain (parent side)).1 = bank := by
    by_cases h : bit = data.side
    · have turn := (C.boundaryEnd_bank_eq_iff Retain (parent true)
        (Q.cycle.point data.enter)).mpr (Or.inr rfl)
      exact ⟨true, turn.trans (data.entry_named.trans
        ((congrArg (fun k => C.relativeCutBank Retain Set.univ k data.side) tag).trans
          ((congrArg (C.relativeCutBank Retain Set.univ cut) h.symm).trans named.symm)))⟩
    · have h' : bit = !data.side := by cases bit <;> cases hs : data.side <;> simp_all
      exact ⟨false, data.exit_named.trans
        ((congrArg (fun k => C.relativeCutBank Retain Set.univ k (!data.side)) tag).trans
          ((congrArg (C.relativeCutBank Retain Set.univ cut) h'.symm).trans named.symm))⟩
  obtain ⟨side, eq⟩ := names
  have path : C.bankMap Retain bank x ∈ Set.range (C.directedBoundaryPath (parent side)) := by
    rw [C.directedBoundaryPath_range]
    rw [eq]
    exact ⟨x, rfl⟩
  obtain ⟨t, at_x⟩ := path
  exact ⟨v, side, t, at_x⟩

end Unfoldings.TriangleComplex
