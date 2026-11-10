module

public import Unfoldings.Complex.RelativeCutGraph

/-!
# Old banks and newly opened banks

Further cutting retains each old bank label and creates exactly two bank labels
for each newly opened seam. No topology or nonoverlap premise is needed.
-/

@[expose] public section

noncomputable section

namespace Unfoldings.TriangleComplex

universe u v

variable {Face : Type u} [Fintype Face] (C : TriangleComplex.{u, v} Face)
  {small large : Set C.Seam} (inclusion : small ⊆ large)

def oldBoundaryBank (bank : C.BoundaryBank large) : C.BoundaryBank small :=
  ⟨bank.val, C.isBoundaryEdge_antitone inclusion bank.property⟩

/-- A newly created bank was paired before its seam was cut. -/
theorem relativeCutBank_not_old (s : C.RelativeCutSeam small large) (side : Bool) :
    ¬ C.IsBoundaryEdge large (C.relativeCutBank small large s side).val := by
  cases side
  · exact fun boundary => (C.isBoundaryEdge_left_iff large s.val).mp boundary s.property.1
  · exact fun boundary => (C.isBoundaryEdge_right_iff large s.val).mp boundary s.property.1

/-- Exact enumeration, retaining the old labels and the two actual sides of every new cut. -/
def relativeBoundaryBankEquiv :
    C.BoundaryBank large ⊕ (C.RelativeCutSeam small large × Bool) ≃ C.BoundaryBank small :=
  Equiv.ofBijective (Sum.elim (C.oldBoundaryBank inclusion)
    (fun p => C.relativeCutBank small large p.1 p.2)) ⟨by
      intro a b equal
      cases a with
      | inl a =>
        cases b with
        | inl b =>
          exact congrArg Sum.inl
            (Subtype.ext (congrArg (fun bank : C.BoundaryBank small => bank.val) equal))
        | inr b =>
          exact (C.relativeCutBank_not_old b.1 b.2
            (congrArg Subtype.val equal ▸ a.property)).elim
      | inr a =>
        cases b with
        | inl b =>
          exact (C.relativeCutBank_not_old a.1 a.2
            (congrArg Subtype.val equal.symm ▸ b.property)).elim
        | inr b => exact congrArg Sum.inr (C.relativeCutBank_injective small large equal), by
      intro bank
      rcases C.relativeBank_cases small large bank with old | ⟨s, side, same⟩
      · exact ⟨Sum.inl ⟨bank.val, old⟩, Subtype.ext rfl⟩
      · exact ⟨Sum.inr (s, side), same.symm⟩⟩

end Unfoldings.TriangleComplex
