module

public import Unfoldings.Complex.BoundaryGraph

/-!
# The two banks of each cut seam on a closed complex

When the original complex has no unpaired edges, its actual boundary banks
are exactly the cut seams with a side label. The equivalence preserves those
labels; exchanging sides gives a fixed-point-free opposite-bank involution.
-/

@[expose] public section

noncomputable section

namespace Unfoldings.TriangleComplex

universe u v

variable {Face : Type u} [Fintype Face] (C : TriangleComplex.{u, v} Face)
  (retain : Set C.Seam)

abbrev CutSeam := {s : C.Seam // s ∉ retain}

def cutBank (s : C.CutSeam retain) (side : Bool) : C.BoundaryBank retain :=
  ⟨C.seamSide s.val side, by
    cases side
    · exact (C.isBoundaryEdge_left_iff retain s.val).mpr s.property
    · exact (C.isBoundaryEdge_right_iff retain s.val).mpr s.property⟩

theorem cutBank_injective : Function.Injective (fun p : C.CutSeam retain × Bool =>
    C.cutBank retain p.1 p.2) := by
  intro p q equal
  have sides_equal := congrArg (fun b : C.BoundaryBank retain => b.val) equal
  change C.seamSide p.1.val p.2 = C.seamSide q.1.val q.2 at sides_equal
  have sides := C.seamSide_injective (a₁ := (p.1.val, p.2)) (a₂ := (q.1.val, q.2)) sides_equal
  have seams : p.1.val = q.1.val := congrArg (fun r : C.Seam × Bool => r.1) sides
  have flags : p.2 = q.2 := congrArg (fun r : C.Seam × Bool => r.2) sides
  exact Prod.ext (Subtype.ext seams) flags

variable (closed : ∀ e, ¬ C.IsBoundaryEdge Set.univ e)

def cutBankEquiv : C.CutSeam retain × Bool ≃ C.BoundaryBank retain :=
  Equiv.ofBijective (fun p => C.cutBank retain p.1 p.2) ⟨C.cutBank_injective retain, by
    intro bank
    have paired : ∃ s, C.Incident s bank.val := by
      by_contra absent
      apply closed bank.val
      rintro ⟨s, _, incident⟩
      exact absent ⟨s, incident⟩
    obtain ⟨s, incident⟩ := paired
    have cut : s ∉ retain := fun kept => bank.property ⟨s, kept, incident⟩
    rcases incident with first | last
    · exact ⟨(⟨s, cut⟩, false), Subtype.ext first.symm⟩
    · exact ⟨(⟨s, cut⟩, true), Subtype.ext last.symm⟩⟩

@[simp] theorem cutBankEquiv_apply (s : C.CutSeam retain) (side : Bool) :
    C.cutBankEquiv retain closed (s, side) = C.cutBank retain s side := rfl

def bankCutSeam (bank : C.BoundaryBank retain) : C.CutSeam retain :=
  ((C.cutBankEquiv retain closed).symm bank).1

def oppositeBank (bank : C.BoundaryBank retain) : C.BoundaryBank retain :=
  C.cutBankEquiv retain closed
    (((C.cutBankEquiv retain closed).symm bank).1,
      !((C.cutBankEquiv retain closed).symm bank).2)

theorem oppositeBank_involutive : Function.Involutive (C.oppositeBank retain closed) := by
  intro bank
  apply (C.cutBankEquiv retain closed).symm.injective
  simp only [oppositeBank, Equiv.symm_apply_apply, Bool.not_not]

theorem oppositeBank_ne (bank : C.BoundaryBank retain) :
    C.oppositeBank retain closed bank ≠ bank := by
  intro equal
  have flags := congrArg (fun b => ((C.cutBankEquiv retain closed).symm b).2) equal
  simp only [oppositeBank, Equiv.symm_apply_apply, Bool.not_eq_self] at flags

@[simp] theorem bankCutSeam_cutBank (s : C.CutSeam retain) (side : Bool) :
    C.bankCutSeam retain closed (C.cutBank retain s side) = s := by
  change ((C.cutBankEquiv retain closed).symm (C.cutBankEquiv retain closed (s, side))).1 = s
  rw [Equiv.symm_apply_apply]

theorem bankCutSeam_fiber (a b : C.BoundaryBank retain) :
    C.bankCutSeam retain closed a = C.bankCutSeam retain closed b ↔
      a = b ∨ a = C.oppositeBank retain closed b := by
  constructor
  · intro same_seam
    have flags : ((C.cutBankEquiv retain closed).symm a).2 =
          ((C.cutBankEquiv retain closed).symm b).2 ∨
        ((C.cutBankEquiv retain closed).symm a).2 =
          !((C.cutBankEquiv retain closed).symm b).2 := by
      cases ((C.cutBankEquiv retain closed).symm a).2 <;>
        cases ((C.cutBankEquiv retain closed).symm b).2 <;> simp
    rcases flags with same | opposite
    · exact Or.inl ((C.cutBankEquiv retain closed).symm.injective (Prod.ext same_seam same))
    · right
      apply (C.cutBankEquiv retain closed).symm.injective
      have pair : (C.cutBankEquiv retain closed).symm a =
          (((C.cutBankEquiv retain closed).symm b).1,
            !((C.cutBankEquiv retain closed).symm b).2) := Prod.ext same_seam opposite
      simpa only [oppositeBank, Equiv.symm_apply_apply] using pair
  · rintro (rfl | rfl)
    · rfl
    · simp only [bankCutSeam, oppositeBank, Equiv.symm_apply_apply]

end Unfoldings.TriangleComplex
