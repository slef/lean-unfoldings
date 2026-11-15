module

public import Unfoldings.Complex.BoundaryRolling

/-! Actual finite boundary chains roll without requiring a complete cyclic contour. -/

@[expose] public section

noncomputable section

namespace Unfoldings.TriangleComplex

universe u v

variable {Face : Type u} [Fintype Face] (C : TriangleComplex.{u, v} Face)
  {retain : Set C.Seam}

/-- A boundary end is the actual endpoint point of its named bank. -/
theorem boundaryEnd_vertexPoint_eq_endpoint (p : C.BoundaryEnd retain) :
    C.vertexPoint retain (C.boundaryEndVertex retain p) =
      C.bankMap retain (C.boundaryEndEquiv retain p).1
        ((C.triangle (C.boundaryEndEquiv retain p).1.val.face).endpoint
          (C.boundaryEndEquiv retain p).1.val.edge (C.boundaryEndEquiv retain p).2) := by
  obtain ⟨⟨bank, flag⟩, rfl⟩ := (C.boundaryEndEquiv retain).symm.surjective p
  rcases bank with ⟨⟨face, edge⟩, boundary⟩
  cases flag <;> fin_cases edge <;> rfl

variable {n : ℕ} (chain : (C.boundarySystem retain).Chain n)

/-- The actual unreduced real headings, with one turn at each internal vertex of the bank chain. -/
def boundaryChainRollHeading : Fin (n + 1) → ℝ :=
  Fin.partialSum (fun i : Fin n =>
    Real.pi - C.totalAngle retain (C.boundaryEndVertex retain (chain.point i.succ)))

@[simp] theorem boundaryChainRollHeading_zero : C.boundaryChainRollHeading chain 0 = 0 :=
  Fin.partialSum_zero _

/-- Roll the actual bank lengths and vertex fan turns, allowing overlap. -/
def boundaryChainRoll : PolygonalChain ℂ (n + 1) :=
  PolygonalChain.ofHeadings 0 (fun i => C.boundaryBankLength (chain.point i))
    (C.boundaryChainRollHeading chain)

/-- Straight actual fans imply zero real heading on every prefix, without a modulo-angle step. -/
theorem boundaryChainRollHeading_eq_zero
    (straight : ∀ i : Fin n,
      C.totalAngle retain (C.boundaryEndVertex retain (chain.point i.succ)) = Real.pi)
    (i : Fin (n + 1)) : C.boundaryChainRollHeading chain i = 0 := by
  unfold boundaryChainRollHeading
  simp only [straight, sub_self]
  exact Fin.induction rfl (fun i previous => by rw [Fin.partialSum_succ, previous, add_zero]) i

end Unfoldings.TriangleComplex
