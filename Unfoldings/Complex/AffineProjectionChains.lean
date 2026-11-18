module

public import Unfoldings.Complex.AffineProjectionBoundary
public import Unfoldings.Complex.BoundaryChainRolling
public import Unfoldings.Topology.ChainInterval

/-! Actual finite bank chains and unreduced projected headings retain every original seam label. -/

@[expose] public section

noncomputable section

namespace Unfoldings.TriangleComplex

universe u v

variable {Face : Type u} [Fintype Face] (C : TriangleComplex.{u, v} Face)
  (A : Face → Plane ≃ᵃ[ℝ] Plane)
  (joined : ∀ s x, A (C.left s).face x.val = A (C.right s).face (C.identify s x).val)
  {retain : Set C.Seam} {n : ℕ} (chain : (C.boundarySystem retain).Chain n)

/-- The projected metric has the exact original bank, endpoint and successor names. -/
def affineProjectionChain :
    ((C.affineProjectionComplex A joined).boundarySystem retain).Chain n where
  point i := C.affineProjectionBoundaryEndEquiv A joined retain (chain.point i)
  injective := (C.affineProjectionBoundaryEndEquiv A joined retain).injective.comp chain.injective
  disjoint i j same := chain.disjoint i j same
  next := by
    intro i
    change (C.affineProjectionComplex A joined).boundaryMate retain
      ((C.affineProjectionComplex A joined).boundaryTurn retain
        (C.affineProjectionBoundaryEndEquiv A joined retain (chain.point i.castSucc))) = _
    rw [C.affineProjection_boundaryTurn, C.affineProjection_boundaryMate]
    exact congrArg (C.affineProjectionBoundaryEndEquiv A joined retain) (chain.next i)

@[simp] theorem affineProjectionChain_point (i : Fin (n + 1)) :
    (C.affineProjectionChain A joined chain).point i =
      C.affineProjectionBoundaryEndEquiv A joined retain (chain.point i) := rfl

open Classical in
/-- The projected real heading uses exactly the original one-sided projected corner sums. -/
theorem affineProjectionChain_heading (i : Fin (n + 1)) :
    (C.affineProjectionComplex A joined).boundaryChainRollHeading
      (C.affineProjectionChain A joined chain) i =
      Fin.partialSum (fun j : Fin n => Real.pi -
        ∑ c : C.Corner, if C.vertexOfCorner retain c =
          C.boundaryEndVertex retain (chain.point j.succ)
        then (C.affineProjectedTriangle A c.1).cornerAngle c.2 else 0) i := by
  apply congrArg (fun turns : Fin n → ℝ => Fin.partialSum turns i)
  funext j
  change Real.pi - (C.affineProjectionComplex A joined).totalAngle retain
    (C.affineProjectionVertexEquiv A joined retain
      (C.boundaryEndVertex retain (chain.point j.succ))) = _
  exact congrArg (fun angle : ℝ => Real.pi - angle)
    (C.affineProjection_totalAngle A joined retain
      (C.boundaryEndVertex retain (chain.point j.succ)))

/-- Consecutive actual bank intervals preserve exactly the same projected chain. -/
theorem affineProjectionChain_interval (first length : ℕ) (fits : first + length ≤ n) :
    C.affineProjectionChain A joined (chain.interval first length fits) =
      (C.affineProjectionChain A joined chain).interval first length fits := rfl

end Unfoldings.TriangleComplex
