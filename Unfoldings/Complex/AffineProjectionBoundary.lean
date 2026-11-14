module

public import Unfoldings.Complex.AffineProjectionAngles
public import Unfoldings.Complex.BoundaryContour

/-! Projected metrics retain the exact same directed banks, vertex mates and contour order. -/

@[expose] public section

noncomputable section

namespace Unfoldings.TriangleComplex

universe u v

variable {Face : Type u} [Fintype Face] (C : TriangleComplex.{u, v} Face)
  (A : Face → Plane ≃ᵃ[ℝ] Plane)
  (joined : ∀ s x, A (C.left s).face x.val = A (C.right s).face (C.identify s x).val)
  (retain : Set C.Seam)

/-- The directed bank names and endpoint flags are unchanged by projection. -/
def affineProjectionBoundaryEndEquiv :
    C.BoundaryEnd retain ≃ (C.affineProjectionComplex A joined).BoundaryEnd retain :=
  Equiv.refl _

@[simp] theorem affineProjection_boundaryEndVertex (p : C.BoundaryEnd retain) :
    (C.affineProjectionComplex A joined).boundaryEndVertex retain
      (C.affineProjectionBoundaryEndEquiv A joined retain p) =
        C.affineProjectionVertexEquiv A joined retain (C.boundaryEndVertex retain p) := rfl

@[simp] theorem affineProjection_boundaryTurn (p : C.BoundaryEnd retain) :
    (C.affineProjectionComplex A joined).boundaryTurn retain
      (C.affineProjectionBoundaryEndEquiv A joined retain p) =
        C.affineProjectionBoundaryEndEquiv A joined retain (C.boundaryTurn retain p) := rfl

/-- Boundary mates are the same actual two corner classes, independently of the metric change. -/
theorem affineProjection_boundaryMate (p : C.BoundaryEnd retain) :
    (C.affineProjectionComplex A joined).boundaryMate retain
      (C.affineProjectionBoundaryEndEquiv A joined retain p) =
        C.affineProjectionBoundaryEndEquiv A joined retain (C.boundaryMate retain p) := by
  let P := C.affineProjectionComplex A joined
  let e := C.affineProjectionBoundaryEndEquiv A joined retain
  apply (P.exists_unique_other_boundaryEnd retain (e p)).unique
    (P.boundaryMate_spec retain (e p))
  refine ⟨e.injective.ne (C.boundaryMate_spec retain p).1, ?_⟩
  exact congrArg (C.affineProjectionVertexEquiv A joined retain)
    (C.boundaryMate_spec retain p).2

/-- Preserve the complete actual cyclic bank order when changing to projected edge lengths. -/
def affineProjectionContour (Q : C.BoundaryContour retain) :
    (C.affineProjectionComplex A joined).BoundaryContour retain where
  length := Q.length
  cycle := {
    point := fun i => C.affineProjectionBoundaryEndEquiv A joined retain (Q.cycle.point i)
    injective := (C.affineProjectionBoundaryEndEquiv A joined retain).injective.comp
      Q.cycle.injective
    disjoint := fun i j same => Q.cycle.disjoint i j same
    next := by
      intro i
      change (C.affineProjectionComplex A joined).boundaryMate retain
        ((C.affineProjectionComplex A joined).boundaryTurn retain
          (C.affineProjectionBoundaryEndEquiv A joined retain (Q.cycle.point i.castSucc))) = _
      rw [C.affineProjection_boundaryTurn, C.affineProjection_boundaryMate]
      exact congrArg (C.affineProjectionBoundaryEndEquiv A joined retain) (Q.cycle.next i) }
  closes := by
    change (C.affineProjectionComplex A joined).boundaryMate retain
      ((C.affineProjectionComplex A joined).boundaryTurn retain
        (C.affineProjectionBoundaryEndEquiv A joined retain Q.cycle.last)) = _
    rw [C.affineProjection_boundaryTurn, C.affineProjection_boundaryMate]
    exact congrArg (C.affineProjectionBoundaryEndEquiv A joined retain) Q.closes
  covers := Q.covers

end Unfoldings.TriangleComplex
