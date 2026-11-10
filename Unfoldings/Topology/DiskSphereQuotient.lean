module

public import Unfoldings.Topology.BoundaryCollapse
public import Unfoldings.Topology.BallBoundaryQuotient
public import Unfoldings.Topology.BoundaryQuotientTransport
public import Mathlib.Analysis.Normed.Module.Ball.Homeomorph
public import Mathlib.Topology.Compactification.OnePoint.Sphere

/-!
# Collapsing the disk boundary produces a sphere

The disk interior is the open unit ball, hence homeomorphic to the plane.
Collapse the boundary to infinity in that interior's one-point compactification,
then use Mathlib's proved one-point-plane-to-sphere homeomorphism. Fibers are
exactly equality or pairs of boundary points.
-/

@[expose] public section

noncomputable section

namespace Unfoldings

def diskBoundarySphereHomeomorph :
    OnePoint ↥((closedBallBoundary (E := EuclideanSpace ℝ (Fin 2)))ᶜ) ≃ₜ
      Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 :=
  ((closedBallInteriorHomeomorph (E := EuclideanSpace ℝ (Fin 2))).trans
    (Homeomorph.unitBall (E := EuclideanSpace ℝ (Fin 2))).symm).onePointCongr.trans
      (onePointEquivSphereOfFinrankEq (ι := Fin 3)
        (V := EuclideanSpace ℝ (Fin 2)) (by simp))

def closedDiskSphereQuotient :
    BoundaryQuotient (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1)
      (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :=
  (collapseBoundaryQuotient (closedBallBoundary (E := EuclideanSpace ℝ (Fin 2)))
    isClosed_closedBallBoundary (by
      obtain ⟨x, norm⟩ := exists_norm_eq (EuclideanSpace ℝ (Fin 2)) (zero_le_one : (0 : ℝ) ≤ 1)
      exact ⟨⟨x, by rw [Metric.mem_closedBall, dist_zero_right, norm]⟩, norm⟩)).postcomp
        diskBoundarySphereHomeomorph

@[simp] theorem closedDiskSphereQuotient_boundary :
    closedDiskSphereQuotient.boundary = closedBallBoundary := rfl

end Unfoldings
