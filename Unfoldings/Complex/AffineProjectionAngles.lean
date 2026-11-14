module

public import Unfoldings.Complex.AffineProjectionClasses
public import Unfoldings.Complex.Angles

/-! The separate projected metric has exactly the actual projected corner-angle sums. -/

@[expose] public section

noncomputable section

namespace Unfoldings.TriangleComplex

universe u v

variable {Face : Type u} [Fintype Face] (C : TriangleComplex.{u, v} Face)
  (A : Face → Plane ≃ᵃ[ℝ] Plane)
  (joined : ∀ s x, A (C.left s).face x.val = A (C.right s).face (C.identify s x).val)

open Classical in
/-- Numerical projected fan angles are summed on precisely the original retained corner class. -/
theorem affineProjection_totalAngle (retain : Set C.Seam) (w : C.Vertex retain) :
    (C.affineProjectionComplex A joined).totalAngle retain
      (C.affineProjectionVertexEquiv A joined retain w) =
        ∑ c : C.Corner, if C.vertexOfCorner retain c = w then
          (C.affineProjectedTriangle A c.1).cornerAngle c.2 else 0 := by
  classical
  unfold totalAngle
  apply Finset.sum_congr rfl
  intro c _
  have same : (C.affineProjectionComplex A joined).vertexOfCorner retain c =
      C.affineProjectionVertexEquiv A joined retain w ↔ C.vertexOfCorner retain c = w := by
    rw [← C.affineProjectionVertexEquiv_ofCorner A joined]
    exact (C.affineProjectionVertexEquiv A joined retain).injective.eq_iff
  rw [same]
  rfl

end Unfoldings.TriangleComplex
