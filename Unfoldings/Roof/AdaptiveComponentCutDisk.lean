module

public import Unfoldings.Roof.AdaptivePotentialForest
public import Unfoldings.Roof.CompatibleComponentCutDisk

/-! Adaptive original-seam parents cut each selected component to a disk. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof.AdaptivePotentialRouting

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexRoof C} {slopes L : Set Plane} {E : SlopeEnvelope} {r margin : ℝ}
  (R : K.AdaptivePotentialRouting {f | K.normalSlope f ∈ slopes} E L r margin)

open Classical in
/-- Keep the actual original seam identities when cutting a component
along its adaptive forest. -/
theorem exists_component_cut_disk (convex : Convex ℝ slopes) (closed : IsClosed slopes)
    (seed : Face) (selected : K.normalSlope seed ∈ slopes) :
    let U := K.selectionComponent slopes seed
    Nonempty ((C.restrictFaces U).Realization (C.restrictRetain U (C.selectedRetain R.selection)) ≃ₜ
      Metric.closedBall (0 : Plane) 1) :=
  K.exists_selected_component_cut_disk convex closed seed selected
    R.parents R.roots_eq R.selection

end Unfoldings.ConvexRoof.AdaptivePotentialRouting
