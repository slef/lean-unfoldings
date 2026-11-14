module

public import Unfoldings.Geometry.SphericalConvex
public import Unfoldings.Roof.SelectionIntrinsicDisk

/-! Whole-edge components selected by spherical convex normal regions on actual roofs. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexRoof C)

/-- The same original-face component, selected by its actual outward unit normals. -/
def normalSelectionComponent (region : Set Space) (seed : Face) : Set Face :=
  K.selectionComponent (Cap.gnomonicRegion region) seed

@[simp] theorem normal_selected_iff (region : Set Space) (f : Face) :
    K.normal f ∈ region ↔ K.normalSlope f ∈ Cap.gnomonicRegion region :=
  Cap.normal_mem_iff_slope_mem (K.normal f) (K.normal_unit f) (K.normal_upward f)

theorem normalSelectionComponent_selected {region : Set Space} {seed : Face}
    (selected : K.normal seed ∈ region) {f : Face}
    (member : f ∈ K.normalSelectionComponent region seed) : K.normal f ∈ region :=
  (K.normal_selected_iff region f).mpr
    (K.selectionComponent_selected ((K.normal_selected_iff region seed).mp selected) member)

open Classical in
/-- Every selected component is an intrinsic disk with injective projection and Jordan frontier.
The statement applies to closed spherical convex regions, including degenerate ones. -/
theorem spherical_normal_selection_component {region : Set Space}
    (convex : SphericalConvex region) (closed : IsClosed region) (seed : Face)
    (selected : K.normal seed ∈ region) :
    Function.Injective (K.restrictProjection (K.normalSelectionComponent region seed)) ∧
    Nonempty ((C.restrictFaces (K.normalSelectionComponent region seed)).Realization Set.univ ≃ₜ
      Metric.closedBall (0 : Plane) 1) ∧
    Schoenflies.IsJordanCurve
      (frontier (K.restrictedCarrier (K.normalSelectionComponent region seed))) :=
  K.convex_gradient_selection_component (Cap.convex_gnomonicRegion convex)
    (Cap.isClosed_gnomonicRegion closed) seed ((K.normal_selected_iff region seed).mp selected)

end Unfoldings.ConvexRoof
