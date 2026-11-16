module

public import Unfoldings.Geometry.SpatialEnvelopeWindowCut
public import Unfoldings.Metric.CutSubfamilyFiber

/-! Strict-interior window inclusion retains every original metric fiber globally. -/

@[expose] public section

namespace Unfoldings.SpatialEnvelope.WholePartition

universe u

variable {I A : Type u} [Fintype I] [Nonempty I] {family : I → SpatialPlane}
  (P : WholePartition family A) [Finite A] {J : Type*}

/-- No two actual window copies can merge above a strict-interior physical point.
This rules out competing preimages outside any chosen local ball. -/
theorem windowCutMap_injective_at (equations : J → Plane →ᵃ[ℝ] ℝ) (signs : A → J → Bool)
    (aligned : ∀ a z, z ∈ P.footprint a → ∀ j,
      0 ≤ AffineArrangement.signed (equations j) (signs a j) z)
    (cuts : Set Plane) (x : P.WindowCut signs cuts)
    (positive : ∀ j, 0 < equations j
      (Cap.horizontal (P.restoreCut cuts (P.windowCutMap signs cuts x)).val))
    (y : P.WindowCut signs cuts)
    (equal : P.windowCutMap signs cuts x = P.windowCutMap signs cuts y) :
    x = y := by
  have chosen : ∀ a,
      (MetricGluing.cutSeams (fun a : {a // WindowSelected signs a} => P.spatialCell a.val)
        (fun a => P.isClosed_spatialCell a.val) (Cap.horizontal ⁻¹' cuts)).fold x ∈
          P.spatialCell a → WindowSelected signs a := by
    intro a member
    apply P.windowSelected_of_spatial_mem equations signs aligned _ _ a member
    intro j
    exact Eq.mp (congrArg (fun p : Space => 0 < equations j (Cap.horizontal p))
      (P.restoreCut_windowCutMap signs cuts x)) (positive j)
  exact MetricGluing.cutSubfamilyMap_injective_at_of_cells_at_point P.spatialCell
    P.isClosed_spatialCell (Cap.horizontal ⁻¹' cuts) (WindowSelected signs) x chosen y
    ((P.cutIsometryEquiv cuts).symm.injective equal)

end Unfoldings.SpatialEnvelope.WholePartition
