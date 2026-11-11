module

public import Unfoldings.Cap.ProjectedStripMaps
public import Unfoldings.Geometry.MonotoneStripBoundedInjective
public import Unfoldings.Cap.CompletedCalibratedThreshold

/-! Mesh-independent tilt bounds make every coherently developed monotone strip injective. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap

universe u v

/-- Only the bounded-height strip must carry the actual face maps.
The strip may have boundary contacts and a zero-width tail. Its developed map must actually
be continuous and select the calibrated original face maps. This theorem proves injectivity
from those local facts; it does not construct a strip partition of the cut surface. -/
theorem exists_uniform_completed_bounded_strip_injectivity :
    ∃ φ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), (3 : ℝ) / 4 ≤ Real.cos φ ∧
      ∀ {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexCap C),
        K.TiltBound φ → ∀ (q : Plane) (cuts : Set Plane) (R : K.RadialCutForest q cuts),
          R.CurvedPathWedges → ∀ D : FacewiseDevelopment C R.completedRetain,
            ∃ calibration : Plane ≃ₗᵢ[ℝ] ℂ, ∀ (frame : Plane ≃ₗᵢ[ℝ] ℂ)
              (S : MonotoneStrip) (a b : ℝ) (F : ℂ → ℂ),
              ContinuousOn F (S.boundedCarrier a b) →
              (∀ z ∈ S.boundedCarrier a b, ∃ f,
                F z = D.coordinatePlacement K calibration frame f z) →
              Set.InjOn F (S.boundedCarrier a b) := by
  obtain ⟨δ, positive, margins⟩ :=
    FacewiseDevelopment.exists_coordinatePlacement_axis_threshold.{u, v}
  obtain ⟨φ, bounds, normal, control⟩ := exists_uniform_completed_direction_control positive
  refine ⟨φ, bounds, normal, fun K tilt q cuts R wedges D => ?_⟩
  obtain ⟨calibration, close⟩ := control K tilt q cuts R wedges D
  refine ⟨calibration, fun frame S a b F continuous selected => ?_⟩
  exact S.injOn_bounded_of_affine_selection
    (fun f => (D.coordinatePlacement K calibration frame f).toAffineMap)
    (D.coordinatePlacement_continuous K calibration frame)
    (margins D K calibration close frame) a b continuous selected

end Unfoldings.ConvexCap
