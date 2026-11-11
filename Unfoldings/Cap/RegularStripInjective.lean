module

public import Unfoldings.Cap.CenteredDevelopedMap
public import Unfoldings.Cap.CompletedCalibratedThreshold

/-! A uniform cap tilt bound makes the actual regular developed strip maps injective. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap

universe u v

/-- Choose the tilt before the cap or its mesh. The map, chart choices, and continuity are
constructed from the minimal development; arbitrary extra flat completion cuts are not removed
from the projected domain. Positive-width slabs avoid any identification of merged bank copies. -/
theorem exists_uniform_regular_strip_injectivity :
    ∃ φ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), (3 : ℝ) / 4 ≤ Real.cos φ ∧
      ∀ {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexCap C),
        K.TiltBound φ → ∀ (q : Plane) (cuts : Set Plane) (R : K.RadialCutForest q cuts),
          R.CurvedPathWedges → ∀ D : FacewiseDevelopment C R.retain,
            ∃ calibration : Plane ≃ₗᵢ[ℝ] ℂ, ∀ (frame : Plane ≃ₗᵢ[ℝ] ℂ)
              (S : MonotoneStrip) (a b : ℝ),
              (∀ h ∈ Set.Icc a b, S.lower.coordinate h < S.upper.coordinate h) →
              (∀ z, z ∈ S.strictCarrier → z.re + z.im ∈ Set.Icc a b →
                q + frame.symm z ∈ K.footprint \ K.projectedCutSet R.retain) →
              Set.InjOn (D.centeredMap K q calibration frame)
                {z | z ∈ S.strictCarrier ∧ z.re + z.im ∈ Set.Icc a b} := by
  obtain ⟨δ, positive, margins⟩ :=
    FacewiseDevelopment.exists_coordinatePlacement_axis_threshold.{u, v}
  obtain ⟨φ, bounds, normal, control⟩ := exists_uniform_completed_direction_control positive
  refine ⟨φ, bounds, normal, fun K tilt q cuts R wedges D => ?_⟩
  obtain ⟨calibration, close⟩ := control K tilt q cuts R wedges (R.completedDevelopment D)
  refine ⟨calibration, fun frame S a b width inside => ?_⟩
  exact D.centeredMap_injOn_open_strip K q calibration frame
    (margins (R.completedDevelopment D) K calibration close frame) S a b width inside

end Unfoldings.ConvexCap
