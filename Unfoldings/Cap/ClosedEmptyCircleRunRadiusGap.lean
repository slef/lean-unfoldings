module

public import Unfoldings.Cap.ClosedEmptyCircleRadiusGap

/-! A finite run absent from a closed circle stays absent from all nearby smaller circles. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap.RadialCutForest

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexCap C} {source : Plane} {cuts : Set Plane} {N : K.RadialCutForest source cuts}
  {D : FacewiseDevelopment C N.retain} {t : ℝ} {positive : 0 < t} {small : t < 1}
  {calibration : Plane ≃ₗᵢ[ℝ] ℂ} {i : FiveSector} {ε cutoff radius : ℝ}

/-- The common lower radius is chosen from actual compact strip images. -/
theorem exists_common_inner_radius_of_empty_closed_circles
    {ι : Type*} [Finite ι] [Nonempty ι] {strips : ι → MonotoneStrip}
    (traces : ∀ j, N.RadialStripTraceData positive small D calibration i (strips j) ε cutoff)
    (radius_positive : 0 < radius) (far : radius < (1 / 2 - ε) * cutoff)
    (empty : ∀ j, (traces j).value '' closure ((strips j).openSlab 0 cutoff) ∩
      {z | ‖z - (traces j).center‖ = radius} = ∅) :
    ∃ lower : ℝ, 0 ≤ lower ∧ lower < radius ∧
      ∀ r : ℝ, lower < r → ∀ j,
        (traces j).value '' closure ((strips j).openSlab 0 cutoff) ∩
          {z | ‖z - (traces j).center‖ = r} = ∅ := by
  obtain ⟨j, maximal⟩ := Finite.exists_max (fun j => (traces j).closedRadiusBound)
  let lower := max 0 (traces j).closedRadiusBound
  have below : lower < radius :=
    max_lt radius_positive
      ((traces j).radiusBound_lt_of_empty_closed_circle radius_positive far (empty j))
  refine ⟨lower, le_max_left _ _, below, ?_⟩
  intro r beyond k
  exact (traces k).empty_closed_circle_of_radiusBound_lt
    (((maximal k).trans (le_max_right _ _)).trans_lt beyond)

end Unfoldings.ConvexCap.RadialCutForest
