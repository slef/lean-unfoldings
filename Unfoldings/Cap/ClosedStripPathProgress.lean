module

public import Unfoldings.Cap.ClosedStripIncrementError
public import Unfoldings.Geometry.ChainCoordinateMargins

/-! Closed strip traces progress strictly along any actual parent path with a uniform margin. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap.RadialCutForest.RadialStripTraceData

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexCap C} {source : Plane} {cuts : Set Plane} {N : K.RadialCutForest source cuts}
  {t : ℝ} {positive : 0 < t} {small : t < 1} {D : FacewiseDevelopment C N.retain}
  {calibration : Plane ≃ₗᵢ[ℝ] ℂ} {i : FiveSector} {S : MonotoneStrip} {ε cutoff : ℝ}
  (data : N.RadialStripTraceData positive small D calibration i S ε cutoff)

/-- Both controlling coordinates grow strictly between actual closed points on the same
margin-controlled path, including branch endpoints and terminal pinch vertices. -/
theorem closed_coordinates_strict_on_margin_path (nonnegative : 0 ≤ ε)
    (linear_error : ∀ f z,
      ‖(D.coordinatePlacement K calibration (fiveSectorFrame t positive small i).place f).linear z -
        z‖ ≤ ε * ‖z‖)
    {n : ℕ} (P : PolygonalChain ℂ n) {μ : ℝ} (numerical : 2 * ε < μ)
    (heights : ∀ j, 0 ≤ (P.edge j).re + (P.edge j).im)
    (margins : ∀ j,
      μ * ((P.edge j).re + (P.edge j).im) ≤ (P.edge j).re ∧
      μ * ((P.edge j).re + (P.edge j).im) ≤ (P.edge j).im)
    (j k : Fin n) (s r : unitInterval)
    (first : P.point j s ∈ closure data.strictDomain)
    (last : P.point k r ∈ closure data.strictDomain)
    (ordered : (P.point j s).re + (P.point j s).im <
      (P.point k r).re + (P.point k r).im) :
    (data.value (P.point j s)).re < (data.value (P.point k r)).re ∧
      (data.value (P.point j s)).im < (data.value (P.point k r)).im := by
  have bounds := P.coordinate_increment_margins heights margins j k s r ordered
  have μpositive : 0 < μ := (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) nonnegative).trans_lt numerical
  have height_positive := sub_pos.mpr ordered
  have horizontal := (mul_pos μpositive height_positive).le.trans bounds.1
  have vertical := (mul_pos μpositive height_positive).le.trans bounds.2
  exact data.closed_coordinates_strict_of_increment_margin nonnegative linear_error first last
    (sub_nonneg.mp horizontal) (sub_nonneg.mp vertical) ordered numerical bounds.1 bounds.2

end Unfoldings.ConvexCap.RadialCutForest.RadialStripTraceData
