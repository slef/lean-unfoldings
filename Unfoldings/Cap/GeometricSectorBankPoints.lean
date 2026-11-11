module

public import Unfoldings.Cap.GeometricSectorBoundaryLeaves
public import Unfoldings.Geometry.RayHeightSegments
public import Unfoldings.Geometry.HeightGraphLatticePoints
public import Unfoldings.Geometry.RayStripPinches

/-! Enclosing-strip banks are actual sector rays and fail the strict sector-coordinate test. -/

@[expose] public section

noncomputable section

namespace Unfoldings

namespace AcuteWedgeFrame

variable {u v : Plane} (B : AcuteWedgeFrame u v)

theorem enclosingStrip_coordinate_homogeneous {h : ℝ} (nonnegative : 0 ≤ h) :
    B.enclosingStrip.lower.coordinate h = B.enclosingStrip.lower.coordinate 1 * h ∧
      B.enclosingStrip.upper.coordinate h = B.enclosingStrip.upper.coordinate 1 * h :=
  MonotoneStrip.rayStrip_coordinate_homogeneous _ _ _ _ _ _ nonnegative

theorem enclosingStrip_recoverablePinchesIn (b : ℝ) :
    B.enclosingStrip.RecoverablePinchesIn {0} 0 b :=
  MonotoneStrip.rayStrip_recoverablePinchesIn _ _ _ _ _ _ b

end AcuteWedgeFrame

theorem fiveSector_enclosingStrip_bank_not_strict {t : ℝ} (positive : 0 < t) (small : t < 1)
    (i : FiveSector) (h : ℝ) :
    let B := fiveSectorFrame t positive small i
    B.place.symm (B.enclosingStrip.lower.point h) ∉ strictFiveSector t i ∧
      B.place.symm (B.enclosingStrip.upper.point h) ∉ strictFiveSector t i := by
  let B := fiveSectorFrame t positive small i
  have first_quad := B.quadrant_self
    (x := fiveSectorFirst t i) ⟨1, 0, by norm_num, le_rfl, by simp⟩ B.first_ne
  have last_quad := B.quadrant_self
    (x := fiveSectorLast t i) ⟨0, 1, le_rfl, by norm_num, by simp⟩ B.last_ne
  let P := MonotoneHeightGraph.ray (B.place (fiveSectorFirst t i)) first_quad.1 first_quad.2
  let Q := MonotoneHeightGraph.ray (B.place (fiveSectorLast t i)) last_quad.1 last_quad.2
  have first_bank : B.place.symm (P.point h) ∉ strictFiveSector t i := by
    intro strict
    rw [MonotoneHeightGraph.ray_point_eq_smul, map_smul, map_smul,
      B.place.symm_apply_apply] at strict
    have zero : fiveSectorCoordinates t i
        (h • (((B.place (fiveSectorFirst t i)).re +
          (B.place (fiveSectorFirst t i)).im)⁻¹ • fiveSectorFirst t i)) 1 = 0 := by
      rw [map_smul, map_smul, fiveSectorCoordinates_first]
      simp
    exact (zero ▸ strict.2).false
  have last_bank : B.place.symm (Q.point h) ∉ strictFiveSector t i := by
    intro strict
    rw [MonotoneHeightGraph.ray_point_eq_smul, map_smul, map_smul,
      B.place.symm_apply_apply] at strict
    have zero : fiveSectorCoordinates t i
        (h • (((B.place (fiveSectorLast t i)).re +
          (B.place (fiveSectorLast t i)).im)⁻¹ • fiveSectorLast t i)) 0 = 0 := by
      rw [map_smul, map_smul, fiveSectorCoordinates_last]
      simp
    exact (zero ▸ strict.1).false
  constructor
  · change B.place.symm ((P.min Q).point h) ∉ strictFiveSector t i
    rcases P.min_point_eq_or Q h with equal | equal
    · exact equal.symm ▸ first_bank
    · exact equal.symm ▸ last_bank
  · change B.place.symm ((P.max Q).point h) ∉ strictFiveSector t i
    rcases P.max_point_eq_or Q h with equal | equal
    · exact equal.symm ▸ first_bank
    · exact equal.symm ▸ last_bank

end Unfoldings
