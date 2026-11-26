module

public import Unfoldings.FewestNets.RevisedLatitudeOrientation
public import Unfoldings.FewestNets.AcuteLatitudeNorthSelector
public import Unfoldings.Geometry.GnomonicChordTriangle
public import Unfoldings.Geometry.RegularPolygonFan

/-! The northern chord fan groups to one regular polygon selector. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FewestNets.RevisedLatitudeGrid

open Real Cap

open AcuteLatitudeGrid (polarFrame polarRadius polarRadius_pos polarRadius_lt)

private theorem north_row_cos_pos {a : ℝ} (positive : 0 < a) (small : a ≤ π / 6) :
    0 < cos (polarRadius a) := cos_pos_of_mem_Ioo
  ⟨by linarith only [polarRadius_pos positive, pi_pos],
    by linarith only [polarRadius_lt small, pi_gt_d2]⟩

theorem north_row_gnomonic (a : ℝ) (k : ℕ) :
    ((rings a).rowSite 0 k 2)⁻¹ • horizontal ((rings a).rowSite 0 k) =
      regularRingVertex polarFrame (rowSize a 0) (tan (polarRadius a)) k := by
  let φ := polarRadius a
  let longitude := rowLongitude (rowSize a 0) k
  have use_lon : 2 * (k : ℝ) * (π / (rowSize a 0 : ℝ)) = longitude := by
    unfold longitude rowLongitude
    ring
  have colat_zero : colatitude a 0 = φ := by simp [colatitude, φ]
  unfold regularRingVertex polarFrame
  rw [LinearIsometryEquiv.symm_symm, use_lon]
  change ((latitudeSite (colatitude a 0) longitude) 2)⁻¹ •
    horizontal (latitudeSite (colatitude a 0) longitude) = _
  rw [colat_zero, tan_eq_sin_div_cos]
  ext i
  fin_cases i
  · change (cos φ)⁻¹ * (sin φ * cos longitude) = (sin φ / cos φ) * (polarRay longitude).re
    rw [polarRay_re, div_eq_mul_inv]
    ring
  · change (cos φ)⁻¹ * (sin φ * sin longitude) = (sin φ / cos φ) * (polarRay longitude).im
    rw [polarRay_im, div_eq_mul_inv]
    ring

private theorem north_row_height (a : ℝ) (k : ℕ) : (rings a).rowSite 0 k 2 = cos (polarRadius a) := by
  change cos (colatitude a 0) = _
  simp [colatitude]

variable {a : ℝ} (positive : 0 < a) (small : a ≤ π / 6)

local notation "B" => LatitudeRings.chordBasis (rings_oriented positive small)

/-- Every northern fan triangle lies in its polar chart's open hemisphere. -/
theorem northChordBasis_upward (e : Fin (rowSize a 0)) (i : Fin 3) :
    0 < B (.inl e) i 2 := by
  rw [LatitudeRings.chordBasis_apply]
  fin_cases i
  · change 0 < cos 0
    simp
  · change 0 < (rings a).rowSite 0 (e.val + 1) 2
    rw [north_row_height]
    exact north_row_cos_pos positive small
  · change 0 < (rings a).rowSite 0 e.val 2
    rw [north_row_height]
    exact north_row_cos_pos positive small

/-- The north chart vertices are the center and the two consecutive ring sites. -/
theorem northChordBasis_chart_range (e : Fin (rowSize a 0)) :
    Set.range (chordChartVertex (B (.inl e))) =
      {0, regularRingVertex polarFrame (rowSize a 0) (tan (polarRadius a)) e.val,
        regularRingVertex polarFrame (rowSize a 0) (tan (polarRadius a)) (e.val + 1)} := by
  let z := chordChartVertex (B (.inl e))
  have pole : z 0 = 0 := by
    unfold z chordChartVertex
    rw [LatitudeRings.chordBasis_apply]
    change (cos 0)⁻¹ • horizontal (latitudeSite 0 0) = _
    have zero : horizontal (latitudeSite 0 0) = 0 := by
      ext i
      fin_cases i <;> simp [horizontal, latitudeSite]
    rw [zero, smul_zero]
  have following : z 1 = regularRingVertex polarFrame (rowSize a 0) (tan (polarRadius a))
      (e.val + 1) := by
    simp only [z, chordChartVertex, LatitudeRings.chordBasis_apply]
    exact north_row_gnomonic a (e.val + 1)
  have current : z 2 = regularRingVertex polarFrame (rowSize a 0) (tan (polarRadius a))
      e.val := by
    simp only [z, chordChartVertex, LatitudeRings.chordBasis_apply]
    exact north_row_gnomonic a e.val
  ext p
  change p ∈ Set.range z ↔ _
  simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨i, rfl⟩
    fin_cases i
    · exact Or.inl pole
    · exact Or.inr (Or.inr following)
    · exact Or.inr (Or.inl current)
  · rintro (rfl | rfl | rfl)
    · exact ⟨0, pole⟩
    · exact ⟨2, current⟩
    · exact ⟨1, following⟩

/-- The northern spherical selector is exactly the whole regular polar polygon. -/
theorem northPolarSelector_eq_chordFan :
    gnomonicNormal '' regularSlopePolygon polarFrame (rowSize a 0) (tan (polarRadius a)) =
      ⋃ e : Fin (rowSize a 0), {p : Space | ‖p‖ = 1 ∧ ∀ i, 0 ≤ (B (.inl e)).coord i p} := by
  have sides : 3 ≤ rowSize a 0 := rowSize_ge_three positive small (Nat.zero_le _)
  have radius : 0 < tan (polarRadius a) := tan_pos_of_pos_of_lt_pi_div_two
    (polarRadius_pos positive) (by linarith only [polarRadius_lt small, pi_gt_d2])
  rw [regularSlopePolygon_eq_iUnion_fan polarFrame sides radius, Set.image_iUnion]
  apply congrArg Set.iUnion
  funext e
  rw [← northChordBasis_chart_range positive small]
  exact gnomonicNormal_image_chordChart (B (.inl e)) (northChordBasis_upward positive small e)

end Unfoldings.FewestNets.RevisedLatitudeGrid
