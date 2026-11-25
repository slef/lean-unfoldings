module

public import Unfoldings.FewestNets.LatitudeFiniteSites
public import Unfoldings.Geometry.RegularPolygonFan
public import Unfoldings.Geometry.SpatialConvexPoleDisk
public import Unfoldings.Geometry.FrontierRays

/-! Every radial direction meets the boundary of the sampled latitude hull. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FewestNets

open Real

private theorem latitude_north_pole :
    latitudeSite 0 0 = Cap.horizontalAtHeight 0 1 := by
  ext i
  fin_cases i <;> simp [latitudeSite, Cap.horizontalAtHeight]

private theorem latitude_south_pole :
    latitudeSite π 0 = Cap.horizontalAtHeight 0 (-1) := by
  ext i
  fin_cases i <;> simp [latitudeSite, Cap.horizontalAtHeight]

/-- The equatorial disk obtained by moving the first row along straight
segments toward the southern pole is inside the sampled hull. -/
theorem zero_mem_interior_latitudeHull {a : ℝ} (positive : 0 < a) (small : a ≤ π / 6) :
    (0 : Space) ∈ interior (convexHull ℝ (latitudeSites a)) := by
  let H := convexHull ℝ (latitudeSites a)
  let k := latitudeRowSize a 0
  let ell := latitudeColatitude a 0
  let J : Plane ≃ₗᵢ[ℝ] ℂ := Complex.orthonormalBasisOneI.repr.symm
  have convex : Convex ℝ H := convex_convexHull ℝ _
  have north : Cap.horizontalAtHeight 0 1 ∈ H :=
    latitude_north_pole ▸ subset_convexHull ℝ _ (Or.inl (Set.mem_insert _ _))
  have south : Cap.horizontalAtHeight 0 (-1) ∈ H :=
    latitude_south_pole ▸ subset_convexHull ℝ _ (Or.inl (Set.mem_insert_of_mem _ rfl))
  have origin : Cap.horizontalAtHeight 0 0 ∈ H := by
    have combine := convex.lineMap_mem south north
      (show (1 / 2 : ℝ) ∈ Set.Icc 0 1 by constructor <;> norm_num)
    convert combine using 1
    ext i
    fin_cases i <;> norm_num [AffineMap.lineMap_apply_module', Cap.horizontalAtHeight,
      PiLp.add_apply, PiLp.smul_apply]
  have ell_eq : ell = latitudeRadius a / 2 := by simp [ell, latitudeColatitude]
  have ell_range : ell ∈ Set.Ioo 0 (π / 2) := by
    rw [ell_eq]
    exact ⟨half_pos (latitudeRadius_pos positive), by linarith only [latitudeRadius_lt small, pi_gt_three]⟩
  have cos_pos : 0 < cos ell :=
    cos_pos_of_mem_Ioo ⟨by linarith only [ell_range.1, pi_pos], ell_range.2⟩
  have sin_pos : 0 < sin ell :=
    sin_pos_of_pos_of_lt_pi ell_range.1 (by linarith only [ell_range.2, pi_pos])
  let scale := (1 + cos ell)⁻¹
  have denom : 0 < 1 + cos ell := by positivity
  have scale_pos : 0 < scale := inv_pos.mpr denom
  have scale_le : scale ≤ 1 := inv_le_one_of_one_le₀ (by linarith only [cos_pos])
  have zero_height : scale * (1 + cos ell) = 1 := inv_mul_cancel₀ denom.ne'
  let r := scale * sin ell
  have r_pos : 0 < r := mul_pos scale_pos sin_pos
  have step := (latitude_polar_size_bounds positive small).2.2.1
  have angle : π / (k : ℝ) < π / 3 := by linarith only [step, small, pi_pos]
  have k_pos := latitude_row_size_pos positive small (Nat.zero_le (latitudeStripCount a))
  have sides : 3 ≤ k := by
    by_contra! fewer
    have lower := div_le_div_of_nonneg_left pi_pos.le (Nat.cast_pos.mpr k_pos)
      (show (k : ℝ) ≤ 3 by exact_mod_cast fewer.le)
    exact angle.not_ge lower
  let lift : Plane →ᵃ[ℝ] Space := Cap.horizontalLift.toAffineMap
  have flat_ring (j : ℕ) : lift (regularRingVertex J k r j) ∈ H := by
    have base : latitudeRowSite a 0 j ∈ H :=
      subset_convexHull ℝ _ (latitudeRowSite_mem_sites a (Nat.zero_le _) _)
    have combine := convex.lineMap_mem south base ⟨scale_pos.le, scale_le⟩
    have longitude : 2 * (j : ℝ) * (π / k) = rowLongitude k j := by unfold rowLongitude; ring
    convert combine using 1
    ext i
    fin_cases i <;> simp [lift, Cap.horizontalLift, regularRingVertex, J, longitude, r,
      Complex.orthonormalBasisOneI_repr_apply, AffineMap.lineMap_apply_module', latitudeRowSite,
      latitudeSite, Cap.horizontalAtHeight, PiLp.smul_apply, PiLp.add_apply, ell, k]
    · ring
    · ring
    · dsimp only [ell] at zero_height
      linarith only [zero_height]
  let directions := regularPolygonSideDirections J sides r_pos
  let ρ := r * cos (π / (k : ℝ))
  have ρ_pos : 0 < ρ := directions.strict ⟨0, k_pos⟩ |>.trans_eq' (inner_zero_right _)
  apply zero_mem_interior_of_equatorial_disk convex ρ_pos _ north south
  intro p close
  have in_polygon : p ∈ regularSlopePolygon J k r := by
    intro i
    have h := real_inner_le_norm (directions.normal i) p
    rw [directions.unit i, one_mul] at h
    exact h.trans close.le
  rw [regularSlopePolygon_eq_iUnion_fan J sides r_pos] at in_polygon
  obtain ⟨i, in_triangle⟩ := Set.mem_iUnion.mp in_polygon
  have all : convexHull ℝ
      ({0, regularRingVertex J k r i.val, regularRingVertex J k r (i.val + 1)} : Set Plane) ⊆
        lift ⁻¹' H := convexHull_min (by
    intro q hq
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hq
    rcases hq with rfl | rfl | rfl
    · exact origin
    · exact flat_ring _
    · exact flat_ring _) (convex.affine_preimage lift)
  exact all in_triangle

theorem positiveRadialHull_latitudeHull_frontier {a : ℝ} (positive : 0 < a) (small : a ≤ π / 6) :
    positiveRadialHull (frontier (convexHull ℝ (latitudeSites a))) = ({0} : Set Space)ᶜ :=
  positiveRadialHull_frontier (convex_convexHull ℝ _) (zero_mem_interior_latitudeHull positive small)
    (isCompact_latitudeHull positive small).isBounded

end Unfoldings.FewestNets
