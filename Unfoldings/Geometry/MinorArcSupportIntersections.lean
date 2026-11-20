module

public import Unfoldings.Geometry.MinorArcConnectivity

/-! A transverse minor arc meets at most two boundary points of a convex spherical cell. -/

@[expose] public section

noncomputable section

namespace Unfoldings

/-- If an arc has three ordered points in one supporting hemisphere, equality
at the middle point forces the full arc into the supporting great circle. -/
theorem minorArc_support_zero_at_middle {u v : Space} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (not_antipodal : u + v ≠ 0) (f : Space →ₗ[ℝ] ℝ)
    {a b c : ℝ} (ha : a ∈ Set.Ioo 0 1) (hb : b ∈ Set.Ioo 0 1)
    (hc : c ∈ Set.Ioo 0 1) (ab : a < b) (bc : b < c)
    (first : 0 ≤ f (NormedSpace.normalize ((1 - a) • u + a • v)))
    (middle : f (NormedSpace.normalize ((1 - b) • u + b • v)) = 0)
    (last : 0 ≤ f (NormedSpace.normalize ((1 - c) • u + c • v))) :
    f u = 0 ∧ f v = 0 := by
  let s (t : ℝ) := (1 - t) * f u + t * f v
  have value (t : ℝ) :
      f (NormedSpace.normalize ((1 - t) • u + t • v)) =
        ‖(1 - t) • u + t • v‖⁻¹ * s t := by
    simp only [NormedSpace.normalize, map_smul, map_add, smul_eq_mul, s]
  have norm_pos (t : ℝ) (ht : t ∈ Set.Ioo 0 1) : 0 < ‖(1 - t) • u + t • v‖⁻¹ :=
    inv_pos.mpr (norm_pos_iff.mpr (minorArc_chord_ne_zero hu hv not_antipodal ht))
  rw [value a] at first
  rw [value b] at middle
  rw [value c] at last
  have first' := nonneg_of_mul_nonneg_right first (norm_pos a ha)
  have last' := nonneg_of_mul_nonneg_right last (norm_pos c hc)
  have middle' := (mul_eq_zero.mp middle).resolve_left (norm_pos b hb).ne'
  have part (t t' : ℝ) : s t - s t' = (t - t') * (f v - f u) := by dsimp [s]; ring
  have slope_nonneg : 0 ≤ f v - f u := by
    have h : 0 ≤ s c - s b := by simpa only [middle', sub_zero] using last'
    rw [part] at h
    exact nonneg_of_mul_nonneg_right h (sub_pos.mpr bc)
  have slope_nonpos : f v - f u ≤ 0 := by
    have h : s b - s a ≤ 0 := sub_nonpos.mpr (by simpa only [middle'] using first')
    rw [part] at h
    exact nonpos_of_mul_nonpos_right h (sub_pos.mpr ab)
  have endpoints : f u = f v := by linarith only [slope_nonneg, slope_nonpos]
  have zero : f u = 0 := by
    dsimp [s] at middle'
    rw [← endpoints] at middle'
    linarith only [middle']
  exact ⟨zero, endpoints ▸ zero⟩

/-- Among three ordered arc points in a spherical convex intersection, the middle
point is strictly inside every supporting hemisphere not containing the full arc. -/
theorem minorArc_middle_strict_of_crossing_supports {I : Type*} {u v : Space}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (not_antipodal : u + v ≠ 0)
    (f : I → Space →ₗ[ℝ] ℝ) (transverse : ∀ i, f i u ≠ 0 ∨ f i v ≠ 0)
    {a b c : ℝ} (ha : a ∈ Set.Ioo 0 1) (hb : b ∈ Set.Ioo 0 1)
    (hc : c ∈ Set.Ioo 0 1) (ab : a < b) (bc : b < c)
    (left : ∀ i, 0 ≤ f i (NormedSpace.normalize ((1 - a) • u + a • v)))
    (middle : ∀ i, 0 ≤ f i (NormedSpace.normalize ((1 - b) • u + b • v)))
    (right : ∀ i, 0 ≤ f i (NormedSpace.normalize ((1 - c) • u + c • v))) :
    ∀ i, 0 < f i (NormedSpace.normalize ((1 - b) • u + b • v)) := by
  intro i
  refine lt_of_le_of_ne (middle i) ?_
  intro zero
  exact (transverse i).elim
    (fun h => h (minorArc_support_zero_at_middle hu hv not_antipodal (f i)
      ha hb hc ab bc (left i) zero.symm (right i)).1)
    (fun h => h (minorArc_support_zero_at_middle hu hv not_antipodal (f i)
      ha hb hc ab bc (left i) zero.symm (right i)).2)

end Unfoldings
