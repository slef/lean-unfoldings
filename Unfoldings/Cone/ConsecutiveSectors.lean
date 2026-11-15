module

public import Unfoldings.Cone.ComplementarySectors

/-! Join consecutive original geometric angular sectors, retaining their shared bank ray. -/

@[expose] public section

noncomputable section

open scoped NNReal

namespace Unfoldings

/-- Consecutive sectors occupy exactly their summed real angular interval. -/
theorem closedAngularSector_union_consecutive (a b : ℝ) (first : 0 ≤ a) (last : 0 ≤ b) :
    closedAngularSector a ∪ rotation (Circle.exp a) '' closedAngularSector b =
      closedAngularSector (a + b) := by
  ext z
  constructor
  · rintro (⟨r, θ, bounds, rfl⟩ | ⟨w, ⟨r, θ, bounds, rfl⟩, rfl⟩)
    · exact ⟨r, θ, ⟨bounds.1, by linarith [bounds.2]⟩, rfl⟩
    · refine ⟨r, a + θ, ⟨by linarith [bounds.1], by linarith [bounds.2]⟩, ?_⟩
      exact rotate_polar_point a θ r
  · rintro ⟨r, θ, bounds, rfl⟩
    by_cases earlier : θ ≤ a
    · exact Or.inl ⟨r, θ, ⟨bounds.1, earlier⟩, rfl⟩
    · right
      refine ⟨(r : ℂ) * polarRay (θ - a),
        ⟨r, θ - a, ⟨by linarith, by linarith [bounds.2]⟩, rfl⟩, ?_⟩
      have placed := rotate_polar_point a (θ - a) r
      simpa only [add_sub_cancel] using placed

/-- Below a full turn, the only physical intersection is the common original equal-radius
bank ray. The apex is included at radius zero. -/
theorem closedAngularSector_inter_consecutive (a b : ℝ) (first : 0 < a) (last : 0 < b)
    (small : a + b < 2 * Real.pi) :
    closedAngularSector a ∩ rotation (Circle.exp a) '' closedAngularSector b =
      Set.range (fun r : ℝ≥0 => (r : ℂ) * polarRay a) := by
  ext z
  constructor
  · rintro ⟨⟨r, θ, θbounds, first_point⟩, ⟨w, ⟨s, φ, φbounds, last_point⟩, equal⟩⟩
    have last_placed : z = (s : ℂ) * polarRay (a + φ) := by
      rw [← equal, last_point]
      exact rotate_polar_point a φ s
    have radii : r = s := polar_radius_eq r s θ (a + φ) (first_point.symm.trans last_placed)
    subst s
    by_cases zero : r = 0
    · exact ⟨0, by rw [first_point, zero]; simp⟩
    · have θsmall : θ < 2 * Real.pi := by linarith [θbounds.2]
      have φsmall : a + φ < 2 * Real.pi := by linarith [φbounds.2]
      have equal_heading : θ = a + φ := by
        rcases polar_eq_heading_cases r zero θ (a + φ)
            ⟨θbounds.1, θsmall.le⟩ ⟨by linarith [φbounds.1], φsmall.le⟩
            (first_point.symm.trans last_placed) with same | ⟨_, bad⟩ | ⟨bad, _⟩
        · exact same
        · exact (φsmall.ne bad).elim
        · exact (θsmall.ne bad).elim
      have at_bank : θ = a := by linarith [θbounds.2, φbounds.1]
      exact ⟨r, by rw [← at_bank]; exact first_point.symm⟩
  · rintro ⟨r, rfl⟩
    refine ⟨⟨r, a, ⟨first.le, le_rfl⟩, rfl⟩, ?_⟩
    refine ⟨(r : ℂ), ⟨r, 0, ⟨le_rfl, last.le⟩, by simp⟩, ?_⟩
    have placed := rotate_polar_point a 0 r
    simpa only [polarRay_zero, mul_one, add_zero] using placed

end Unfoldings
