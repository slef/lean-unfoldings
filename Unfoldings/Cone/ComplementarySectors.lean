module

public import Unfoldings.Cone.ReentrantSector

/-! Complementary geometric sectors cover the plane and meet exactly along their two banks. -/

@[expose] public section

noncomputable section

open scoped NNReal

namespace Unfoldings

/-- The complementary sector starts at the original sector's terminal ray. -/
def complementarySector (width : ℝ) : Set ℂ :=
  rotation (Circle.exp width) '' closedAngularSector (2 * Real.pi - width)

theorem rotate_polar_point (a b : ℝ) (r : ℝ≥0) :
    rotation (Circle.exp a) ((r : ℂ) * polarRay b) = (r : ℂ) * polarRay (a + b) := by
  change polarRay a * ((r : ℂ) * polarRay b) = _
  rw [polarRay_add]
  ring

/-- Complementarity is about the actual geometric regions, including reentrant sectors. -/
theorem closedAngularSector_union_complementary (width : ℝ) :
    closedAngularSector width ∪ complementarySector width = Set.univ := by
  apply Set.eq_univ_of_forall
  intro z
  obtain ⟨r, θ, bounds, equal⟩ := exists_polar_nonnegative_heading z
  by_cases before : θ ≤ width
  · exact Or.inl ⟨r, θ, ⟨bounds.1, before⟩, equal⟩
  · have after : width ≤ θ := (lt_of_not_ge before).le
    refine Or.inr ⟨(r : ℂ) * polarRay (θ - width),
      ⟨r, θ - width, ⟨sub_nonneg.mpr after, by linarith [bounds.2]⟩, rfl⟩, ?_⟩
    rw [rotate_polar_point, add_sub_cancel]
    exact equal.symm

/-- The common banks are the initial and terminal rays, at the original exact radius.
Interior nonoverlap does not exclude these intended closed-bank contacts. -/
theorem closedAngularSector_inter_complementary (width : ℝ)
    (positive : 0 < width) (small : width < 2 * Real.pi) :
    closedAngularSector width ∩ complementarySector width =
      Set.range (fun r : ℝ≥0 => (r : ℂ)) ∪
        Set.range (fun r : ℝ≥0 => (r : ℂ) * polarRay width) := by
  ext z
  constructor
  · rintro ⟨⟨r, θ, θbounds, θpoint⟩, ⟨v, ⟨s, φ, φbounds, φpoint⟩, last⟩⟩
    have last_point : z = (s : ℂ) * polarRay (width + φ) := by
      rw [← last, φpoint, rotate_polar_point]
    have same_radius : r = s := polar_radius_eq r s θ (width + φ) (θpoint.symm.trans last_point)
    subst s
    by_cases zero : r = 0
    · apply Or.inl
      refine ⟨0, ?_⟩
      simpa only [zero, NNReal.coe_zero, Complex.ofReal_zero, zero_mul] using θpoint.symm
    · have first_global : θ ∈ Set.Icc 0 (2 * Real.pi) :=
        ⟨θbounds.1, θbounds.2.trans small.le⟩
      have last_global : width + φ ∈ Set.Icc 0 (2 * Real.pi) :=
        ⟨by linarith [φbounds.1], by linarith [φbounds.2]⟩
      rcases polar_eq_heading_cases r zero θ (width + φ) first_global last_global
          (θpoint.symm.trans last_point) with same | ⟨first, _last⟩ | ⟨last, _first⟩
      · have at_bank : θ = width := by linarith [θbounds.2, φbounds.1]
        exact Or.inr ⟨r, by simpa only [at_bank] using θpoint.symm⟩
      · exact Or.inl ⟨r, by simpa only [first, polarRay_zero, mul_one] using θpoint.symm⟩
      · exact False.elim (small.not_ge (last ▸ θbounds.2))
  · rintro (⟨r, rfl⟩ | ⟨r, rfl⟩)
    · refine ⟨⟨r, 0, ⟨le_rfl, positive.le⟩, by simp⟩, ?_⟩
      refine ⟨(r : ℂ) * polarRay (2 * Real.pi - width),
        ⟨r, 2 * Real.pi - width, ⟨by linarith, le_rfl⟩, rfl⟩, ?_⟩
      rw [rotate_polar_point, add_sub_cancel]
      simp [polarRay]
    · refine ⟨⟨r, width, ⟨positive.le, le_rfl⟩, rfl⟩, ?_⟩
      refine ⟨(r : ℂ) * polarRay 0, ⟨r, 0, ⟨le_rfl, by linarith⟩, rfl⟩, ?_⟩
      rw [rotate_polar_point, add_zero]

end Unfoldings
