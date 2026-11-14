module

public import Unfoldings.Convex.ExteriorRay
public import Unfoldings.Geometry.AffineMaximum

/-! Boundary potential, strict selected region, and safe-ray avoidance of interior slopes. -/

@[expose] public section

noncomputable section

namespace Unfoldings.SlopeEnvelope

variable (E : SlopeEnvelope)

/-- Strict excess over the boundary potential means that every active slope is interior. -/
theorem strict_boundary_iff (nonempty : (frontier E.slopes).Nonempty) (v : Plane) :
    (E.boundaryEnvelope nonempty).height v < E.height v ↔
      ∀ p, E.Active v p → p ∈ interior E.slopes := by
  constructor
  · intro strict p active
    by_contra outside
    have boundary : p ∈ frontier E.slopes :=
      ⟨subset_closure active.1, outside⟩
    have equal := E.active_boundary nonempty active boundary
    exact (ne_of_lt strict) (equal.2.trans active.2.symm)
  · intro interior
    have bound := E.boundary_height_le nonempty v
    by_contra not_strict
    have equal := le_antisymm bound (le_of_not_gt not_strict)
    obtain ⟨p, hp, active⟩ := (E.boundaryEnvelope nonempty).exists_height_eq v
    have original : E.Active v p :=
      ⟨E.compact.isClosed.frontier_subset hp, equal.symm.trans active⟩
    exact hp.2 (interior p original)

/-- A nonzero supporting direction exposes no interior slope. -/
theorem interior_slope_lt {u q : Plane} {c : ℝ} (nonzero : u ≠ 0)
    (support : ∀ r ∈ E.slopes, inner ℝ u r ≤ c) (inside : q ∈ interior E.slopes) :
    inner ℝ u q < c := by
  have functional_nonzero : innerSL ℝ u ≠ 0 := by
    intro zero
    have value := congrArg (fun L : Plane →L[ℝ] ℝ => L u) zero
    change inner ℝ u u = 0 at value
    exact nonzero (inner_self_eq_zero.mp value)
  exact supporting_functional_lt_on_interior (innerSL ℝ u) functional_nonzero E.slopes c
    support q inside

/-- Open exterior rays have no active interior slope, including at original edges or vertices. -/
theorem active_ray_not_interior {p v u q : Plane} {c t : ℝ} (active : E.Active v p)
    (side : inner ℝ u p = c) (support : ∀ r ∈ E.slopes, inner ℝ u r ≤ c)
    (direction : u ≠ 0) (time : 0 < t) (along : E.Active (v + t • u) q) :
    q ∉ interior E.slopes := by
  intro inside
  have on_side := ((E.active_ray_iff active side support time).mp along).2
  exact (ne_of_lt (E.interior_slope_lt direction support inside)) on_side

end Unfoldings.SlopeEnvelope
