module

public import Unfoldings.Convex.ExteriorRay
public import Unfoldings.Geometry.PositiveSides

/-! A fixed corner-to-side assignment prevents crossings between distinct exterior directions. -/

@[expose] public section

namespace Unfoldings.SlopeEnvelope

variable (E : SlopeEnvelope)

/-- At a crossing of two open safe rays assigned to distinct supporting sides, the two
chosen active slopes must be the same shared corner of the slope polygon. -/
theorem crossing_open_rays_same_slope {p q v w u z : Plane} {c d s t : ℝ}
    (first : E.Active v p) (last : E.Active w q)
    (pside : inner ℝ u p = c) (qside : inner ℝ z q = d)
    (support_u : ∀ r ∈ E.slopes, inner ℝ u r ≤ c)
    (support_z : ∀ r ∈ E.slopes, inner ℝ z r ≤ d)
    (uunit : ‖u‖ = 1) (zunit : ‖z‖ = 1) (different : u ≠ z)
    (cpos : 0 < c) (dpos : 0 < d) (spos : 0 < s) (tpos : 0 < t)
    (crossing : v + s • u = w + t • z) : p = q := by
  have pactive : E.Active (v + s • u) p :=
    (E.active_ray_iff first pside support_u spos).mpr ⟨first, pside⟩
  have qactive : E.Active (w + t • z) q :=
    (E.active_ray_iff last qside support_z tpos).mpr ⟨last, qside⟩
  have uq := ((E.active_ray_iff first pside support_u spos).mp (crossing.symm ▸ qactive)).2
  have zp := ((E.active_ray_iff last qside support_z tpos).mp (crossing ▸ pactive)).2
  exact positive_unit_sides_intersection_unique uunit zunit different cpos dpos pside uq zp qside

/-- A deterministic side choice for every slope, in particular every polygon corner,
makes open exterior rays from distinct assigned directions disjoint. -/
theorem assigned_open_rays_disjoint (direction : Plane → Plane) {p q v w : Plane} {c d : ℝ}
    (first : E.Active v p) (last : E.Active w q)
    (pside : inner ℝ (direction p) p = c) (qside : inner ℝ (direction q) q = d)
    (support_p : ∀ r ∈ E.slopes, inner ℝ (direction p) r ≤ c)
    (support_q : ∀ r ∈ E.slopes, inner ℝ (direction q) r ≤ d)
    (punit : ‖direction p‖ = 1) (qunit : ‖direction q‖ = 1)
    (different : direction p ≠ direction q) (cpos : 0 < c) (dpos : 0 < d) :
    Disjoint {x | ∃ s : ℝ, 0 < s ∧ x = v + s • direction p}
      {x | ∃ t : ℝ, 0 < t ∧ x = w + t • direction q} := by
  apply Set.disjoint_left.mpr
  rintro x ⟨s, spos, first_eq⟩ ⟨t, tpos, last_eq⟩
  have same := E.crossing_open_rays_same_slope first last pside qside support_p support_q
    punit qunit different cpos dpos spos tpos (first_eq.symm.trans last_eq)
  exact different (congrArg direction same)

end Unfoldings.SlopeEnvelope
