module

public import Unfoldings.Convex.ExteriorRayCompatibility
public import Unfoldings.Geometry.BoundarySupportDirection

/-! Construct canonical safe exterior rays at any finite pool of exterior roots. -/

@[expose] public section

noncomputable section

namespace Unfoldings.SlopeEnvelope

/-- Geometric ray data. The same slope always uses the same assigned outward direction. -/
structure ExteriorPlan (E : SlopeEnvelope) (V : Type*) where
  point : V → Plane
  point_injective : Function.Injective point
  slope : V → Plane
  direction : Plane → Plane
  active : ∀ v, E.Active (point v) (slope v)
  unit : ∀ v, ‖direction (slope v)‖ = 1
  positive : ∀ v, 0 < inner ℝ (direction (slope v)) (slope v)
  support : ∀ v q, q ∈ E.slopes →
    inner ℝ (direction (slope v)) q ≤ inner ℝ (direction (slope v)) (slope v)

variable (E : SlopeEnvelope)

/-- Boundary-envelope equality is the actual exterior-location condition. Unit rays and
the globally consistent corner choices are constructed from convexity and an interior origin. -/
theorem exists_exteriorPlan {V : Type*} (point : V → Plane)
    (injective : Function.Injective point) (convex : Convex ℝ E.slopes)
    (origin : (0 : Plane) ∈ interior E.slopes)
    (boundary_nonempty : (frontier E.slopes).Nonempty)
    (exterior : ∀ v, (E.boundaryEnvelope boundary_nonempty).height (point v) = E.height (point v)) :
    ∃ R : E.ExteriorPlan V, R.point = point := by
  choose slope boundary equal using
    (fun v => (E.boundaryEnvelope boundary_nonempty).exists_height_eq (point v))
  let direction := boundarySupportDirection convex origin
  refine ⟨{
    point := point
    point_injective := injective
    slope := slope
    direction := direction
    active v := ⟨E.compact.isClosed.frontier_subset (boundary v), (exterior v).symm.trans (equal v)⟩
    unit v := (boundarySupportDirection_spec convex origin (boundary v)).1
    positive v := (boundarySupportDirection_spec convex origin (boundary v)).2.1
    support v := (boundarySupportDirection_spec convex origin (boundary v)).2.2 }, rfl⟩

namespace ExteriorPlan

variable {E} {V : Type*} (R : E.ExteriorPlan V)

def rate (v : V) : ℝ := inner ℝ (R.direction (R.slope v)) (R.slope v)

def ray (v : V) (t : ℝ) : Plane := R.point v + t • R.direction (R.slope v)

def openRay (v : V) : Set Plane := {x | ∃ t : ℝ, 0 < t ∧ x = R.ray v t}

theorem height_ray (v : V) {t : ℝ} (time : 0 ≤ t) :
    E.height (R.ray v t) = E.height (R.point v) + t * R.rate v :=
  E.height_ray (R.active v) rfl (R.support v) time

theorem strict_ray (v : V) {t : ℝ} (time : 0 < t) :
    E.height (R.point v) < E.height (R.ray v t) := by
  rw [R.height_ray v time.le]
  exact lt_add_of_pos_right _ (mul_pos time (R.positive v))

theorem open_rays_disjoint_of_direction_ne {v w : V}
    (different : R.direction (R.slope v) ≠ R.direction (R.slope w)) :
    Disjoint (R.openRay v) (R.openRay w) :=
  E.assigned_open_rays_disjoint R.direction (R.active v) (R.active w) rfl rfl
    (R.support v) (R.support w) (R.unit v) (R.unit w) different (R.positive v) (R.positive w)

/-- An open ray meets another root only at a strictly larger common potential. -/
def Contact (v w : V) : Prop := R.point w ∈ R.openRay v

theorem contact_height_lt {v w : V} (contact : R.Contact v w) :
    E.height (R.point v) < E.height (R.point w) := by
  obtain ⟨t, positive, equal⟩ := contact
  rw [equal]
  exact R.strict_ray v positive

theorem contact_irrefl (v : V) : ¬ R.Contact v v := by
  intro contact
  exact lt_irrefl _ (R.contact_height_lt contact)

end ExteriorPlan
end Unfoldings.SlopeEnvelope
