module

public import Unfoldings.Cone.PlacedAngularSectorChart
public import Mathlib.Topology.UnitInterval

/-! A whole original sector chart with its two arclength-parametrized bank rays. -/

@[expose] public section

noncomputable section

open scoped ENNReal

namespace Unfoldings

variable {X : Type*} [EMetricSpace X] (x : X) (angle : ℝ)
  (mark : Bool → unitInterval → X) (length : Bool → ℝ)

/-- The initial bank is on the positive axis and the terminal bank is on the
ray at the named angle, measured in the same original distance parameter. -/
structure MarkedSectorGerm where
  sector : CenteredSectorGerm x angle
  distance (b : Bool) (t : unitInterval) :
    edist (mark b t) x = ENNReal.ofReal (t.val * length b)
  trace (b : Bool) (t : unitInterval)
    (near : edist (mark b t) x < ENNReal.ofReal sector.radius) :
    (sector.chart ⟨mark b t, near⟩).val.val =
      (t.val * length b) • polarRay (if b then angle else 0)

end Unfoldings
