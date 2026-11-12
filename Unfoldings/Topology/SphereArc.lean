module

public import Unfoldings.Topology.PathRadiusExit

/-! Simple arcs that first reach a prescribed source sphere at their final point. -/

@[expose] public section

namespace Unfoldings

variable {X : Type*} [PseudoMetricSpace X]

/-- A simple arc starting inside a source ball and meeting its sphere only at the end. -/
structure SphereArc (center start : X) (radius : ℝ) where
  finish : X
  curve : Path start finish
  injective : Function.Injective curve
  on_sphere : dist center finish = radius
  inside : ∀ s : unitInterval, s < 1 → dist center (curve s) < radius

theorem SphereArc.start_inside {center start : X} {radius : ℝ}
    (A : SphereArc center start radius) : dist center start < radius := by
  have first := A.inside 0 zero_lt_one
  rwa [A.curve.source] at first

theorem SphereArc.range_subset_closedBall {center start : X} {radius : ℝ}
    (A : SphereArc center start radius) : Set.range A.curve ⊆ Metric.closedBall center radius := by
  rintro p ⟨s, rfl⟩
  rw [Metric.mem_closedBall, dist_comm]
  rcases lt_or_eq_of_le (show s ≤ (1 : unitInterval) from s.property.2) with before | last
  · exact (A.inside s before).le
  · rw [last, A.curve.target, A.on_sphere]

/-- Stop a simple path at its first sphere crossing, preserving its initial point
and retaining only points of the original path. -/
theorem exists_sphereArc_of_injective_path {a b : X} (P : Path a b)
    (injective : Function.Injective P) (center : X) (radius : ℝ)
    (start : dist center a < radius) (finish : radius ≤ dist center b) :
    ∃ A : SphereArc center a radius, Set.range A.curve ⊆ Set.range P := by
  obtain ⟨t, _, equal, simple, inside⟩ :=
    exists_injective_initial_subpath_to_sphere P injective center radius start finish
  let A : SphereArc center a radius :=
    { finish := P t
      curve := (P.subpath 0 t).cast P.source.symm rfl
      injective := simple
      on_sphere := equal
      inside := inside }
  exact ⟨A, P.range_subpath_subset 0 t⟩

end Unfoldings
