module

public import Unfoldings.Source.PathNeighborhood
public import Unfoldings.Path.AffineSamples
public import Unfoldings.Metric.RigidChartTransition
public import Unfoldings.Basic
public import Mathlib.Analysis.InnerProductSpace.Convex

/-!
# Continuing a straight family through an actual overlapping chart

A trace records a proved affine coordinate identity for all shortest paths in
a neighborhood of one reference path. To cross into the next chart, construct
the rigid transition on a whole common ball and retain two distinct sample
times in that ball. Compact-time chart stability keeps all nearby paths in
the required domains. Geodesic straightness then extends the identity over
the whole next interval.
-/

@[expose] public section

open scoped Topology

noncomputable section

namespace Unfoldings

variable {X : Type*} [MetricSpace X] {source : X}

structure AffineChartTrace (p : SourcePath source)
    (line : SourcePath source → ℝ →ᵃ[ℝ] Plane) (r s : unitInterval) where
  domain : Set X
  target : Set Plane
  open_domain : IsOpen domain
  open_target : IsOpen target
  chart : domain ≃ᵢ target
  place : Plane →ᵃⁱ[ℝ] Plane
  nearby : Set (SourcePath source)
  neighborhood : nearby ∈ 𝓝 p
  inside : ∀ q ∈ nearby, ∀ t ∈ Set.Icc r s, q.path t ∈ domain
  straight : ∀ q (hq : q ∈ nearby), ∀ t (ht : t ∈ Set.Icc r s),
    place (chart ⟨q.path t, inside q hq t ht⟩).val = line q (t : ℝ)

namespace AffineChartTrace

variable {p : SourcePath source} {line : SourcePath source → ℝ →ᵃ[ℝ] Plane}
  {r s t : unitInterval}

theorem extend (old : AffineChartTrace p line r s) (ordered : r < s) (next_ordered : s < t)
    {G : Set X} {V : Set Plane} (next : G ≃ᵢ V) (open_G : IsOpen G) (open_V : IsOpen V)
    (next_inside : ∀ v ∈ Set.Icc s t, p.path v ∈ G) :
    Nonempty (AffineChartTrace p line s t) := by
  have in_old : p ∈ old.nearby := mem_of_mem_nhds old.neighborhood
  have at_old := old.inside p in_old s ⟨ordered.le, le_rfl⟩
  have at_next := next_inside s ⟨le_rfl, next_ordered.le⟩
  obtain ⟨δ, positive, in_G, in_D, A, agreement⟩ := exists_rigid_chart_transition next old.chart
    open_G old.open_domain open_V old.open_target (p.path s) at_next at_old
  have near : p.path ⁻¹' Metric.ball (p.path s) δ ∈ 𝓝 s :=
    (Metric.isOpen_ball.preimage p.path.continuous).mem_nhds (Metric.mem_ball_self positive)
  obtain ⟨l, h, ⟨ls, sh⟩, overlap⟩ :=
    (mem_nhds_iff_exists_Ioo_subset' ⟨r, ordered⟩ ⟨t, next_ordered⟩).mp near
  obtain ⟨u, lower, us⟩ := exists_between (max_lt ordered ls)
  have ru : r < u := (le_max_left _ _).trans_lt lower
  have lu : l < u := (le_max_right _ _).trans_lt lower
  have overlap_inside : ∀ v ∈ Set.Icc u s, p.path v ∈ Metric.ball (p.path s) δ :=
    fun v hv => overlap ⟨lu.trans_le hv.1, hv.2.trans_lt sh⟩
  have whole_inside : ∀ v ∈ Set.Icc u t, p.path v ∈ G := by
    intro v hv
    by_cases before : v ≤ s
    · exact in_G (overlap_inside v ⟨hv.1, before⟩)
    · exact next_inside v ⟨le_of_not_ge before, hv.2⟩
  let nearby : Set (SourcePath source) :=
    (old.nearby ∩ {q | ∀ v ∈ Set.Icc u t, q.path v ∈ G}) ∩
      {q | ∀ v ∈ Set.Icc u s, q.path v ∈ Metric.ball (p.path s) δ}
  have neighborhood : nearby ∈ 𝓝 p :=
    Filter.inter_mem (Filter.inter_mem old.neighborhood
      (p.eventually_inside_on_compact isCompact_Icc open_G whole_inside))
      (p.eventually_inside_on_compact isCompact_Icc Metric.isOpen_ball overlap_inside)
  have inside : ∀ q ∈ nearby, ∀ v ∈ Set.Icc s t, q.path v ∈ G :=
    fun q hq v hv => hq.1.2 v ⟨us.le.trans hv.1, hv.2⟩
  let place := old.place.comp A
  let f : G → Plane := fun x => place (next x).val
  have isometry : Isometry f := old.place.isometry.comp (A.isometry.comp
    ((isometry_subtype_coe (s := V)).comp next.isometry))
  have straight : ∀ q (hq : q ∈ nearby), ∀ v (hv : v ∈ Set.Icc s t),
      place (next ⟨q.path v, inside q hq v hv⟩).val = line q (v : ℝ) := by
    intro q hq v hv
    have in_next : ∀ z ∈ Set.Icc u t, q.path z ∈ G := hq.1.2
    have samples (z : unitInterval) (hz : z ∈ Set.Icc u s) :
        f ⟨q.path z, in_next z ⟨hz.1, hz.2.trans next_ordered.le⟩⟩ = line q (z : ℝ) := by
      have near_z := hq.2 z hz
      have rigid := congrArg old.place (agreement ⟨q.path z, near_z⟩)
      exact rigid.trans (old.straight q hq.1.1 z ⟨ru.le.trans hz.1, hz.2⟩)
    have full := q.geodesic.coordinates_eq_affine_of_two_samples f isometry
      (us.trans next_ordered) in_next (line q) us.ne
      ⟨le_rfl, (us.trans next_ordered).le⟩ ⟨us.le, next_ordered.le⟩
      (samples u ⟨le_rfl, us.le⟩) (samples s ⟨us.le, le_rfl⟩)
    exact full v ⟨us.le.trans hv.1, hv.2⟩
  exact ⟨⟨G, V, open_G, open_V, next, place, nearby, neighborhood, inside, straight⟩⟩

end AffineChartTrace
end Unfoldings
