module

public import Unfoldings.Metric.Quotient
public import Unfoldings.Path.Distance
public import Unfoldings.Path.EMetricShortest
public import Unfoldings.Path.EMetricGeodesic

/-!
# Continuous paths for the constructed gluing metric

If the original cells have paths no longer than their own distances, finite
routes give continuous paths of no greater length. Thus route distance agrees
with continuous-path distance. Compact finite families then have actual
shortest paths between every pair of points at finite distance.
-/

@[expose] public section

open scoped ENNReal

noncomputable section

namespace Unfoldings.MetricGluing

universe u v

variable {ι : Type u} (E : ι → Type v) [∀ i, MetricSpace (E i)]
  (cellPath : ∀ i, ∀ a b : E i, Path a b)
  (cellLength : ∀ i a b, (cellPath i a b).eLength ≤ edist a b)

include cellPath cellLength

theorem exists_step_path (glue : Total E → Total E → Prop) (a b : Total E)
    (finite : stepCost E glue a b ≠ ⊤) :
    ∃ p : Path (point E glue a) (point E glue b), p.eLength ≤ stepCost E glue a b := by
  classical
  by_cases related : glue a b ∨ glue b a
  · have equal : point E glue a = point E glue b :=
      related.elim (point_eq_of_glue E) (fun h => (point_eq_of_glue E h).symm)
    have zero_path {x y : Realization E glue} (same : x = y) :
        ∃ p : Path x y, p.eLength = 0 := by
      subst y
      exact ⟨Path.refl x, Path.eLength_refl x⟩
    obtain ⟨p, hp⟩ := zero_path equal
    exact ⟨p, hp.le.trans bot_le⟩
  · obtain ⟨i, a⟩ := a
    obtain ⟨j, b⟩ := b
    by_cases same : i = j
    · subst j
      let p := (cellPath i a b).map (of_lipschitz E glue i).continuous
      have bound : p.eLength ≤ (cellPath i a b).eLength := by
        simpa only [ENNReal.coe_one, one_mul] using
          (cellPath i a b).eLength_map_le (of_lipschitz E glue i)
      refine ⟨p, ?_⟩
      have cost : stepCost E glue ⟨i, a⟩ ⟨i, b⟩ = edist a b := by
        simp [stepCost, related, faceCost]
      rw [cost]
      exact bound.trans (cellLength i a b)
    · exact (finite (by simp [stepCost, related, faceCost, same])).elim

theorem exists_route_path (glue : Total E → Total E → Prop) {a b : Total E}
    (route : Route (Total E) a b)
    (finite : route.length (stepCost E glue) ≠ ⊤) :
    ∃ p : Path (point E glue a) (point E glue b), p.eLength ≤ route.length (stepCost E glue) := by
  induction route with
  | nil a => exact ⟨Path.refl _, by simp [Route.length]⟩
  | cons a b tail ih =>
    obtain ⟨step_finite, tail_finite⟩ := ENNReal.add_ne_top.mp finite
    obtain ⟨first, first_bound⟩ := exists_step_path E cellPath cellLength glue a b step_finite
    obtain ⟨rest, rest_bound⟩ := ih tail_finite
    refine ⟨first.trans rest, ?_⟩
    rw [Path.eLength_trans]
    exact add_le_add first_bound rest_bound

theorem exists_path_eLength_lt (glue : Total E → Total E → Prop) (a b : Total E)
    {r : ℝ≥0∞} (less : edist (point E glue a) (point E glue b) < r) :
    ∃ p : Path (point E glue a) (point E glue b), p.eLength < r := by
  change (⨅ route : Route (Total E) a b, route.length (stepCost E glue)) < r at less
  obtain ⟨route, short⟩ := iInf_lt_iff.mp less
  obtain ⟨p, bound⟩ := exists_route_path E cellPath cellLength glue route (ne_top_of_lt short)
  exact ⟨p, bound.trans_lt short⟩

/-- The finite-route construction is the actual continuous-path intrinsic metric. -/
theorem eDistance_eq_edist (glue : Total E → Total E → Prop) (x y : Realization E glue) :
    Path.eDistance x y = edist x y := by
  obtain ⟨a, rfl⟩ := point_surjective E glue x
  obtain ⟨b, rfl⟩ := point_surjective E glue y
  apply le_antisymm
  · apply le_of_forall_gt
    intro r less
    obtain ⟨p, short⟩ := exists_path_eLength_lt E cellPath cellLength glue a b less
    exact (p.eDistance_le_eLength).trans_lt short
  · exact Path.edist_le_eDistance _ _

/-- Finite-distance points in a compact gluing are joined by a finite shortest path. -/
theorem exists_distance_path [Finite ι] [∀ i, CompactSpace (E i)]
    (glue : Total E → Total E → Prop) (x y : Realization E glue) (finite : edist x y ≠ ⊤) :
    ∃ p : Path x y, p.IsLengthMinimizing ∧ p.eLength = edist x y ∧
      LipschitzWith p.eLength.toNNReal p := by
  obtain ⟨a, rfl⟩ := point_surjective E glue x
  obtain ⟨b, rfl⟩ := point_surjective E glue y
  obtain ⟨first, short⟩ := exists_path_eLength_lt E cellPath cellLength glue a b
    (lt_top_iff_ne_top.mpr finite)
  obtain ⟨p, minimal, pfinite, speed⟩ := first.exists_lengthMinimizing_emetric (ne_top_of_lt short)
  exact ⟨p, minimal,
    minimal.eLength_eq_eDistance.trans (eDistance_eq_edist E cellPath cellLength glue _ _), speed⟩

/-- Compact gluing of geodesic cells is geodesic on every finite-distance component. -/
theorem exists_geodesic [Finite ι] [∀ i, CompactSpace (E i)]
    (glue : Total E → Total E → Prop) (x y : Realization E glue) (finite : edist x y ≠ ⊤) :
    ∃ p : Path x y, p.IsGeodesic := by
  obtain ⟨p, minimal, length, speed⟩ := exists_distance_path E cellPath cellLength glue x y finite
  exact ⟨p, p.isGeodesic_of_eLength_eq_of_lipschitz_emetric (length ▸ finite) length speed⟩

end Unfoldings.MetricGluing
