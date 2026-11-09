module

public import Unfoldings.Source.ConvexCoordinates
public import Unfoldings.Source.EndpointChart
public import Unfoldings.Source.EndpointStability
public import Unfoldings.Source.CutLocus

/-!
# A unique shortest path to a regular endpoint stays off the closed cut locus

The entire reference path is regular. Its constructed terminal chart gives
one affine endpoint formula for all nearby shortest paths. Compactness places
every shortest path to any nearby endpoint in that neighborhood. Equal
endpoint formulas and the proved source-vector injectivity exclude all ties
on a whole endpoint neighborhood, hence also exclude their closure.
-/

@[expose] public section

open scoped Topology

namespace Unfoldings.SpatialFolding.ConvexBoundary

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {F : SpatialFolding C} (P : F.ConvexBoundary)

theorem sourcePath_all_regular :
    letI := P.metricSpace
    ∀ {source : C.Realization Set.univ} (_R : SourceFrame source) (p : SourcePath source),
      C.IsRegularPoint Set.univ p.target → ∀ t, C.IsRegularPoint Set.univ (p.path t) := by
  let := P.metricSpace
  intro source R p endpoint t
  have at_source : C.IsRegularPoint Set.univ source :=
    ⟨R.radius, R.positive, R.center, ⟨R.chart⟩⟩
  by_cases same : p.target = source
  · rw [SourcePath.eq_source_of_target_eq same t]
    exact at_source
  by_cases zero : t = 0
  · simpa only [zero, Path.source] using at_source
  by_cases one : t = 1
  · simpa only [one, Path.target] using endpoint
  have positive : (0 : unitInterval) < t :=
    lt_of_le_of_ne (show (0 : unitInterval) ≤ t from t.property.1) (Ne.symm zero)
  have before : t < (1 : unitInterval) :=
    lt_of_le_of_ne (show t ≤ (1 : unitInterval) from t.property.2) one
  exact P.geodesic_isRegularPoint p.geodesic (Ne.symm same) t ⟨positive, before⟩

theorem unique_regular_endpoint_not_cutLocus :
    letI := P.metricSpace
    ∀ {source : C.Realization Set.univ} (_R : SourceFrame source) (p : SourcePath source),
      C.IsRegularPoint Set.univ p.target →
        (∀ q : SourcePath source, q.target = p.target → q = p) →
          p.target ∉ sourceCutLocus source := by
  let := P.metricSpace
  intro source R p endpoint unique
  obtain ⟨D, U, _open_D, _open_U, chart, A, W, nearby, inside, formula⟩ :=
    R.exists_endpoint_chart p (P.sourcePath_all_regular R p endpoint)
  obtain ⟨V, neighborhood, force⟩ := p.endpoint_neighborhood_of_unique unique nearby
  have no_ties : V ⊆ (nonuniqueSourcePoints source)ᶜ := by
    intro x hx nonunique
    obtain ⟨q, r, first, last, different⟩ := nonunique
    let left : SourcePath source := ⟨x, q, first⟩
    let right : SourcePath source := ⟨x, r, last⟩
    have left_inside : left ∈ W := force left hx
    have right_inside : right ∈ W := force right hx
    have equal : P.sourcePathCoordinate R left = P.sourcePathCoordinate R right :=
      (formula left left_inside).trans (formula right right_inside).symm
    have paths := P.sourcePathCoordinate_injective R equal
    apply different
    ext t
    exact congrArg (fun s : SourcePath source => s.path t) paths
  have outside_near : (nonuniqueSourcePoints source)ᶜ ∈ 𝓝 p.target :=
    Filter.mem_of_superset neighborhood no_ties
  have inside_complement : p.target ∈ interior ((nonuniqueSourcePoints source)ᶜ) :=
    mem_interior_iff_mem_nhds.mpr outside_near
  rw [interior_compl] at inside_complement
  exact inside_complement

end Unfoldings.SpatialFolding.ConvexBoundary
