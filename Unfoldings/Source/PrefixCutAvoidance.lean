module

public import Unfoldings.Source.RegularUnique
public import Unfoldings.Source.PrefixUniqueness
public import Unfoldings.Source.Prefixes

/-! Every proper shortest-path prefix avoids the actual closed source cut locus. -/

@[expose] public section

namespace Unfoldings.SpatialFolding.ConvexBoundary

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {F : SpatialFolding C} (P : F.ConvexBoundary)

theorem sourcePath_proper_prefix_not_cutLocus :
    letI := P.metricSpace
    ∀ {source : C.Realization Set.univ} (_R : SourceFrame source) (p : SourcePath source)
      (t : unitInterval), t < 1 → p.path t ∉ sourceCutLocus source := by
  let := P.metricSpace
  intro source R p t before_end
  by_cases same : p.target = source
  · rw [SourcePath.eq_source_of_target_eq same t]
    exact R.source_not_mem_cutLocus
  by_cases zero : t = 0
  · simpa only [zero, Path.source] using R.source_not_mem_cutLocus
  have positive : (0 : unitInterval) < t :=
    lt_of_le_of_ne (show (0 : unitInterval) ≤ t from t.property.1) (Ne.symm zero)
  let initialPath := p.initial t
  have regular : C.IsRegularPoint Set.univ initialPath.target :=
    P.geodesic_isRegularPoint p.geodesic (Ne.symm same) t ⟨positive, before_end⟩
  have unique : ∀ q : SourcePath source, q.target = initialPath.target → q = initialPath := by
    intro q equal
    obtain ⟨x, q, geodesic⟩ := q
    change x = p.path t at equal
    subst x
    apply SourcePath.ext
    intro u
    exact P.geodesic_prefix_unique p.geodesic (Ne.symm same) t positive before_end q geodesic u
  exact P.unique_regular_endpoint_not_cutLocus R initialPath regular unique

end Unfoldings.SpatialFolding.ConvexBoundary
