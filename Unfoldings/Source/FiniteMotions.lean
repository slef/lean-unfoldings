module

public import Unfoldings.Source.RoutePropagation

/-!
# Only finitely many actual source-face motions occur

Fix one actual face copy of the source. Each shortest path has a face route
with at most twice the original face count plus one pieces. Within a piece
the actual motion is fixed, and each crossing uses a bounded seam word from
a finite type. Bounded finite-choice reachability therefore covers every
actual retained face motion. No finite-image hypothesis is assumed.
-/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialFolding.ConvexBoundary

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {F : SpatialFolding C} (P : F.ConvexBoundary)

def sourceMotionCandidates :
    letI := P.metricSpace
    {source : C.Realization Set.univ} → (R : SourceFrame source) →
      C.PointFiber Set.univ source → Set (Plane ≃ᵃⁱ[ℝ] Plane) := by
  let := P.metricSpace
  intro source R base
  exact finiteReach (C.boundedWordPlacement (N := Fintype.card Face))
    (P.sourceFiberMotion R source R.source_not_mem_cutLocus base) (2 * Fintype.card Face + 2)

theorem finite_sourceMotionCandidates :
    letI := P.metricSpace
    ∀ {source : C.Realization Set.univ} (R : SourceFrame source)
      (base : C.PointFiber Set.univ source),
      (P.sourceMotionCandidates R base).Finite := by
  let := P.metricSpace
  intro source R base
  exact finite_finiteReach _ _ _

theorem sourceTaggedMotion_mem_candidates :
    letI := P.metricSpace
    ∀ {source : C.Realization Set.univ} (R : SourceFrame source)
      (base : C.PointFiber Set.univ source) (a : C.Total)
      (outside : MetricGluing.point C.Cell (C.glue Set.univ) a ∉ sourceCutLocus source),
      P.sourceTaggedMotion R a outside ∈ P.sourceMotionCandidates R base := by
  let := P.metricSpace
  intro source R base a outside
  obtain ⟨p, target⟩ := P.sourcePath_target_surjective source
    (MetricGluing.point C.Cell (C.glue Set.univ) a)
  have endpoint_off : p.target ∉ sourceCutLocus source := target.symm ▸ outside
  obtain ⟨route, bound⟩ := F.exists_geodesic_faceRoute P.embedded p.geodesic
  let finish_copy : C.PointFiber Set.univ p.target := ⟨a, target.symm⟩
  have reachable := P.sourceMotion_reachable_along_faceRoute R p.path route
    (P.sourcePath_avoids_cut_of_target_off_cut R p endpoint_off)
    base finish_copy R.source_not_mem_cutLocus endpoint_off
  change P.sourceTaggedMotion R a outside ∈
    finiteReach (C.boundedWordPlacement (N := Fintype.card Face))
      (P.sourceFiberMotion R source R.source_not_mem_cutLocus base) (route.steps + 1) at reachable
  exact finiteReach_mono _ _ (by omega) reachable

theorem exists_finite_actual_source_motions :
    letI := P.metricSpace
    ∀ {source : C.Realization Set.univ} (R : SourceFrame source),
      ∃ M : Set (Plane ≃ᵃⁱ[ℝ] Plane), M.Finite ∧
        ∀ (a : C.Total)
          (outside : MetricGluing.point C.Cell (C.glue Set.univ) a ∉ sourceCutLocus source),
          P.sourceTaggedMotion R a outside ∈ M := by
  let := P.metricSpace
  intro source R
  obtain ⟨a, image⟩ := MetricGluing.point_surjective C.Cell (C.glue Set.univ) source
  let base : C.PointFiber Set.univ source := ⟨a, image⟩
  exact ⟨P.sourceMotionCandidates R base, P.finite_sourceMotionCandidates R base,
    P.sourceTaggedMotion_mem_candidates R base⟩

end Unfoldings.SpatialFolding.ConvexBoundary
