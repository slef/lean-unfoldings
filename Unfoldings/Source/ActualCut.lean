module

public import Unfoldings.Source.ConeLeaves
public import Unfoldings.Source.CutProjection
public import Unfoldings.Source.CutIntrinsic
public import Unfoldings.Source.CompletedRadials

/-!
# The source disk cuts exactly the closure of shortest-path ties

The cone-leaf theorem removes the temporary distinction between the singular
slit set and the closed source cut locus. The retained surface is exactly the
cut-locus complement, and the completed disk's boundary projects exactly to
that cut locus. All metric and development data remain the constructed ones.
-/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialFolding.ConvexBoundary

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {F : SpatialFolding C} (P : F.ConvexBoundary)

theorem sourceRegularRegion_eq_cutComplement :
    letI := P.metricSpace
    ∀ {source : C.Realization Set.univ} (_R : SourceFrame source),
      sourceRegularRegion source = (sourceCutLocus source)ᶜ := by
  let := P.metricSpace
  intro source R
  rw [sourceRegularRegion_eq_compl_slitSet, P.sourceSlitSet_eq_sourceCutLocus R]

theorem regular_of_not_mem_sourceCutLocus :
    letI := P.metricSpace
    ∀ {source : C.Realization Set.univ} (_R : SourceFrame source)
      {x : C.Realization Set.univ}, x ∉ sourceCutLocus source → C.IsRegularPoint Set.univ x := by
  let := P.metricSpace
  intro source R x outside
  by_contra singular
  exact outside (P.singular_point_mem_sourceCutLocus R x singular)

theorem source_vector_mem_interior_iff_off_cut :
    letI := P.metricSpace
    ∀ {source : C.Realization Set.univ} (R : SourceFrame source) (p : SourcePath source),
      R.coordinate p.path p.geodesic ∈ interior R.domain ↔ p.target ∉ sourceCutLocus source := by
  let := P.metricSpace
  intro source R p
  rw [P.source_vector_mem_interior_iff R p]
  exact ⟨And.right, fun outside => ⟨P.regular_of_not_mem_sourceCutLocus R outside, outside⟩⟩

theorem sourceCutCompletion_boundary_projection_cutLocus :
    letI := P.metricSpace
    ∀ {source : C.Realization Set.univ} (R : SourceFrame source),
      R.cutCompletionProjection (P.sourcePathCoordinate_injective R) ''
        {z : R.cutCompletion | z.val ∈ frontier R.domain} = sourceCutLocus source := by
  let := P.metricSpace
  intro source R
  rw [P.sourceCutCompletion_boundary_projection R, P.sourceSlitSet_eq_sourceCutLocus R]

def sourceCutComplementHomeomorph :
    letI := P.metricSpace
    {source : C.Realization Set.univ} → (R : SourceFrame source) →
      ↥((sourceCutLocus source)ᶜ) ≃ₜ R.cutInterior := by
  let := P.metricSpace
  intro source R
  exact (Homeomorph.setCongr (P.sourceRegularRegion_eq_cutComplement R).symm).trans
    (P.sourceCutSurfaceHomeomorph R)

theorem source_coordinates_local_isometry :
    letI := P.metricSpace
    ∀ {source : C.Realization Set.univ} (R : SourceFrame source)
      (x : ↥((sourceCutLocus source)ᶜ)),
      ∃ S : Set ↥((sourceCutLocus source)ᶜ), IsOpen S ∧ x ∈ S ∧
        Isometry (fun y : S => R.coordinatesOffCutLocus
          (P.sourcePath_target_surjective source) y.val) := by
  let := P.metricSpace
  intro source R x
  exact P.source_coordinates_local_isometry_at_regular R x
    (P.regular_of_not_mem_sourceCutLocus R x.property)

/-- The metric and topological source disk, constructed from the convex boundary alone.
Finite polygonal descriptions are supplied in `Source.PolygonalPieces`;
the graph/tree characterization is separate. -/
theorem source_disk_properties :
    letI := P.metricSpace
    ∀ {source : C.Realization Set.univ} (R : SourceFrame source),
      CompactSpace R.cutCompletion ∧ CompleteSpace R.cutCompletion ∧
      Nonempty (R.cutCompletion ≃ₜ Metric.closedBall (0 : Plane) 1) ∧
      Function.Injective (PolygonalPoint.val (s := R.domain)) ∧
      LipschitzWith 1 (PolygonalPoint.val (s := R.domain)) ∧
      LipschitzWith 1 (R.cutCompletionProjection (P.sourcePathCoordinate_injective R)) ∧
      Function.Surjective (R.cutCompletionProjection (P.sourcePathCoordinate_injective R)) ∧
      R.cutCompletionProjection (P.sourcePathCoordinate_injective R) ''
        {z : R.cutCompletion | z.val ∈ frontier R.domain} = sourceCutLocus source := by
  let := P.metricSpace
  intro source R
  exact ⟨P.sourceCutCompletion_compact R, P.sourceCutCompletion_complete R,
    ⟨P.sourceCutDiskHomeomorph R⟩, R.cutCompletion_development_injective,
    R.cutCompletion_development_lipschitz, P.sourceCutCompletion_projection_lipschitz R,
    R.cutCompletionProjection_surjective _ (P.sourcePath_target_surjective source),
    P.sourceCutCompletion_boundary_projection_cutLocus R⟩

end Unfoldings.SpatialFolding.ConvexBoundary
