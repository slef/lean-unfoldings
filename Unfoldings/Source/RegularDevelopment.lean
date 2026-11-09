module

public import Unfoldings.Source.InteriorHomeomorph
public import Unfoldings.Source.ConvexLocalIsometry

/-!
# An actual nonoverlapping source development of the flat retained region

The constructed coordinates are continuous, injective and locally isometric
at every point of the regular closed-cut complement. Actual geodesics from
the source remain in this region and develop to straight radial segments.
The homeomorphism with the planar domain interior has already been proved.
Boundary completion and the finite cut graph are separate constructions.
-/

@[expose] public section

noncomputable section

namespace Unfoldings.SourceFrame

variable {X : Type*} [MetricSpace X] [CompactSpace X] {source : X}
  (R : SourceFrame source)
  (exists_paths : Function.Surjective (SourcePath.target (source := source)))

theorem local_isometry_regularCoordinates_of_offCut (x : sourceRegularRegion source)
    (local_isometry : ∃ S : Set ↥((sourceCutLocus source)ᶜ), IsOpen S ∧
      regularRegionToOffCut x ∈ S ∧
        Isometry (fun y : S => R.coordinatesOffCutLocus exists_paths y.val)) :
    ∃ T : Set (sourceRegularRegion source), IsOpen T ∧ x ∈ T ∧
      Isometry (fun y : T => R.regularCoordinates exists_paths y.val) := by
  obtain ⟨S, open_S, inside, isometry⟩ := local_isometry
  let T : Set (sourceRegularRegion source) :=
    (regularRegionToOffCut (source := source)) ⁻¹' S
  let map (y : T) : S := ⟨regularRegionToOffCut y.val, y.property⟩
  have open_T : IsOpen T := open_S.preimage
    (regularRegionToOffCut_isometry (source := source)).continuous
  refine ⟨T, open_T, inside, ?_⟩
  intro y z
  exact isometry (map y) (map z)

end Unfoldings.SourceFrame

namespace Unfoldings.SpatialFolding.ConvexBoundary

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {F : SpatialFolding C} (P : F.ConvexBoundary)

theorem regular_source_coordinates_local_isometry :
    letI := P.metricSpace
    ∀ {source : C.Realization Set.univ} (R : SourceFrame source) (x : sourceRegularRegion source),
      ∃ T : Set (sourceRegularRegion source), IsOpen T ∧ x ∈ T ∧
        Isometry (fun y : T =>
          R.regularCoordinates (P.sourcePath_target_surjective source) y.val) := by
  let := P.metricSpace
  intro source R x
  exact R.local_isometry_regularCoordinates_of_offCut _ x
    (P.source_coordinates_local_isometry_at_regular R (regularRegionToOffCut x) x.property.2)

theorem exists_regular_retained_radial :
    letI := P.metricSpace
    ∀ {source : C.Realization Set.univ} (R : SourceFrame source) (x : sourceRegularRegion source),
      ∃ path : Path R.regularSourcePoint x, path.IsGeodesic ∧ ∀ t,
        R.regularCoordinates (P.sourcePath_target_surjective source) (path t) =
          (t : ℝ) • R.regularCoordinates (P.sourcePath_target_surjective source) x := by
  let := P.metricSpace
  intro source R x
  obtain ⟨path, geodesic, straight⟩ := P.exists_retained_radial R (regularRegionToOffCut x)
  let original := path.map continuous_subtype_val
  have original_geodesic : original.IsGeodesic := geodesic.map_isometry Subtype.val
    (isometry_subtype_coe (s := (sourceCutLocus source)ᶜ))
  let q : SourcePath source := ⟨x.val, original, original_geodesic⟩
  have regular := P.sourcePath_all_regular R q x.property.2
  have inside (t : unitInterval) : original t ∈ sourceRegularRegion source :=
    ⟨(path t).property, regular t⟩
  let restricted := original.codRestrict (sourceRegularRegion source)
    R.regularSourcePoint.property x.property inside
  exact ⟨restricted, original_geodesic.codRestrict _ _ _ inside, straight⟩

theorem regular_source_coordinates_nonoverlap :
    letI := P.metricSpace
    ∀ {source : C.Realization Set.univ} (R : SourceFrame source),
      Function.Injective (R.regularCoordinates (P.sourcePath_target_surjective source)) := by
  let := P.metricSpace
  intro source R
  exact R.regularCoordinates_injective _ (P.sourcePathCoordinate_injective R)

end Unfoldings.SpatialFolding.ConvexBoundary
