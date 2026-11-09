module

public import Unfoldings.Source.PrefixCutAvoidance
public import Unfoldings.Source.RadialDomain
public import Unfoldings.Source.OffCutCoordinates

/-!
# Actual developed radial geodesics remain in the closed-cut complement

Every proper prefix avoids the closed cut locus, and its source vector is
the exact scalar multiple of the full vector. Restrict the original shortest
path to the retained region. This constructs all radial lifts rather than
assuming them as an interface condition.
-/

@[expose] public section

noncomputable section

namespace Unfoldings.SourceFrame

variable {X : Type*} [MetricSpace X] [CompactSpace X] {source : X} (R : SourceFrame source)
  (exists_paths : Function.Surjective (SourcePath.target (source := source)))

theorem coordinate_of_sourcePath_off_cut (p : SourcePath source)
    (outside : p.target ∉ sourceCutLocus source) :
    R.coordinatesOffCutLocus exists_paths ⟨p.target, outside⟩ = R.coordinate p.path p.geodesic := by
  let q := ((SourcePath.offCutLocusHomeomorph exists_paths).symm ⟨p.target, outside⟩).val
  have target : q.target = p.target := congrArg Subtype.val
    ((SourcePath.offCutLocusHomeomorph exists_paths).apply_symm_apply ⟨p.target, outside⟩)
  have same : q = p := SourcePath.eq_of_target_eq_off_cutLocus (by rwa [target]) target
  change R.coordinate q.path q.geodesic = R.coordinate p.path p.geodesic
  rw [same]

theorem coordinatesOffCutLocus_source :
    R.coordinatesOffCutLocus exists_paths ⟨source, R.source_not_mem_cutLocus⟩ = 0 := by
  apply norm_eq_zero.mp
  rw [R.norm_coordinatesOffCutLocus, dist_self]

end Unfoldings.SourceFrame

namespace Unfoldings.SpatialFolding.ConvexBoundary

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {F : SpatialFolding C} (P : F.ConvexBoundary)

theorem exists_retained_radial :
    letI := P.metricSpace
    ∀ {source : C.Realization Set.univ} (R : SourceFrame source)
      (x : ↥((sourceCutLocus source)ᶜ)),
      ∃ path : Path (⟨source, R.source_not_mem_cutLocus⟩ : ↥((sourceCutLocus source)ᶜ)) x,
        path.IsGeodesic ∧ ∀ t,
          R.coordinatesOffCutLocus (P.sourcePath_target_surjective source) (path t) =
            (t : ℝ) • R.coordinatesOffCutLocus (P.sourcePath_target_surjective source) x := by
  let := P.metricSpace
  intro source R x
  let exists_paths := P.sourcePath_target_surjective source
  let p := ((SourcePath.offCutLocusHomeomorph exists_paths).symm x).val
  have target : p.target = x.val := congrArg Subtype.val
    ((SourcePath.offCutLocusHomeomorph exists_paths).apply_symm_apply x)
  have inside (t : unitInterval) : p.path t ∉ sourceCutLocus source := by
    by_cases last : t = 1
    · subst t
      rw [Path.target, target]
      exact x.property
    · exact P.sourcePath_proper_prefix_not_cutLocus R p t
        (lt_of_le_of_ne (show t ≤ (1 : unitInterval) from t.property.2) last)
  let q : Path source x.val := p.path.cast rfl target.symm
  let path := q.codRestrict (sourceCutLocus source)ᶜ R.source_not_mem_cutLocus x.property inside
  have geodesic : path.IsGeodesic := by
    intro s t
    change edist (p.path s) (p.path t) = edist source x.val * edist s t
    rw [← target]
    exact p.geodesic s t
  refine ⟨path, geodesic, ?_⟩
  intro t
  have initial_coordinates :=
    R.coordinate_of_sourcePath_off_cut exists_paths (p.initial t) (inside t)
  have radial := R.coordinate_initial p t
  have full : R.coordinatesOffCutLocus exists_paths x = R.coordinate p.path p.geodesic := by
    have outside : p.target ∉ sourceCutLocus source := by rw [target]; exact x.property
    have equal := R.coordinate_of_sourcePath_off_cut exists_paths p outside
    have point : (⟨p.target, outside⟩ : ↥((sourceCutLocus source)ᶜ)) = x := Subtype.ext target
    rwa [point] at equal
  exact initial_coordinates.trans (radial.trans (congrArg (fun z : Plane => (t : ℝ) • z) full.symm))

theorem retained_coordinate_image_starConvex :
    letI := P.metricSpace
    ∀ {source : C.Realization Set.univ} (R : SourceFrame source),
      StarConvex ℝ (0 : Plane)
        (Set.range (R.coordinatesOffCutLocus (P.sourcePath_target_surjective source))) := by
  let := P.metricSpace
  intro source R z member a b _ha hb sum
  obtain ⟨x, rfl⟩ := member
  let t : unitInterval := ⟨b, hb, by linarith⟩
  obtain ⟨path, _geodesic, straight⟩ := P.exists_retained_radial R x
  exact ⟨path t, by simpa only [smul_zero, zero_add] using straight t⟩

end Unfoldings.SpatialFolding.ConvexBoundary
