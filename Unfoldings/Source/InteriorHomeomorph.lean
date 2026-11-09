module

public import Unfoldings.Source.RegularRegion
public import Unfoldings.Source.ConvexDomainInterior
public import Unfoldings.Source.RetainedRadials

/-!
# The flat retained surface is homeomorphic to the actual planar domain interior

The forward map is the constructed source-coordinate function. The inverse
is the already constructed continuous endpoint projection from the whole
compact domain. Exact interior membership proves both maps have the required
domains, and actual shortest-path identities prove both round trips.
-/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialFolding.ConvexBoundary

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {F : SpatialFolding C} (P : F.ConvexBoundary)

def sourceInteriorHomeomorph :
    letI := P.metricSpace
    {source : C.Realization Set.univ} → (R : SourceFrame source) →
      sourceRegularRegion source ≃ₜ interior R.domain := by
  let := P.metricSpace
  intro source R
  let exists_paths := P.sourcePath_target_surjective source
  let injective := P.sourcePathCoordinate_injective R
  let H := R.coordinateHomeomorph injective
  let select := fun x : sourceRegularRegion source =>
    ((SourcePath.offCutLocusHomeomorph exists_paths).symm (regularRegionToOffCut x)).val
  have target (x : sourceRegularRegion source) : (select x).target = x.val :=
    congrArg Subtype.val ((SourcePath.offCutLocusHomeomorph exists_paths).apply_symm_apply _)
  have forward_inside (x : sourceRegularRegion source) :
      R.regularCoordinates exists_paths x ∈ interior R.domain := by
    change R.coordinate (select x).path (select x).geodesic ∈ interior R.domain
    apply (P.source_vector_mem_interior_iff R (select x)).mpr
    rw [target]
    exact ⟨x.property.2, x.property.1⟩
  let forward (x : sourceRegularRegion source) : interior R.domain :=
    ⟨R.regularCoordinates exists_paths x, forward_inside x⟩
  let include_point (z : interior R.domain) : R.domain := ⟨z.val, interior_subset z.property⟩
  let path (z : interior R.domain) := H.symm (include_point z)
  have image (z : interior R.domain) : R.coordinate (path z).path (path z).geodesic = z.val :=
    congrArg Subtype.val (H.apply_symm_apply (include_point z))
  have inverse_inside (z : interior R.domain) : (path z).target ∈ sourceRegularRegion source := by
    have near : R.coordinate (path z).path (path z).geodesic ∈ interior R.domain := by
      rw [image z]
      exact z.property
    have facts := (P.source_vector_mem_interior_iff R (path z)).mp near
    exact ⟨facts.2, facts.1⟩
  let inverse (z : interior R.domain) : sourceRegularRegion source :=
    ⟨(path z).target, inverse_inside z⟩
  have left_inverse (x : sourceRegularRegion source) : inverse (forward x) = x := by
    apply Subtype.ext
    have point : include_point (forward x) = H (select x) := Subtype.ext rfl
    change (H.symm (include_point (forward x))).target = x.val
    rw [point, H.symm_apply_apply]
    exact target x
  have right_inverse (z : interior R.domain) : forward (inverse z) = z := by
    apply Subtype.ext
    have coordinate := R.coordinate_of_sourcePath_off_cut exists_paths (path z)
      (inverse_inside z).1
    exact coordinate.trans (image z)
  have continuous_forward : Continuous forward :=
    (R.continuous_regularCoordinates exists_paths).subtype_mk _
  have continuous_inclusion : Continuous include_point := continuous_subtype_val.subtype_mk _
  have continuous_inverse : Continuous inverse :=
    ((R.continuous_projection injective).comp continuous_inclusion).subtype_mk _
  exact ⟨⟨forward, inverse, left_inverse, right_inverse⟩, continuous_forward, continuous_inverse⟩

@[simp] theorem sourceInteriorHomeomorph_apply :
    letI := P.metricSpace
    ∀ {source : C.Realization Set.univ} (R : SourceFrame source) (x : sourceRegularRegion source),
      (P.sourceInteriorHomeomorph R x).val =
        R.regularCoordinates (P.sourcePath_target_surjective source) x := by
  let := P.metricSpace
  intro source R x
  rfl

end Unfoldings.SpatialFolding.ConvexBoundary
