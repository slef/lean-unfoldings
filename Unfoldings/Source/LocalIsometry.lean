module

public import Unfoldings.Source.EndpointChart
public import Unfoldings.Source.OffCutCoordinates

/-!
# Actual local metric compatibility of the constructed source coordinates

At a cut-complement point whose whole unique path is regular, construct the
terminal affine chart formula. The unique-path selection is continuous, so
that formula holds on a whole open endpoint neighborhood. A rigid placement
of an actual isometric chart preserves its distances exactly.
-/

@[expose] public section

open scoped Topology

noncomputable section

namespace Unfoldings.SourceFrame

variable {X : Type*} [MetricSpace X] [CompactSpace X] {source : X} (R : SourceFrame source)
  (exists_paths : Function.Surjective (SourcePath.target (source := source)))

theorem exists_off_cut_isometry_near (x : ↥((sourceCutLocus source)ᶜ))
    (regular : ∀ t, HasMetricBallChart Plane
      (((SourcePath.offCutLocusHomeomorph exists_paths).symm x).val.path t)) :
    ∃ S : Set ↥((sourceCutLocus source)ᶜ), IsOpen S ∧ x ∈ S ∧
      Isometry (fun y : S => R.coordinatesOffCutLocus exists_paths y.val) := by
  let H := SourcePath.offCutLocusHomeomorph exists_paths
  let select := fun y : ↥((sourceCutLocus source)ᶜ) => (H.symm y).val
  let p := select x
  obtain ⟨D, U, _open_D, _open_U, chart, A, W, nearby, inside, formula⟩ :=
    R.exists_endpoint_chart p regular
  have continuous : Continuous select := continuous_subtype_val.comp H.symm.continuous
  have neighborhood : select ⁻¹' W ∈ 𝓝 x := (continuous.tendsto x).eventually nearby
  obtain ⟨S, subset, open_S, at_x⟩ := mem_nhds_iff.mp neighborhood
  have target (y : ↥((sourceCutLocus source)ᶜ)) : (select y).target = y.val :=
    congrArg Subtype.val (H.apply_symm_apply y)
  have in_D (y : ↥((sourceCutLocus source)ᶜ)) (hy : y ∈ S) : y.val ∈ D := by
    have member := inside (select y) (subset hy)
    rwa [target y] at member
  have coordinates (y : ↥((sourceCutLocus source)ᶜ)) (hy : y ∈ S) :
      R.coordinatesOffCutLocus exists_paths y = A (chart ⟨y.val, in_D y hy⟩).val - R.origin := by
    have equal := formula (select y) (subset hy)
    have point : (⟨(select y).target, inside (select y) (subset hy)⟩ : D) =
        ⟨y.val, in_D y hy⟩ := Subtype.ext (target y)
    rw [point] at equal
    exact equal
  refine ⟨S, open_S, at_x, ?_⟩
  apply Isometry.of_dist_eq
  intro y z
  change dist (R.coordinatesOffCutLocus exists_paths y.val)
    (R.coordinatesOffCutLocus exists_paths z.val) = dist y.val.val z.val.val
  rw [coordinates y.val y.property, coordinates z.val z.property,
    dist_sub_right, A.isometry.dist_eq]
  exact chart.isometry.dist_eq ⟨y.val.val, in_D y.val y.property⟩
    ⟨z.val.val, in_D z.val z.property⟩

end Unfoldings.SourceFrame
