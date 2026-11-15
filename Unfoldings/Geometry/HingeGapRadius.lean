module

public import Unfoldings.Geometry.HingeGapPrefix
public import Unfoldings.Geometry.RotationSweepUniqueness

/-! An outward hinge sweep stays beyond its source-centered hinge circle. -/

@[expose] public section

noncomputable section

open scoped NNReal

namespace Unfoldings.PolygonalRay

variable {n : ℕ} (R : PolygonalRay ℂ n)

theorem rotateSuffix_hinge (hinge : Fin (n + 1)) (angle : ℝ) :
    (R.rotateSuffix hinge angle).chain.vertex hinge = R.chain.vertex hinge :=
  R.chain.rotateSuffix_vertex_le hinge angle hinge le_rfl

theorem rotateSuffix_direction_ne_zero (hinge : Fin (n + 1)) (angle : ℝ)
    (nonzero : R.direction ≠ 0) : (R.rotateSuffix hinge angle).direction ≠ 0 := by
  change complexRotation angle R.direction ≠ 0
  simpa only [map_zero] using (complexRotation angle).injective.ne nonzero

variable (hinge : Fin (n + 1)) (outward : (R.suffix hinge).Outward)
  (nonzero : R.direction ≠ 0) (angle : ℝ) (positive : 0 < angle) (small : angle < Real.pi)
  (radial : ∀ θ ∈ Set.Icc 0 angle, (R.rotateSuffix hinge θ).Outward)

include radial in
/-- Every intermediate actual suffix stays beyond the original source-centered hinge radius. -/
theorem rotatedSuffix_radius_ge_hinge {θ : ℝ} (bounds : θ ∈ Set.Icc 0 angle) {z : ℂ}
    (bank : z ∈ (R.suffix hinge).rotatedCarrier θ) :
    dist R.start (R.chain.vertex hinge) ≤ dist R.start z := by
  have member : z ∈ ((R.rotateSuffix hinge θ).suffix hinge).carrier := by
    rwa [R.rotateSuffix_suffix_carrier]
  have lower := (R.rotateSuffix hinge θ).suffix_radius_ge_hinge (radial θ bounds) hinge member
  simpa only [R.rotateSuffix_start, R.rotateSuffix_hinge] using lower

include positive small radial in
/-- The entire hinge gap avoids the smaller open source-centered ball. -/
theorem hingeGap_radius_ge_hinge {z : ℂ}
    (member : z ∈ (R.suffix hinge).rotationGap outward nonzero angle) :
    dist R.start (R.chain.vertex hinge) ≤ dist R.start z := by
  obtain ⟨θ, bounds, bank⟩ :=
    ((R.suffix hinge).mem_rotationGap_iff_sweep outward nonzero angle positive small z).mp member
  exact R.rotatedSuffix_radius_ge_hinge hinge angle radial bounds bank

include positive small radial in
/-- The closed hinge-radius ball touches the actual gap only at its hinge. -/
theorem hingeGap_inter_closedBall :
    (R.suffix hinge).rotationGap outward nonzero angle ∩
      Metric.closedBall R.start (dist R.start (R.chain.vertex hinge)) = {R.chain.vertex hinge} := by
  ext z
  constructor
  · rintro ⟨member, near⟩
    have upper : dist R.start z ≤ dist R.start (R.chain.vertex hinge) := by
      simpa only [Metric.mem_closedBall, dist_comm] using near
    have lower :=
      R.hingeGap_radius_ge_hinge hinge outward nonzero angle positive small radial member
    have radius := le_antisymm upper lower
    obtain ⟨θ, bounds, bank⟩ :=
      ((R.suffix hinge).mem_rotationGap_iff_sweep outward nonzero angle positive small z).mp member
    have suffix_member : z ∈ ((R.rotateSuffix hinge θ).suffix hinge).carrier := by
      rwa [R.rotateSuffix_suffix_carrier]
    have whole : z ∈ (R.rotateSuffix hinge θ).carrier := by
      rw [(R.rotateSuffix hinge θ).carrier_split hinge]
      exact Or.inr suffix_member
    have same := (R.rotateSuffix hinge θ).eq_of_radius_eq (radial θ bounds)
      (R.rotateSuffix_direction_ne_zero hinge θ nonzero) whole
      (Or.inl ((R.rotateSuffix hinge θ).chain.vertex_mem_path_range hinge)) (by
        simpa only [R.rotateSuffix_start, R.rotateSuffix_hinge] using radius)
    exact same.trans (R.rotateSuffix_hinge hinge θ)
  · rintro rfl
    constructor
    · apply ((R.suffix hinge).mem_rotationGap_iff_sweep outward nonzero angle positive small _).mpr
      refine ⟨0, ⟨le_rfl, positive.le⟩, (R.suffix hinge).start, (R.suffix hinge).start_mem, ?_⟩
      simp
    · exact Metric.mem_closedBall.mpr (le_of_eq (dist_comm _ _))

/-- The unique point on an intermediate whole bank at the prescribed original-source radius. -/
def hingeCirclePoint (r : ℝ≥0) (θ : Set.Icc 0 angle) : ℂ :=
  (R.rotateSuffix hinge θ.val).radialPoint (radial θ.val θ.property)
    (R.rotateSuffix_direction_ne_zero hinge θ.val nonzero) r

include nonzero radial in
@[simp] theorem hingeCirclePoint_radius (r : ℝ≥0) (θ : Set.Icc 0 angle) :
    dist R.start (R.hingeCirclePoint hinge nonzero angle radial r θ) = (r : ℝ) := by
  have radius := (R.rotateSuffix hinge θ.val).norm_radialPoint_sub_start
    (radial θ.val θ.property) (R.rotateSuffix_direction_ne_zero hinge θ.val nonzero) r
  rw [R.rotateSuffix_start] at radius
  exact (dist_eq_norm' _ _).trans radius

include nonzero radial in
/-- Above the hinge radius, each circle contact lies on the moved suffix itself. -/
theorem hingeCirclePoint_mem_suffix (r : ℝ≥0)
    (higher : dist R.start (R.chain.vertex hinge) < (r : ℝ)) (θ : Set.Icc 0 angle) :
    R.hingeCirclePoint hinge nonzero angle radial r θ ∈ (R.suffix hinge).rotatedCarrier θ.val := by
  have member := (R.rotateSuffix hinge θ.val).radialPoint_mem (radial θ.val θ.property)
    (R.rotateSuffix_direction_ne_zero hinge θ.val nonzero) r
  rw [(R.rotateSuffix hinge θ.val).carrier_split hinge] at member
  rcases member with fixed | suffix_member
  · have upper := (R.rotateSuffix hinge θ.val).prefix_radius_le_hinge
      (radial θ.val θ.property) hinge fixed
    rw [R.rotateSuffix_start, R.rotateSuffix_hinge] at upper
    have radius := R.hingeCirclePoint_radius hinge nonzero angle radial r θ
    exact ((not_lt_of_ge upper) (radius.symm ▸ higher)).elim
  · rwa [R.rotateSuffix_suffix_carrier] at suffix_member

include outward positive small radial in
/-- Distinct intermediate angles give distinct original-source circle contacts above the hinge. -/
theorem hingeCirclePoint_injective (r : ℝ≥0)
    (higher : dist R.start (R.chain.vertex hinge) < (r : ℝ)) :
    Function.Injective (R.hingeCirclePoint hinge nonzero angle radial r) := by
  intro θ ψ equal
  have first := R.hingeCirclePoint_mem_suffix hinge nonzero angle radial r higher θ
  have last := R.hingeCirclePoint_mem_suffix hinge nonzero angle radial r higher ψ
  rw [← equal] at last
  have nonapex : R.hingeCirclePoint hinge nonzero angle radial r θ ≠ (R.suffix hinge).start := by
    intro same
    have radius := R.hingeCirclePoint_radius hinge nonzero angle radial r θ
    rw [same, R.suffix_start] at radius
    exact higher.ne radius
  apply Subtype.ext
  exact (R.suffix hinge).rotatedCarrier_contact_angle outward nonzero
    (small.trans (by linarith [Real.pi_pos])) θ.property ψ.property first last nonapex

include outward positive small radial in
/-- Every point of the actual source-circle slice occurs at one intermediate opening angle. -/
theorem range_hingeCirclePoint (r : ℝ≥0)
    (higher : dist R.start (R.chain.vertex hinge) < (r : ℝ)) :
    Set.range (R.hingeCirclePoint hinge nonzero angle radial r) =
      (R.suffix hinge).rotationGap outward nonzero angle ∩
        {z | dist R.start z = (r : ℝ)} := by
  ext z
  constructor
  · rintro ⟨θ, rfl⟩
    refine ⟨?_, R.hingeCirclePoint_radius hinge nonzero angle radial r θ⟩
    exact ((R.suffix hinge).mem_rotationGap_iff_sweep outward nonzero angle positive small _).mpr
      ⟨θ.val, θ.property, R.hingeCirclePoint_mem_suffix hinge nonzero angle radial r higher θ⟩
  · rintro ⟨member, radius⟩
    obtain ⟨θ, bounds, bank⟩ :=
      ((R.suffix hinge).mem_rotationGap_iff_sweep outward nonzero angle positive small z).mp member
    let t : Set.Icc 0 angle := ⟨θ, bounds⟩
    refine ⟨t, ?_⟩
    have whole : z ∈ (R.rotateSuffix hinge θ).carrier := by
      rw [(R.rotateSuffix hinge θ).carrier_split hinge]
      apply Or.inr
      rwa [R.rotateSuffix_suffix_carrier]
    have actual := (R.rotateSuffix hinge θ).radialPoint_mem (radial θ bounds)
      (R.rotateSuffix_direction_ne_zero hinge θ nonzero) r
    apply (R.rotateSuffix hinge θ).eq_of_radius_eq (radial θ bounds)
      (R.rotateSuffix_direction_ne_zero hinge θ nonzero) actual whole
    rw [R.rotateSuffix_start]
    change dist R.start (R.hingeCirclePoint hinge nonzero angle radial r t) = dist R.start z
    exact (R.hingeCirclePoint_radius hinge nonzero angle radial r t).trans radius.symm

end Unfoldings.PolygonalRay
