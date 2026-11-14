module

public import Unfoldings.Geometry.PolygonalRayFrame
public import Unfoldings.Cone.SectorFrontier

/-! Construct embedded source-rotation gaps with the exact two polygonal banks as frontier. -/

@[expose] public section

noncomputable section

open scoped NNReal

namespace Unfoldings.PolygonalRay

variable {n : ℕ} (R : PolygonalRay ℂ n) (outward : R.Outward) (nonzero : R.direction ≠ 0)

include outward nonzero in
theorem range_radialPoint : Set.range (R.radialPoint outward nonzero) = R.carrier := by
  apply Set.Subset.antisymm
  · rintro x ⟨r, rfl⟩
    exact R.radialPoint_mem outward nonzero r
  · intro x hx
    refine ⟨R.radius ⟨x, hx⟩, ?_⟩
    exact congrArg Subtype.val ((R.radialHomeomorph outward nonzero).symm_apply_apply ⟨x, hx⟩)

/-- The whole bank after a rigid source opening. -/
def rotatedCarrier (angle : ℝ) : Set ℂ :=
  (fun z => R.start + complexRotation angle (z - R.start)) '' R.carrier

include outward nonzero in
theorem bankFrame_image_realRay :
    R.bankFrame outward nonzero '' Set.range (fun r : ℝ≥0 => (r : ℂ)) = R.carrier := by
  rw [← Set.range_comp]
  simpa only [Function.comp_def, R.bankFrame_real] using R.range_radialPoint outward nonzero

include outward nonzero in
theorem bankFrame_image_rotatedRay (angle : ℝ) :
    R.bankFrame outward nonzero '' Set.range (fun r : ℝ≥0 => polarRay angle * (r : ℂ)) =
      R.rotatedCarrier angle := by
  rw [← Set.range_comp]
  simp only [Function.comp_def, R.bankFrame_rotated_ray]
  rw [rotatedCarrier, ← R.range_radialPoint outward nonzero, ← Set.range_comp]
  rfl

/-- The gap is a genuine ambient image of a closed sector. -/
def rotationGap (angle : ℝ) : Set ℂ := R.bankFrame outward nonzero '' planarSector angle

theorem isClosed_rotationGap (angle : ℝ) (sine : Real.sin angle ≠ 0) :
    IsClosed (R.rotationGap outward nonzero angle) :=
  (R.bankFrame outward nonzero).isClosedMap _ (isClosed_planarSector angle sine)

theorem frontier_rotationGap (angle : ℝ) (sine : Real.sin angle ≠ 0) :
    frontier (R.rotationGap outward nonzero angle) = R.carrier ∪ R.rotatedCarrier angle := by
  rw [rotationGap, ← (R.bankFrame outward nonzero).image_frontier,
    frontier_planarSector angle sine, Set.image_union,
    R.bankFrame_image_realRay outward nonzero, R.bankFrame_image_rotatedRay outward nonzero]

theorem rotationGap_interior_nonempty (angle : ℝ) (sine : Real.sin angle ≠ 0) :
    (interior (R.rotationGap outward nonzero angle)).Nonempty := by
  rw [rotationGap, ← (R.bankFrame outward nonzero).image_interior]
  apply Set.Nonempty.image
  rw [interior_planarSector angle sine]
  exact ⟨(1 : ℂ) + polarRay angle, 1, zero_lt_one, 1, zero_lt_one, by simp⟩

theorem rotationGap_regular_closed (angle : ℝ) (sine : Real.sin angle ≠ 0) :
    closure (interior (R.rotationGap outward nonzero angle)) =
      R.rotationGap outward nonzero angle := by
  have full : (interior (planarSector angle)).Nonempty := by
    rw [interior_planarSector angle sine]
    exact ⟨(1 : ℂ) + polarRay angle, 1, zero_lt_one, 1, zero_lt_one, by simp⟩
  rw [rotationGap, ← (R.bankFrame outward nonzero).image_interior,
    ← (R.bankFrame outward nonzero).image_closure,
    (convex_planarSector angle).closure_interior_eq_closure_of_nonempty_interior full,
    (isClosed_planarSector angle sine).closure_eq]

include outward nonzero in
/-- Distinct banks meet exactly at their shared source, at every radius. -/
theorem rotatedCarrier_inter (angle : ℝ) (distinct : polarRay angle ≠ 1) :
    R.carrier ∩ R.rotatedCarrier angle = {R.start} := by
  ext z
  constructor
  · rintro ⟨hz, x, hx, equal⟩
    have radius : dist R.start x = dist R.start z := by
      rw [← equal, dist_eq_norm', dist_eq_norm']
      simp only [add_sub_cancel_left, (complexRotation angle).norm_map]
    have same := R.eq_of_radius_eq outward nonzero hx hz radius
    subst x
    have fixed : polarRay angle * (z - R.start) = z - R.start := by
      change R.start + complexRotation angle (z - R.start) = z at equal
      rw [complexRotation_apply] at equal
      exact eq_sub_of_add_eq (by simpa only [add_comm] using equal)
    have zero : z - R.start = 0 := by
      have product : (polarRay angle - 1) * (z - R.start) = 0 := by
        rw [sub_mul, one_mul, fixed, sub_self]
      exact (mul_eq_zero.mp product).resolve_left (sub_ne_zero.mpr distinct)
    exact Set.mem_singleton_iff.mpr (sub_eq_zero.mp zero)
  · rintro rfl
    refine ⟨R.start_mem, R.start, R.start_mem, ?_⟩
    simp

end Unfoldings.PolygonalRay
