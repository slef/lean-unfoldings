module

public import Unfoldings.Convex.PhysicalModelMesh
public import Unfoldings.Convex.SlopeReference

/-! Affine floors cut compact sections without changing the physical roof or its supporting planes. -/

@[expose] public section

noncomputable section

namespace Unfoldings.AffineEnvelope

variable {I : Type*} [Fintype I] [Nonempty I] (support : I → Plane →ᵃ[ℝ] ℝ)
  (floor : Plane →ᵃ[ℝ] ℝ)

theorem height_sub_floor (x : Plane) :
    height (fun i => support i - floor) x = height support x - floor x := by
  obtain ⟨i, active⟩ := exists_height_eq support x
  obtain ⟨j, shifted⟩ := exists_height_eq (fun i => support i - floor) x
  apply le_antisymm
  · rw [active]
    exact height_le (fun i => support i - floor) x i
  · rw [shifted]
    change height support x - floor x ≤ support j x - floor x
    exact sub_le_sub_right (height_le support x j) _

theorem active_sub_floor_iff {i : I} {x : Plane} :
    height (fun i => support i - floor) x = (support i - floor) x ↔
      height support x = support i x := by
  rw [height_sub_floor]
  change height support x - floor x = support i x - floor x ↔ _
  exact sub_left_inj

end Unfoldings.AffineEnvelope

namespace Unfoldings.SpatialEnvelope

variable {I : Type*} [Fintype I] [Nonempty I] (family : I → SpatialPlane)
  (floor : Plane →ᵃ[ℝ] ℝ)

/-- Project the part of the roof lying above a tilted affine floor. -/
def clipAbove (Z : ℝ) : Set Plane := AffineEnvelope.clip (fun i => (family i).height - floor) Z

theorem mem_clipAbove_iff {x : Plane} {Z : ℝ} :
    x ∈ clipAbove family floor Z ↔ Z + floor x ≤ height family x := by
  change Z ≤ AffineEnvelope.height _ x ↔ _
  rw [AffineEnvelope.height_sub_floor]
  exact le_sub_iff_add_le

theorem convex_clipAbove (Z : ℝ) : Convex ℝ (clipAbove family floor Z) :=
  AffineEnvelope.convex_clip _ Z

theorem mem_interior_clipAbove {x : Plane} {Z : ℝ} (above : Z + floor x < height family x) :
    x ∈ interior (clipAbove family floor Z) := by
  apply AffineEnvelope.mem_interior_clip
  rw [AffineEnvelope.height_sub_floor]
  exact lt_sub_iff_add_lt.mpr above

end Unfoldings.SpatialEnvelope

namespace Unfoldings.SlopeEnvelope.FiniteSlopeModel

variable {E : SlopeEnvelope} (M : E.FiniteSlopeModel) (reference : Plane)

def referenceFloor : Plane →ᵃ[ℝ] ℝ :=
  (-(innerSL ℝ reference).toLinearMap).toAffineMap

theorem referenceFloor_apply (x : Plane) :
    referenceFloor reference x = -(inner ℝ x reference) := by
  change -(inner ℝ reference x) = _
  rw [real_inner_comm reference x]

/-- Compact level sets of the translated potential are physical sections of the original roof. -/
theorem clipAbove_referenceFloor_eq (level : ℝ) :
    SpatialEnvelope.clipAbove M.plane (referenceFloor reference) (-level) =
      {x | (E.recenter reference).height x ≤ level} := by
  ext x
  rw [SpatialEnvelope.mem_clipAbove_iff, M.height_eq, referenceFloor_apply,
    Set.mem_setOf_eq, E.recenter_height]
  constructor <;> intro h <;> linarith only [h]

theorem compact_clipAbove_referenceFloor (inside : reference ∈ interior E.slopes) (level : ℝ) :
    IsCompact (SpatialEnvelope.clipAbove M.plane (referenceFloor reference) (-level)) := by
  rw [M.clipAbove_referenceFloor_eq]
  exact E.compact_recenter_sublevel reference inside level

end Unfoldings.SlopeEnvelope.FiniteSlopeModel
