module

public import Unfoldings.Metric.EuclideanDevelopment
public import Unfoldings.Metric.OpenEuclideanAtlas
public import Mathlib.Analysis.Convex.Contractible

/-! The interior of a flat metric disk has a global planar local isometry, allowing overlap. -/

@[expose] public section

noncomputable section

namespace Unfoldings

variable {X : Type*} [MetricSpace X]

def diskInterior (disk : X ≃ₜ Metric.closedBall (0 : Plane) 1) : Set X :=
  {x | ‖(disk x).val‖ < 1}

theorem isOpen_diskInterior (disk : X ≃ₜ Metric.closedBall (0 : Plane) 1) :
    IsOpen (diskInterior disk) :=
  isOpen_lt (continuous_norm.comp (continuous_subtype_val.comp disk.continuous)) continuous_const

def diskInteriorEquiv (disk : X ≃ₜ Metric.closedBall (0 : Plane) 1) :
    diskInterior disk ≃ Metric.ball (0 : Plane) 1 where
  toFun x := ⟨(disk x.val).val, by
    change dist (disk x.val).val 0 < 1
    rw [dist_zero_right]
    exact x.property⟩
  invFun y := ⟨disk.symm ⟨y.val, Metric.ball_subset_closedBall y.property⟩, by
    change ‖(disk (disk.symm _)).val‖ < 1
    rw [disk.apply_symm_apply]
    simpa only [Metric.mem_ball, dist_zero_right] using y.property⟩
  left_inv x := Subtype.ext (disk.symm_apply_apply x.val)
  right_inv y := by
    apply Subtype.ext
    change (disk (disk.symm ⟨y.val, Metric.ball_subset_closedBall y.property⟩)).val = y.val
    exact congrArg Subtype.val (disk.apply_symm_apply _)

def diskInteriorHomeomorph (disk : X ≃ₜ Metric.closedBall (0 : Plane) 1) :
    diskInterior disk ≃ₜ Metric.ball (0 : Plane) 1 where
  toEquiv := diskInteriorEquiv disk
  continuous_toFun := (continuous_subtype_val.comp
    (disk.continuous.comp continuous_subtype_val)).subtype_mk _
  continuous_invFun :=
    (disk.symm.continuous.comp (continuous_subtype_val.subtype_mk _)).subtype_mk _

theorem diskInterior_simplyConnectedSpace (disk : X ≃ₜ Metric.closedBall (0 : Plane) 1) :
    SimplyConnectedSpace (diskInterior disk) := by
  let : ContractibleSpace (Metric.ball (0 : Plane) 1) :=
    (convex_ball (0 : Plane) 1).contractibleSpace ⟨0, Metric.mem_ball_self zero_lt_one⟩
  exact (diskInteriorHomeomorph disk).toHomotopyEquiv.simplyConnectedSpace

theorem diskInterior_locallyPathConnectedSpace (disk : X ≃ₜ Metric.closedBall (0 : Plane) 1) :
    LocallyPathConnectedSpace (diskInterior disk) := by
  let : LocallyPathConnectedSpace (Metric.ball (0 : Plane) 1) :=
    Metric.isOpen_ball.locallyPathConnectedSpace
  exact (diskInteriorHomeomorph disk).symm.locallyPathConnectedSpace

/-- Flatness is intrinsic whole-ball regularity throughout the actual open disk. -/
theorem exists_diskInterior_development (disk : X ≃ₜ Metric.closedBall (0 : Plane) 1)
    (regular : ∀ x ∈ diskInterior disk, HasMetricBallChart Plane x) :
    ∃ f : diskInterior disk → Plane, ∀ x, ∃ r > 0,
      Isometry (fun y : Metric.ball x r => f y.val) := by
  let := diskInterior_simplyConnectedSpace disk
  let := diskInterior_locallyPathConnectedSpace disk
  let A := EuclideanAtlas.onOpen (diskInterior disk) (isOpen_diskInterior disk) regular
  let root : diskInterior disk :=
    (diskInteriorHomeomorph disk).symm ⟨0, Metric.mem_ball_self zero_lt_one⟩
  exact A.exists_local_isometry root ⟨AffineIsometryEquiv.refl ℝ Plane⟩

end Unfoldings
