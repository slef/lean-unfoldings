module

public import Unfoldings.Metric.RigidFrameBundle

/-! Postcomposition and relative motion are continuous operations on the discrete frame covering. -/

@[expose] public section

noncomputable section

open Topology

namespace Unfoldings

namespace RigidFrame

/-- Postcompose a chart's frame by a global rigid motion. -/
def postcompose (u motion : RigidFrame) : RigidFrame := ⟨u.motion.trans motion.motion⟩

/-- The rigid motion taking the output of the first frame to that of the second. -/
def relative (u v : RigidFrame) : RigidFrame := ⟨u.motion.symm.trans v.motion⟩

theorem postcompose_relative (u v : RigidFrame) : u.postcompose (u.relative v) = v := by
  apply congrArg RigidFrame.mk
  apply AffineIsometryEquiv.ext
  intro x
  change v.motion (u.motion.symm (u.motion x)) = v.motion x
  rw [u.motion.symm_apply_apply]

theorem postcompose_injective (u : RigidFrame) : Function.Injective u.postcompose := by
  intro a b eq
  cases a with | mk a =>
  cases b with | mk b =>
  apply congrArg RigidFrame.mk
  apply AffineIsometryEquiv.ext
  intro x
  have vals := congrArg (fun v : RigidFrame => v.motion (u.motion.symm x)) eq
  change a (u.motion (u.motion.symm x)) = b (u.motion (u.motion.symm x)) at vals
  rw [u.motion.apply_symm_apply] at vals
  exact vals

theorem postcompose_assoc (u v w : RigidFrame) :
    (u.postcompose v).postcompose w = u.postcompose (v.postcompose w) := by
  apply congrArg RigidFrame.mk
  apply AffineIsometryEquiv.ext
  intro x
  rfl

/-- Comparing two frames is unchanged by the common input chart change. -/
theorem relative_postcompose_input (p u v : RigidFrame) :
    (p.postcompose u).relative (p.postcompose v) = u.relative v := by
  apply (p.postcompose u).postcompose_injective
  rw [postcompose_relative, postcompose_assoc, postcompose_relative]

end RigidFrame

namespace EuclideanAtlas

variable {X : Type*} [MetricSpace X] (A : EuclideanAtlas X)
  {Z : Type*} [TopologicalSpace Z]

local notation "Frames" => EuclideanAtlas.frameCore A

/-- When two frame families project to the same base point, their relative
rigid motion is a continuous map into the discrete rigid motions. -/
theorem continuous_relativeFrames (u v : C(Z, (Frames).TotalSpace))
    (same_base : ∀ x, (u x).1 = (v x).1) :
    Continuous (fun x => (u x).2.relative (v x).2) := by
  rw [continuous_iff_continuousAt]
  intro x
  let i := (u x).1
  let t := (Frames).localTriv i
  have at_u : u x ∈ t.source :=
    (FiberBundleCore.mem_localTriv_source Frames i (u x)).mpr ((A i).center_mem)
  have at_v : v x ∈ t.source :=
    (FiberBundleCore.mem_localTriv_source Frames i (v x)).mpr
      ((same_base x) ▸ (A i).center_mem)
  have uc : ContinuousAt (fun y => (t (u y)).2) x :=
    ((t.toOpenPartialHomeomorph.continuousAt at_u).comp u.continuous.continuousAt).snd
  have vc : ContinuousAt (fun y => (t (v y)).2) x :=
    ((t.toOpenPartialHomeomorph.continuousAt at_v).comp v.continuous.continuousAt).snd
  have operation : Continuous (fun p : RigidFrame × RigidFrame => p.1.relative p.2) :=
    continuous_of_discreteTopology
  have coordinate_eq (y : Z) : ((t (u y)).2).relative ((t (v y)).2) =
      (u y).2.relative (v y).2 := by
    let m (b : X) : RigidFrame := ⟨(A.transition b i b).symm⟩
    change ((m (u y).1).postcompose (u y).2).relative
      ((m (v y).1).postcompose (v y).2) = _
    rw [← same_base y]
    exact RigidFrame.relative_postcompose_input (m (u y).1) (u y).2 (v y).2
  exact (operation.continuousAt.comp (uc.prodMk vc)).congr (Filter.Eventually.of_forall coordinate_eq)

/-- A varying, locally constant global motion may postcompose a continuous family of frames. -/
theorem continuous_postcomposeFrames (u : C(Z, (Frames).TotalSpace)) (m : C(Z, RigidFrame)) :
    Continuous (fun x => (⟨(u x).1, (u x).2.postcompose (m x)⟩ : (Frames).TotalSpace)) := by
  rw [continuous_iff_continuousAt]
  intro x
  let i := (u x).1
  let t := (Frames).localTriv i
  have at_u : u x ∈ t.source :=
    (FiberBundleCore.mem_localTriv_source Frames i (u x)).mpr ((A i).center_mem)
  have uc : ContinuousAt (fun y => (t (u y)).2) x :=
    ((t.toOpenPartialHomeomorph.continuousAt at_u).comp u.continuous.continuousAt).snd
  have operation : Continuous (fun p : RigidFrame × RigidFrame => p.1.postcompose p.2) :=
    continuous_of_discreteTopology
  have coord (y : Z) : (t (⟨(u y).1, (u y).2.postcompose (m y)⟩ : (Frames).TotalSpace)).2 =
      ((t (u y)).2).postcompose (m y) := by
    let d : RigidFrame := ⟨(A.transition (u y).1 i (u y).1).symm⟩
    change d.postcompose ((u y).2.postcompose (m y)) = (d.postcompose (u y).2).postcompose (m y)
    exact (RigidFrame.postcompose_assoc d _ _).symm
  apply (FiberBundle.continuousAt_totalSpace RigidFrame _).mpr
  refine ⟨?_, ?_⟩
  · change ContinuousAt (fun y => (u y).1) x
    exact ((Frames).continuous_proj.comp u.continuous).continuousAt
  ·
    change ContinuousAt
      (fun y => (t (⟨(u y).1, (u y).2.postcompose (m y)⟩ : (Frames).TotalSpace)).2) x
    exact (operation.continuousAt.comp (uc.prodMk m.continuous.continuousAt)).congr
      (Filter.Eventually.of_forall (fun y => (coord y).symm))

end EuclideanAtlas
end Unfoldings
