module

public import Unfoldings.Metric.EuclideanCocycle
public import Mathlib.Topology.Covering.Basic

/-! The discrete bundle of locally continued rigid Euclidean frames. -/

@[expose] public section

noncomputable section

namespace Unfoldings

/-- Rigid motions with the discrete topology, recording continuation rather than deformation. -/
structure RigidFrame where
  motion : Plane ≃ᵃⁱ[ℝ] Plane

instance : TopologicalSpace RigidFrame := ⊥
instance : DiscreteTopology RigidFrame := ⟨rfl⟩

namespace EuclideanAtlas

variable {X : Type*} [MetricSpace X] (A : EuclideanAtlas X)

def changeFrame (i j x : X) (frame : RigidFrame) : RigidFrame :=
  ⟨(A.transition i j x).symm.trans frame.motion⟩

theorem changeFrame_continuousOn (i j : X) :
    ContinuousOn (fun p : X × RigidFrame => A.changeFrame i j p.1 p.2)
      (((A i).domain ∩ (A j).domain) ×ˢ Set.univ) := by
  rw [continuousOn_iff_continuous_domRestrict]
  let B := ((A i).domain ∩ (A j).domain) ×ˢ (Set.univ : Set RigidFrame)
  let base : B → ↥((A i).domain ∩ (A j).domain) := fun p => ⟨p.val.1, p.property.1⟩
  have base_continuous : Continuous base :=
    (continuous_fst.comp continuous_subtype_val).subtype_mk _
  have transition_continuous :
      Continuous (fun p : B => (⟨A.transition i j p.val.1⟩ : RigidFrame)) :=
    (((A.transition_locallyConstant i j).comp RigidFrame.mk).continuous).comp base_continuous
  have motion_continuous : Continuous (fun p : B => p.val.2) :=
    continuous_snd.comp continuous_subtype_val
  have compose : Continuous (fun p : RigidFrame × RigidFrame =>
      (⟨p.1.motion.symm.trans p.2.motion⟩ : RigidFrame)) := continuous_of_discreteTopology
  exact compose.comp (transition_continuous.prodMk motion_continuous)

def frameCore : FiberBundleCore X X RigidFrame where
  baseSet i := (A i).domain
  isOpen_baseSet i := (A i).open_domain
  indexAt := id
  mem_baseSet_at x := (A x).center_mem
  coordChange := A.changeFrame
  coordChange_self i x member frame := by
    change RigidFrame.mk ((A.transition i i x).symm.trans frame.motion) = frame
    rw [A.transition_self i x member]
    cases frame
    rfl
  continuousOn_coordChange := A.changeFrame_continuousOn
  coordChange_comp i j k x member frame := by
    apply congrArg RigidFrame.mk
    apply AffineIsometryEquiv.ext
    intro z
    change frame.motion ((A.transition i j x).symm ((A.transition j k x).symm z)) =
      frame.motion ((A.transition i k x).symm z)
    apply congrArg frame.motion
    rw [A.transition_symm i j x member.1,
      A.transition_symm j k x ⟨member.1.2, member.2⟩,
      A.transition_symm i k x ⟨member.1.1, member.2⟩]
    exact congrArg (fun M : Plane ≃ᵃⁱ[ℝ] Plane => M z)
      (A.transition_comp k j i x ⟨⟨member.2, member.1.2⟩, member.1.1⟩)

/-- Rigid frame germs form a genuine covering of the Euclidean metric space. -/
theorem frameCore_isCoveringMap : IsCoveringMap A.frameCore.proj :=
  FiberBundle.isCoveringMap

end EuclideanAtlas
end Unfoldings
