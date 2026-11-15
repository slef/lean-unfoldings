module

public import Unfoldings.Geometry.SpatialEnvelopeCutExcision
public import Unfoldings.Geometry.SpatialEnvelopeFaceSideBall
public import Unfoldings.Metric.PhysicalSeamFiber

/-! Equal local cut germs give unique entire original metric fibers under restoration. -/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialEnvelope.WholePartition

universe u

variable {I A : Type u} [Fintype I] [Nonempty I] {family : I → SpatialPlane}
  (P : WholePartition family A) [Finite A]

/-- Every restored metric copy has a preimage in the same original rigid-cell partition. -/
theorem forgetCut_surjective (cuts other : Set Plane) (included : other ⊆ cuts) :
    Function.Surjective (P.forgetCut cuts other included) := by
  intro y
  obtain ⟨⟨a, p⟩, rfl⟩ := MetricGluing.point_surjective (fun a => P.planarCell a)
    (P.cutGlue other) y
  exact ⟨MetricGluing.of (fun a => P.planarCell a) (P.cutGlue cuts) a p, rfl⟩

/-- A local geometric cut germ rules out every competing preimage of the actual bank copy.
This is global injectivity at the fiber, including preimages outside any chosen ball. -/
theorem forgetCut_injective_at_of_local_eq (cuts other : Set Plane) (included : other ⊆ cuts)
    (x : P.Cut cuts) {ε : ℝ} (positive : 0 < ε)
    (same : ∀ z, dist z (Cap.horizontal (P.restoreCut cuts x).val) < ε →
      (z ∈ cuts ↔ z ∈ other))
    (y : P.Cut cuts) (equal : P.forgetCut cuts other included x =
      P.forgetCut cuts other included y) : x = y := by
  let S := P.cutPhysicalSeams cuts
  let T := P.cutPhysicalSeams other
  have carrier_inclusion : ∀ a b, S.carrier a b ⊆ T.carrier a b := by
    intro a b
    exact closure_mono (Set.sdiff_subset_sdiff_right (Set.preimage_mono included))
  have agreement : ∀ a b, S.fold (P.cutIsometryEquiv cuts x) ∈ T.carrier a b →
      S.fold (P.cutIsometryEquiv cuts x) ∈ S.carrier a b := by
    intro a b member
    have physical : S.fold (P.cutIsometryEquiv cuts x) = (P.restoreCut cuts x).val :=
      P.fold_cutIsometryEquiv cuts x
    let U : Set Space := Cap.horizontal ⁻¹'
      Metric.ball (Cap.horizontal (P.restoreCut cuts x).val) ε
    have inside : S.fold (P.cutIsometryEquiv cuts x) ∈ U := by
      change dist (Cap.horizontal (S.fold (P.cutIsometryEquiv cuts x)))
        (Cap.horizontal (P.restoreCut cuts x).val) < ε
      rw [physical, dist_self]
      exact positive
    exact (MetricGluing.cutSeams_carrier_iff_of_local_eq P.spatialCell P.isClosed_spatialCell
      (Cap.horizontal ⁻¹' cuts) (Cap.horizontal ⁻¹' other)
      (Metric.isOpen_ball.preimage Cap.horizontalCLM.continuous)
      (fun z near => same (Cap.horizontal z) near) inside a b).mpr member
  apply (P.cutIsometryEquiv cuts).injective
  apply S.forget_injective_at_of_carriers T carrier_inclusion (P.cutIsometryEquiv cuts x)
    agreement (P.cutIsometryEquiv cuts y)
  exact (P.cutIsometryEquiv_forgetCut cuts other included x).symm.trans
    ((congrArg (P.cutIsometryEquiv other) equal).trans
      (P.cutIsometryEquiv_forgetCut cuts other included y))

end Unfoldings.SpatialEnvelope.WholePartition
