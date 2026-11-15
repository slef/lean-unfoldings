module

public import Unfoldings.Geometry.SpatialEnvelopeCutRays
public import Mathlib.Topology.MetricSpace.Dilation

/-! Actual terminal bank tails are closed embedded Euclidean half-lines with exact speed. -/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialEnvelope.WholePartition

universe u

variable {I A : Type u} [Fintype I] [Nonempty I] {family : I → SpatialPlane}
  (P : WholePartition family A) [Finite A]

/-- The exact intrinsic speed is the norm of the supporting plane's rigid ray vector. -/
theorem edist_liftRayTail_eq (cuts : Set Plane) (a : A) (p d : Plane) (T : ℝ)
    (inside : ∀ t : ℝ, T ≤ t → p + t • d ∈ P.footprint a) (s t : Set.Ici T) :
    edist (P.liftRayTail cuts a p d T inside s) (P.liftRayTail cuts a p d T inside t) =
      ENNReal.ofReal (|s.val - t.val| * ‖(family (P.support a)).project.symm.linear d‖) := by
  change edist (MetricGluing.of _ _ a _) (MetricGluing.of _ _ a _) = _
  rw [(P.cut_of_isometry cuts a).edist_eq]
  change edist ((family (P.support a)).project.symm (p + s.val • d))
    ((family (P.support a)).project.symm (p + t.val • d)) = _
  have difference :
      (family (P.support a)).project.symm (p + s.val • d) -
        (family (P.support a)).project.symm (p + t.val • d) =
      (s.val - t.val) • (family (P.support a)).project.symm.linear d := by
    have linear := (family (P.support a)).project.symm.toAffineMap.linear_apply_vsub
      (p + s.val • d) (p + t.val • d)
    change (family (P.support a)).project.symm.linear
      ((p + s.val • d) - (p + t.val • d)) =
      (family (P.support a)).project.symm (p + s.val • d) -
        (family (P.support a)).project.symm (p + t.val • d) at linear
    rw [← linear]
    change (family (P.support a)).project.symm.linear
      ((p + s.val • d) - (p + t.val • d)) = _
    rw [add_sub_add_left_eq_sub, ← sub_smul, map_smul]
  rw [edist_dist, dist_eq_norm, difference, norm_smul, Real.norm_eq_abs]

/-- A nonconstant actual ray tail is a dilation of a complete real half-line. -/
def rayTailDilation (cuts : Set Plane) (a : A) (p d : Plane) (nonzero : d ≠ 0) (T : ℝ)
    (inside : ∀ t : ℝ, T ≤ t → p + t • d ∈ P.footprint a) : Set.Ici T →ᵈ P.Cut cuts where
  toFun := P.liftRayTail cuts a p d T inside
  edist_eq' := by
    refine ⟨‖(family (P.support a)).project.symm.linear d‖₊, ?_, ?_⟩
    · apply nnnorm_ne_zero_iff.mpr
      intro zero
      apply nonzero
      apply (family (P.support a)).project.symm.linear.injective
      simpa only [map_zero] using zero
    · intro s t
      rw [P.edist_liftRayTail_eq]
      change ENNReal.ofReal (|s.val - t.val| *
        ‖(family (P.support a)).project.symm.linear d‖) = _ * edist s.val t.val
      rw [edist_dist, Real.dist_eq]
      rw [ENNReal.ofReal_mul (abs_nonneg _), mul_comm]
      simp only [ofReal_norm, enorm_eq_nnnorm]

/-- The entire tail, including its initial endpoint, is closed and embedded in the cut metric. -/
theorem liftRayTail_isClosedEmbedding (cuts : Set Plane) (a : A) (p d : Plane)
    (nonzero : d ≠ 0) (T : ℝ)
    (inside : ∀ t : ℝ, T ≤ t → p + t • d ∈ P.footprint a) :
    Topology.IsClosedEmbedding (P.liftRayTail cuts a p d T inside) := by
  let : CompleteSpace (Set.Ici T) := isClosed_Ici.isComplete.completeSpace_coe
  exact Dilation.isClosedEmbedding (P.rayTailDilation cuts a p d nonzero T inside)

end Unfoldings.SpatialEnvelope.WholePartition
