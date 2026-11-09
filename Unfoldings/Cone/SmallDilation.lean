module

public import Unfoldings.Cone.Dilation

/-!
# Simultaneously shrinking finitely near cone points

Two arbitrary tangent points can be dilated into any prescribed positive
apex ball by one positive scale. Exact dilation distances make the estimate
independent of cell representatives.
-/

@[expose] public section

open scoped ENNReal NNReal

noncomputable section

namespace Unfoldings.TriangleComplex

universe u v

variable {Face : Type u} [Fintype Face] (C : TriangleComplex.{u, v} Face)
  (retain : Set C.Seam) (v : C.Vertex retain)

theorem exists_tangentDilate_near_pair (r : ℝ) (positive : 0 < r)
    (z w : C.TangentFan retain v) :
    ∃ t : ℝ≥0, t ≠ 0 ∧
      edist (C.tangentOrigin retain v) (C.tangentDilate retain v t z) < ENNReal.ofReal r ∧
      edist (C.tangentOrigin retain v) (C.tangentDilate retain v t w) < ENNReal.ofReal r := by
  let D := 1 + dist (C.tangentOrigin retain v) z + dist (C.tangentOrigin retain v) w
  have Dpos : 0 < D := by dsimp only [D]; positivity
  let t : ℝ≥0 := ⟨r / (2 * D), (div_pos positive (mul_pos (by norm_num) Dpos)).le⟩
  have tpos : 0 < (t : ℝ) := div_pos positive (mul_pos (by norm_num) Dpos)
  have product : (t : ℝ) * D = r / 2 := by
    change r / (2 * D) * D = r / 2
    field_simp [Dpos.ne']
  have radial (x : C.TangentFan retain v) :
      dist (C.tangentOrigin retain v) (C.tangentDilate retain v t x) =
        (t : ℝ) * dist (C.tangentOrigin retain v) x := by
    simpa only [C.tangentDilate_origin] using
      C.tangentDilate_dist retain v t (C.tangentOrigin retain v) x
  have dz : dist (C.tangentOrigin retain v) z ≤ D := by
    dsimp only [D]
    linarith [dist_nonneg (x := C.tangentOrigin retain v) (y := w)]
  have dw : dist (C.tangentOrigin retain v) w ≤ D := by
    dsimp only [D]
    linarith [dist_nonneg (x := C.tangentOrigin retain v) (y := z)]
  have near (x : C.TangentFan retain v) (bound : dist (C.tangentOrigin retain v) x ≤ D) :
      edist (C.tangentOrigin retain v) (C.tangentDilate retain v t x) < ENNReal.ofReal r := by
    rw [edist_dist]
    apply (ENNReal.ofReal_lt_ofReal_iff_of_nonneg dist_nonneg).mpr
    rw [radial x]
    have scaled := mul_le_mul_of_nonneg_left bound tpos.le
    linarith
  exact ⟨t, fun zero => tpos.ne' (congrArg (fun a : ℝ≥0 => (a : ℝ)) zero),
    near z dz, near w dw⟩

end Unfoldings.TriangleComplex
