module

public import Unfoldings.Cone.SurfaceTags
public import Unfoldings.Metric.Lipschitz
public import Mathlib.Analysis.Normed.Affine.AddTorsor

/-!
# Radial dilations of constructed tangent fans

Scale actual wedge coordinates about their apices, prove compatibility with
every radial seam, and descend through the route metric. Scale zero is included.
-/

@[expose] public section

open scoped ENNReal NNReal

noncomputable section

namespace Unfoldings.TriangleComplex

universe u v

variable {Face : Type u} [Fintype Face] (C : TriangleComplex.{u, v} Face)
  (retain : Set C.Seam) (v : C.Vertex retain)

def tangentCellDilate (c : C.CornerAt retain v) (t : ℝ≥0)
    (x : C.TangentCell retain v c) : C.TangentCell retain v c :=
  ⟨AffineMap.lineMap (C.tangentApex retain v c).val x.val (t : ℝ),
    (C.triangle c.val.1).lineMap_mem_cornerWedge c.val.2 x.property t.coe_nonneg⟩

theorem tangentCellDilate_lipschitz (c : C.CornerAt retain v) (t : ℝ≥0) :
    LipschitzWith t (C.tangentCellDilate retain v c t) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  change dist (AffineMap.lineMap (C.tangentApex retain v c).val x.val (t : ℝ))
    (AffineMap.lineMap (C.tangentApex retain v c).val y.val (t : ℝ)) ≤
      (t : ℝ) * dist x.val y.val
  rw [← AffineMap.homothety_eq_lineMap, ← AffineMap.homothety_eq_lineMap,
    dist_homothety, Real.norm_eq_abs, abs_of_nonneg t.coe_nonneg]

theorem tangentCellDilate_radial (c : C.CornerAt retain v) (t : ℝ≥0)
    (x : C.Cell c.val.1) (s : ℝ) (nonnegative : 0 ≤ s) :
    C.tangentCellDilate retain v c t (C.tangentRadialPoint retain v c x s nonnegative) =
      C.tangentRadialPoint retain v c x ((t : ℝ) * s)
        (mul_nonneg t.coe_nonneg nonnegative) := by
  apply Subtype.ext
  exact AffineMap.lineMap_lineMap_right _ _ s (t : ℝ)

theorem tangentCellDilate_compatible (t : ℝ≥0) (a b : C.TangentTotal retain v)
    (joined : C.tangentGlue retain v a b) :
    C.tangentFaceMap retain v a.1 (C.tangentCellDilate retain v a.1 t a.2) =
      C.tangentFaceMap retain v b.1 (C.tangentCellDilate retain v b.1 t b.2) := by
  obtain ⟨s, x, r, nonnegative, rfl, rfl⟩ := joined
  apply MetricGluing.point_eq_of_glue
  refine ⟨s, x, (t : ℝ) * r, mul_nonneg t.coe_nonneg nonnegative, ?_, ?_⟩
  · apply congrArg (Sigma.mk (C.tangentLeft retain v s))
    exact C.tangentCellDilate_radial retain v _ t _ r nonnegative
  · apply congrArg (Sigma.mk (C.tangentRight retain v s))
    exact C.tangentCellDilate_radial retain v _ t _ r nonnegative

theorem tangentCellDilate_face_lipschitz (t : ℝ≥0) (c : C.CornerAt retain v) :
    LipschitzWith t (fun x =>
      C.tangentFaceMap retain v c (C.tangentCellDilate retain v c t x)) := by
  change LipschitzWith t
    (C.tangentFaceMap retain v c ∘ C.tangentCellDilate retain v c t)
  simpa only [one_mul] using (C.tangentFaceMap_lipschitz retain v c).comp
    (C.tangentCellDilate_lipschitz retain v c t)

/-- The descended dilation uses a positive majorant also at scale zero. -/
def tangentDilate (t : ℝ≥0) : C.TangentFan retain v → C.TangentFan retain v :=
  MetricGluing.liftLipschitz (C.TangentCell retain v) (C.tangentGlue retain v)
    (max 1 t) (lt_of_lt_of_le zero_lt_one (le_max_left _ _))
    (fun c x => C.tangentFaceMap retain v c (C.tangentCellDilate retain v c t x))
    (fun c => (C.tangentCellDilate_face_lipschitz retain v t c).weaken (le_max_right _ _))
    (C.tangentCellDilate_compatible retain v t)

@[simp] theorem tangentDilate_faceMap (t : ℝ≥0) (c : C.CornerAt retain v)
    (x : C.TangentCell retain v c) :
    C.tangentDilate retain v t (C.tangentFaceMap retain v c x) =
      C.tangentFaceMap retain v c (C.tangentCellDilate retain v c t x) := rfl

@[simp] theorem tangentDilate_zero (x : C.TangentFan retain v) :
    C.tangentDilate retain v 0 x = C.tangentOrigin retain v := by
  obtain ⟨⟨c, p⟩, rfl⟩ := MetricGluing.point_surjective
    (C.TangentCell retain v) (C.tangentGlue retain v) x
  change C.tangentFaceMap retain v c (C.tangentCellDilate retain v c 0 p) = _
  have apex : C.tangentCellDilate retain v c 0 p = C.tangentApex retain v c := by
    apply Subtype.ext
    exact AffineMap.lineMap_apply_zero _ _
  rw [apex]
  exact (C.tangentOrigin_eq retain v c).symm

@[simp] theorem tangentDilate_one (x : C.TangentFan retain v) :
    C.tangentDilate retain v 1 x = x := by
  obtain ⟨⟨c, p⟩, rfl⟩ := MetricGluing.point_surjective
    (C.TangentCell retain v) (C.tangentGlue retain v) x
  change C.tangentFaceMap retain v c (C.tangentCellDilate retain v c 1 p) =
    C.tangentFaceMap retain v c p
  congr 1
  apply Subtype.ext
  exact AffineMap.lineMap_apply_one _ _

theorem tangentDilate_mul (s t : ℝ≥0) (x : C.TangentFan retain v) :
    C.tangentDilate retain v s (C.tangentDilate retain v t x) =
      C.tangentDilate retain v (s * t) x := by
  obtain ⟨⟨c, p⟩, rfl⟩ := MetricGluing.point_surjective
    (C.TangentCell retain v) (C.tangentGlue retain v) x
  change C.tangentDilate retain v s (C.tangentFaceMap retain v c
    (C.tangentCellDilate retain v c t p)) = _
  rw [C.tangentDilate_faceMap]
  change C.tangentFaceMap retain v c
    (C.tangentCellDilate retain v c s (C.tangentCellDilate retain v c t p)) =
    C.tangentFaceMap retain v c (C.tangentCellDilate retain v c (s * t) p)
  congr 1
  apply Subtype.ext
  exact AffineMap.lineMap_lineMap_right _ _ (t : ℝ) (s : ℝ)

@[simp] theorem tangentDilate_origin (t : ℝ≥0) :
    C.tangentDilate retain v t (C.tangentOrigin retain v) = C.tangentOrigin retain v := by
  obtain ⟨corner, eq_corner⟩ := C.vertexOfCorner_surjective retain v
  let c : C.CornerAt retain v := ⟨corner, eq_corner⟩
  rw [C.tangentOrigin_eq retain v c, C.tangentDilate_faceMap]
  have apex : C.tangentCellDilate retain v c t (C.tangentApex retain v c) =
      C.tangentApex retain v c := by
    apply Subtype.ext
    exact AffineMap.lineMap_same_apply _ _
  rw [apex]

theorem tangentDilate_edist_le (t : ℝ≥0) (x y : C.TangentFan retain v) :
    edist (C.tangentDilate retain v t x) (C.tangentDilate retain v t y) ≤
      t * edist x y := by
  by_cases zero : t = 0
  · simp [zero]
  · obtain ⟨a, rfl⟩ := MetricGluing.point_surjective
      (C.TangentCell retain v) (C.tangentGlue retain v) x
    obtain ⟨b, rfl⟩ := MetricGluing.point_surjective
      (C.TangentCell retain v) (C.tangentGlue retain v) y
    exact MetricGluing.map_edist_le_mul (C.TangentCell retain v) (C.tangentGlue retain v)
      t (pos_iff_ne_zero.mpr zero)
      (fun c p => C.tangentFaceMap retain v c (C.tangentCellDilate retain v c t p))
      (C.tangentCellDilate_face_lipschitz retain v t)
      (C.tangentCellDilate_compatible retain v t) a b

theorem tangentDilate_lipschitz (t : ℝ≥0) :
    LipschitzWith t (C.tangentDilate retain v t) :=
  C.tangentDilate_edist_le retain v t

theorem tangentDilate_inv_apply (t : ℝ≥0) (nonzero : t ≠ 0)
    (x : C.TangentFan retain v) :
    C.tangentDilate retain v t⁻¹ (C.tangentDilate retain v t x) = x := by
  rw [C.tangentDilate_mul, inv_mul_cancel₀ nonzero, C.tangentDilate_one]

/-- Every nonnegative radial scaling multiplies all intrinsic distances by its scale. -/
theorem tangentDilate_edist (t : ℝ≥0) (x y : C.TangentFan retain v) :
    edist (C.tangentDilate retain v t x) (C.tangentDilate retain v t y) =
      t * edist x y := by
  by_cases zero : t = 0
  · simp [zero]
  · apply le_antisymm (C.tangentDilate_edist_le retain v t x y)
    have reverse := C.tangentDilate_edist_le retain v t⁻¹
      (C.tangentDilate retain v t x) (C.tangentDilate retain v t y)
    rw [C.tangentDilate_inv_apply retain v t zero x,
      C.tangentDilate_inv_apply retain v t zero y] at reverse
    have bound := mul_le_mul_right reverse (t : ℝ≥0∞)
    simpa only [← mul_assoc, ← ENNReal.coe_mul, mul_inv_cancel₀ zero,
      ENNReal.coe_one, one_mul] using bound

theorem tangentDilate_dist (t : ℝ≥0) (x y : C.TangentFan retain v) :
    dist (C.tangentDilate retain v t x) (C.tangentDilate retain v t y) =
      (t : ℝ) * dist x y := by
  have equal := congrArg ENNReal.toReal (C.tangentDilate_edist retain v t x y)
  simpa only [edist_dist, ENNReal.toReal_ofReal dist_nonneg,
    ENNReal.toReal_mul, ENNReal.coe_toReal] using equal

/-- Positive radial scaling is a homeomorphism, with the reciprocal scaling as inverse. -/
def tangentDilateHomeomorph (t : ℝ≥0) (nonzero : t ≠ 0) :
    C.TangentFan retain v ≃ₜ C.TangentFan retain v where
  toFun := C.tangentDilate retain v t
  invFun := C.tangentDilate retain v t⁻¹
  left_inv := C.tangentDilate_inv_apply retain v t nonzero
  right_inv := by
    intro x
    rw [C.tangentDilate_mul, mul_inv_cancel₀ nonzero, C.tangentDilate_one]
  continuous_toFun := (C.tangentDilate_lipschitz retain v t).continuous
  continuous_invFun := (C.tangentDilate_lipschitz retain v t⁻¹).continuous

end Unfoldings.TriangleComplex
