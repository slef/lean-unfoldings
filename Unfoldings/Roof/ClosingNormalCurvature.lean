module

public import Unfoldings.Roof.AngularCurvature
public import Unfoldings.Roof.CurvatureNonnegative
public import Unfoldings.Roof.NormalRibbonCancellation
public import Unfoldings.Cap.SharpGnomonicSolidAngle

/-! The signed intrinsic roof curvature cancels against the actual normal ribbon. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof

open Cap MeasureTheory
open scoped ENNReal

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  (K : ConvexRoof C)

/-- From a supported horizontal trace, its signed winding cancels the signed
intrinsic vertex charge at common normal directions. -/
theorem abs_signed_defects_sub_winding_le
    {cell : Set Plane} (compact : IsCompact cell) (convex : Convex ℝ cell)
    (slopes : ∀ f, K.normalSlope f ∈ cell)
    (level : ℝ) (trace chord : ℝ → ℝ) (htrace : Measurable trace) (hchord : Measurable chord)
    {a b : ℝ}
    (contacts : ∀ p ∈ Set.Ioc a b, ∃ x : Plane, x 1 = level ∧
      WithLp.toLp 2 ![p, trace p] ∈ supportingSlopes K.roofHeight x)
    (ribbon : graphRibbon trace chord a b ∪ graphRibbon chord trace a b ⊆ Cap.planeCartesian '' cell)
    (weight : C.Vertex Set.univ → ℝ) (bounded : ∀ v, |weight v| ≤ 1)
    (sign : ∀ v, 0 ≤ (K.projectedVertex v 1 - level) * weight v)
    (on_link : ∀ v, K.projectedVertex v 1 = level → weight v = 0) :
    |(∑ v, weight v * C.interiorAngularDefect Set.univ v) -
      (∫ z, normalRibbonWinding trace chord a b z ∂Cap.cartesianSolidAngle)| ≤
      (solidAngleMeasure (Cap.gnomonicNormal '' cell)).toReal := by
  classical
  let w (v : C.Vertex Set.univ) := if C.IsBoundaryVertex Set.univ v then 0 else weight v
  have wbound (v : C.Vertex Set.univ) : |w v| ≤ 1 := by
    unfold w
    split_ifs
    · norm_num
    · exact bounded v
  have wsign (v : C.Vertex Set.univ) : 0 ≤ (K.projectedVertex v 1 - level) * w v := by
    unfold w
    split_ifs
    · rw [mul_zero]
    · exact sign v
  have wzero (v : C.Vertex Set.univ) (endpt : K.projectedVertex v 1 = level) : w v = 0 := by
    unfold w
    rw [on_link v endpt, ite_self]
  have included (v : C.Vertex Set.univ) : K.normalPolygon v ⊆ cell := by
    apply convexHull_min _ convex
    rintro p ⟨f, j, _, rfl⟩
    exact slopes f
  have finite : Cap.cartesianSolidAngle (Cap.planeCartesian '' cell) < ∞ := by
    rw [Cap.cartesianSolidAngle_image compact]
    exact (Cap.solidAngle_gnomonic_le_volume compact).trans_lt compact.measure_lt_top
  have bound := abs_supporting_charge_sub_winding_le K.roofHeight compact finite
    (fun _ _ h => K.normalPolygons_nonoverlapping h) included K.projectedVertex
    (fun v _ h => K.normalPolygon_supports v h) level trace chord htrace hchord contacts ribbon
    w wbound wsign wzero
  have charge := Cap.integral_normalPolygonCharge finite included (K.compact_normalPolygon)
    (fun _ => convex_convexHull ℝ _) w
  rw [charge] at bound
  have identity :
      (∑ v, w v * (solidAngleMeasure (Cap.gnomonicNormal '' K.normalPolygon v)).toReal) =
        ∑ v, weight v * C.interiorAngularDefect Set.univ v := by
    apply Finset.sum_congr rfl
    intro v _
    by_cases border : C.IsBoundaryVertex Set.univ v
    · simp only [w, border, ite_true, TriangleComplex.interiorAngularDefect, mul_zero, zero_mul]
    · have geometry := K.angular_defect_eq_solid_normal v border
      change ENNReal.ofReal (2 * Real.pi - C.totalAngle Set.univ v) =
        solidAngleMeasure (Cap.gnomonicNormal '' K.normalPolygon v) at geometry
      have pos := K.interiorCurvature_nonneg v
      rw [TriangleComplex.interiorAngularDefect, ite_eq_right border] at pos
      simp only [w, ite_eq_right border, TriangleComplex.interiorAngularDefect,
        ← geometry, ENNReal.toReal_ofReal pos]
  rwa [identity] at bound

end Unfoldings.ConvexRoof
