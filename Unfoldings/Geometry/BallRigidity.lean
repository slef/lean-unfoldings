module

public import Unfoldings.Geometry.IsometryOnConvex
public import Unfoldings.Geometry.RadialLocality

/-!
# Rigid extension of an isometric map of a whole open ball

Radial straightness makes the normalized displacement independent of the
positive sampling scale. Shrinking any pair of ambient points to one common
scale then proves that this extension is globally isometric. Strict convexity
of the target makes it an affine isometry. No surjectivity or global extension
is assumed for the original ball map.
-/

@[expose] public section

noncomputable section

namespace Unfoldings

variable (E F : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

structure IsometricBallMap where
  center : E
  radius : ℝ
  positive : 0 < radius
  map : Metric.ball center radius → F
  isometry : Isometry map

namespace IsometricBallMap

variable {E F} [StrictConvexSpace ℝ F] (B : IsometricBallMap E F)

def centerPoint : Metric.ball B.center B.radius := ⟨B.center, Metric.mem_ball_self B.positive⟩

def scale (z : E) : ℝ := Classical.choose (exists_positive_lineMap_mem_ball B.center z B.positive)

omit [NormedSpace ℝ F] [StrictConvexSpace ℝ F] in
theorem scale_pos (z : E) : 0 < B.scale z :=
  (Classical.choose_spec (exists_positive_lineMap_mem_ball B.center z B.positive)).1

omit [NormedSpace ℝ F] [StrictConvexSpace ℝ F] in
theorem scale_near (z : E) :
    AffineMap.lineMap B.center z (B.scale z) ∈ Metric.ball B.center B.radius :=
  (Classical.choose_spec (exists_positive_lineMap_mem_ball B.center z B.positive)).2

def sample (z : E) : Metric.ball B.center B.radius :=
  ⟨AffineMap.lineMap B.center z (B.scale z), B.scale_near z⟩

theorem slope_eq (z : E) {t u : ℝ} (tpos : 0 < t) (upos : 0 < u)
    (near_t : AffineMap.lineMap B.center z t ∈ Metric.ball B.center B.radius)
    (near_u : AffineMap.lineMap B.center z u ∈ Metric.ball B.center B.radius) :
    t⁻¹ • (B.map ⟨AffineMap.lineMap B.center z t, near_t⟩ - B.map B.centerPoint) =
      u⁻¹ • (B.map ⟨AffineMap.lineMap B.center z u, near_u⟩ - B.map B.centerPoint) := by
  have ordered_case : ∀ {t u : ℝ}, 0 < t → 0 < u →
      ∀ (ht : AffineMap.lineMap B.center z t ∈ Metric.ball B.center B.radius)
        (hu : AffineMap.lineMap B.center z u ∈ Metric.ball B.center B.radius), t ≤ u →
      t⁻¹ • (B.map ⟨AffineMap.lineMap B.center z t, ht⟩ - B.map B.centerPoint) =
        u⁻¹ • (B.map ⟨AffineMap.lineMap B.center z u, hu⟩ - B.map B.centerPoint) := by
    intro t u ht hu near_t near_u ordered
    have ratio : t / u ∈ Set.Icc (0 : ℝ) 1 :=
      ⟨(div_pos ht hu).le, (div_le_one hu).mpr ordered⟩
    let y : Metric.ball B.center B.radius := ⟨AffineMap.lineMap B.center z u, near_u⟩
    have expression : AffineMap.lineMap B.center y.val (t / u) =
        AffineMap.lineMap B.center z t := by
      rw [AffineMap.lineMap_lineMap_right, div_mul_cancel₀ _ hu.ne']
    have equal := isometry_lineMap_on_convex (convex_ball B.center B.radius)
      B.map B.isometry B.centerPoint y (t / u) ratio
    change B.map ⟨AffineMap.lineMap B.center y.val (t / u), _⟩ =
      AffineMap.lineMap (B.map B.centerPoint) (B.map y) (t / u) at equal
    have point : (⟨AffineMap.lineMap B.center y.val (t / u),
        (convex_ball B.center B.radius).lineMap_mem B.centerPoint.property y.property ratio⟩ :
        Metric.ball B.center B.radius) = ⟨AffineMap.lineMap B.center z t, near_t⟩ :=
      Subtype.ext expression
    rw [point] at equal
    have formula := equal.trans (AffineMap.lineMap_apply_module'
      (B.map B.centerPoint) (B.map y) (t / u))
    have displacement : B.map ⟨AffineMap.lineMap B.center z t, near_t⟩ - B.map B.centerPoint =
        (t / u) • (B.map y - B.map B.centerPoint) := by
      rw [formula, add_sub_cancel_right]
    rw [displacement, ← mul_smul]
    have coefficient : t⁻¹ * (t / u) = u⁻¹ := by field_simp
    rw [coefficient]
  rcases le_total t u with ordered | ordered
  · exact ordered_case tpos upos near_t near_u ordered
  · exact (ordered_case upos tpos near_u near_t ordered).symm

def extension (z : E) : F :=
  (B.scale z)⁻¹ • (B.map (B.sample z) - B.map B.centerPoint) + B.map B.centerPoint

theorem extension_eq_slope (z : E) {t : ℝ} (positive : 0 < t)
    (near : AffineMap.lineMap B.center z t ∈ Metric.ball B.center B.radius) :
    B.extension z = t⁻¹ • (B.map ⟨AffineMap.lineMap B.center z t, near⟩ -
      B.map B.centerPoint) + B.map B.centerPoint :=
  congrArg (fun y => y + B.map B.centerPoint)
    (B.slope_eq z (B.scale_pos z) positive (B.scale_near z) near)

theorem extension_agrees (x : Metric.ball B.center B.radius) : B.extension x.val = B.map x := by
  have near : AffineMap.lineMap B.center x.val (1 : ℝ) ∈ Metric.ball B.center B.radius := by
    simpa only [AffineMap.lineMap_apply_one] using x.property
  have equal := B.extension_eq_slope x.val zero_lt_one near
  simpa only [AffineMap.lineMap_apply_one, inv_one, one_smul, sub_add_cancel] using equal

omit [NormedSpace ℝ F] [StrictConvexSpace ℝ F] in
theorem near_of_le_scale (z : E) {t : ℝ} (nonnegative : 0 ≤ t) (bound : t ≤ B.scale z) :
    AffineMap.lineMap B.center z t ∈ Metric.ball B.center B.radius := by
  have near := B.scale_near z
  rw [Metric.mem_ball, dist_lineMap_left, Real.norm_of_nonneg (B.scale_pos z).le] at near
  rw [Metric.mem_ball, dist_lineMap_left, Real.norm_of_nonneg nonnegative]
  exact (mul_le_mul_of_nonneg_right bound dist_nonneg).trans_lt near

theorem extension_isometry : Isometry B.extension := by
  apply Isometry.of_dist_eq
  intro z w
  let t := min (B.scale z) (B.scale w)
  have positive : 0 < t := lt_min (B.scale_pos z) (B.scale_pos w)
  have near_z := B.near_of_le_scale z positive.le (min_le_left _ _)
  have near_w := B.near_of_le_scale w positive.le (min_le_right _ _)
  rw [B.extension_eq_slope z positive near_z, B.extension_eq_slope w positive near_w,
    dist_add_right, dist_smul₀, Real.norm_of_nonneg (inv_nonneg.mpr positive.le),
    dist_sub_right, B.isometry.dist_eq]
  change t⁻¹ * dist (AffineMap.lineMap B.center z t) (AffineMap.lineMap B.center w t) = dist z w
  rw [← AffineMap.homothety_eq_lineMap, ← AffineMap.homothety_eq_lineMap, dist_homothety,
    Real.norm_of_nonneg positive.le, ← mul_assoc, inv_mul_cancel₀ positive.ne', one_mul]

def affineExtension : E →ᵃⁱ[ℝ] F := B.extension_isometry.affineIsometryOfStrictConvexSpace

@[simp] theorem affineExtension_agrees (x : Metric.ball B.center B.radius) :
    B.affineExtension x.val = B.map x := B.extension_agrees x

end IsometricBallMap
end Unfoldings
