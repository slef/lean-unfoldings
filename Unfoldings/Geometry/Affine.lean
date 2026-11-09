module

public import Unfoldings.Geometry.Halfplane
public import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
public import Mathlib.Tactic.Linarith

/-! Rigid motions extending closed-edge isometries and reflection in an edge line. -/

@[expose] public section

noncomputable section

namespace Unfoldings

theorem rigid_apply_lineMap (f : Plane ≃ᵃⁱ[ℝ] Plane) (a b : Plane) (t : ℝ) :
    f (AffineMap.lineMap a b t) = AffineMap.lineMap (f a) (f b) t :=
  f.toAffineMap.apply_lineMap a b t

theorem orient_lineMap (a b : Plane) (t : ℝ) : orient a b (AffineMap.lineMap a b t) = 0 := by
  rw [AffineMap.lineMap_apply_module']
  change (b 0 - a 0) * (t * (b 1 - a 1) + a 1 - a 1) -
    (b 1 - a 1) * (t * (b 0 - a 0) + a 0 - a 0) = 0
  ring

/-- The zero set of signed area is the whole affine edge line. -/
theorem exists_lineMap_of_orient_eq_zero {a b x : Plane} (different : a ≠ b)
    (zero : orient a b x = 0) : ∃ t : ℝ, x = AffineMap.lineMap a b t := by
  have nonzero : b 0 - a 0 ≠ 0 ∨ b 1 - a 1 ≠ 0 := by
    by_contra neither
    push Not at neither
    apply different
    ext i
    fin_cases i
    · exact (sub_eq_zero.mp neither.1).symm
    · exact (sub_eq_zero.mp neither.2).symm
  rcases nonzero with h0 | h1
  · refine ⟨(x 0 - a 0) / (b 0 - a 0), ?_⟩
    rw [AffineMap.lineMap_apply_module']
    ext i
    fin_cases i
    · change x 0 = (x 0 - a 0) / (b 0 - a 0) * (b 0 - a 0) + a 0
      rw [div_mul_cancel₀ _ h0]
      ring
    · change x 1 = (x 0 - a 0) / (b 0 - a 0) * (b 1 - a 1) + a 1
      apply (mul_left_inj' h0).mp
      field_simp
      dsimp [orient] at zero
      nlinarith
  · refine ⟨(x 1 - a 1) / (b 1 - a 1), ?_⟩
    rw [AffineMap.lineMap_apply_module']
    ext i
    fin_cases i
    · change x 0 = (x 1 - a 1) / (b 1 - a 1) * (b 0 - a 0) + a 0
      apply (mul_left_inj' h1).mp
      field_simp
      dsimp [orient] at zero
      nlinarith
    · change x 1 = (x 1 - a 1) / (b 1 - a 1) * (b 1 - a 1) + a 1
      rw [div_mul_cancel₀ _ h1]
      ring

theorem orient_map_ne_zero (f : Plane ≃ᵃⁱ[ℝ] Plane) {a b c : Plane}
    (nonzero : orient a b c ≠ 0) : orient (f a) (f b) (f c) ≠ 0 := by
  have different : a ≠ b := by
    intro equal
    apply nonzero
    simp [orient, equal]
  intro zero
  obtain ⟨t, ht⟩ := exists_lineMap_of_orient_eq_zero (f.injective.ne different) zero
  have expression : c = AffineMap.lineMap a b t := f.injective (by
    rw [ht]
    exact (f.toAffineMap.apply_lineMap a b t).symm)
  exact nonzero (expression ▸ orient_lineMap a b t)

/-- A rigid motion matching any two pairs of equally separated points. -/
def twoPointIsometry (a b c d : Plane) : Plane ≃ᵃⁱ[ℝ] Plane :=
  (AffineIsometryEquiv.vaddConst ℝ a).symm.trans
    ((Submodule.reflection (ℝ ∙ ((b - a) - (d - c)))ᗮ).toAffineIsometryEquiv.trans
      (AffineIsometryEquiv.vaddConst ℝ c))

@[simp] theorem twoPointIsometry_left (a b c d : Plane) : twoPointIsometry a b c d a = c := by
  simp [twoPointIsometry]

theorem twoPointIsometry_right (a b c d : Plane) (same : dist a b = dist c d) :
    twoPointIsometry a b c d b = d := by
  have norm_eq : ‖b - a‖ = ‖d - c‖ := by simpa only [dist_eq_norm'] using same
  change (Submodule.reflection (ℝ ∙ ((b - a) - (d - c)))ᗮ) (b - a) + c = d
  rw [Submodule.reflection_sub norm_eq]
  exact sub_add_cancel _ _

/-- Isometries from a closed segment into the plane agree with affine interpolation. -/
theorem isometry_apply_segment_lineMap {a b : Plane} (f : segment ℝ a b → Plane)
    (isometry : Isometry f) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    f ⟨AffineMap.lineMap a b t, lineMap_mem_segment ℝ a b ht⟩ =
      AffineMap.lineMap (f ⟨a, left_mem_segment ℝ _ _⟩)
        (f ⟨b, right_mem_segment ℝ _ _⟩) t := by
  apply eq_lineMap_of_dist_eq_mul_of_dist_eq_mul
  · rw [isometry.dist_eq, isometry.dist_eq]
    change dist a (AffineMap.lineMap a b t) = t * dist a b
    rw [dist_left_lineMap, Real.norm_of_nonneg ht.1]
  · rw [isometry.dist_eq, isometry.dist_eq]
    change dist (AffineMap.lineMap a b t) b = (1 - t) * dist a b
    rw [dist_lineMap_right, Real.norm_of_nonneg (sub_nonneg.mpr ht.2)]

/-- Every isometric embedding of a closed edge into the plane extends to a rigid motion. -/
theorem exists_affineIsometry_extension_segment {a b : Plane} (f : segment ℝ a b → Plane)
    (isometry : Isometry f) : ∃ F : Plane ≃ᵃⁱ[ℝ] Plane, ∀ x, F x.val = f x := by
  let a' := f ⟨a, left_mem_segment ℝ _ _⟩
  let b' := f ⟨b, right_mem_segment ℝ _ _⟩
  let F := twoPointIsometry a b a' b'
  have left : F a = a' := twoPointIsometry_left _ _ _ _
  have length : dist a b = dist a' b' :=
    (isometry.dist_eq ⟨a, left_mem_segment ℝ _ _⟩ ⟨b, right_mem_segment ℝ _ _⟩).symm
  have right : F b = b' := twoPointIsometry_right a b a' b' length
  refine ⟨F, ?_⟩
  intro x
  obtain ⟨t, ht, equal⟩ := (segment_eq_image_lineMap ℝ a b).le x.property
  have point_eq : (⟨AffineMap.lineMap a b t, lineMap_mem_segment ℝ a b ht⟩ : segment ℝ a b) = x :=
    Subtype.ext equal
  rw [← point_eq]
  change F (AffineMap.lineMap a b t) = _
  rw [rigid_apply_lineMap, left, right]
  exact (isometry_apply_segment_lineMap f isometry t ht).symm

/-- Reflection in the whole affine line through two edge endpoints. -/
def lineReflection (a b : Plane) : Plane ≃ᵃⁱ[ℝ] Plane :=
  (AffineIsometryEquiv.vaddConst ℝ a).symm.trans
    ((Submodule.reflection (ℝ ∙ (b - a))).toAffineIsometryEquiv.trans
      (AffineIsometryEquiv.vaddConst ℝ a))

theorem lineReflection_apply (a b x : Plane) :
    lineReflection a b x = (Submodule.reflection (ℝ ∙ (b - a))) (x - a) + a := rfl

@[simp] theorem lineReflection_left (a b : Plane) : lineReflection a b a = a := by
  rw [lineReflection_apply, sub_self, map_zero, zero_add]

@[simp] theorem lineReflection_right (a b : Plane) : lineReflection a b b = b := by
  rw [lineReflection_apply, Submodule.reflection_mem_subspace_eq_self
    (Submodule.mem_span_singleton_self (b - a)), sub_add_cancel]

theorem lineReflection_lineMap (a b : Plane) (t : ℝ) :
    lineReflection a b (AffineMap.lineMap a b t) = AffineMap.lineMap a b t := by
  rw [rigid_apply_lineMap, lineReflection_left, lineReflection_right]

theorem lineReflection_of_mem_segment {a b x : Plane} (hx : x ∈ segment ℝ a b) :
    lineReflection a b x = x := by
  obtain ⟨t, ht, rfl⟩ := (segment_eq_image_lineMap ℝ a b).le hx
  exact lineReflection_lineMap a b t

/-- Reflection fixes the edge and reverses its signed side test. -/
theorem orient_lineReflection (a b x : Plane) :
    orient a b (lineReflection a b x) = -orient a b x := by
  let K : Submodule ℝ Plane := ℝ ∙ (b - a)
  let h := lineHeight a b
  have zero : h (b - a) = 0 := by
    rw [map_sub, ← orient_eq_height]
    exact orient_self_right a b
  have vanish : ∀ v ∈ K, h v = 0 := by
    intro v hv
    obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.mp hv
    simp only [map_smul, zero, smul_zero]
  have projection : h (K.starProjection (x - a)) = 0 :=
    vanish _ (Submodule.starProjection_apply_mem K _)
  calc
    orient a b (lineReflection a b x) = h (lineReflection a b x - a) := by
      rw [map_sub, ← orient_eq_height]
    _ = -h (x - a) := by
      rw [lineReflection_apply, add_sub_cancel_right, Submodule.reflection_apply,
        two_smul, map_sub, map_add, projection, add_zero, zero_sub]
    _ = -orient a b x := by rw [map_sub, ← orient_eq_height]

end Unfoldings
