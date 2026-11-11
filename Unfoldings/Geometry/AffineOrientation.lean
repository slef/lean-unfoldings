module

public import Unfoldings.Geometry.Affine

/-! Signed area under an affine map and preservation of relative side signs. -/

@[expose] public section

noncomputable section

namespace Unfoldings

def orientationScale (f : Plane →ᵃ[ℝ] Plane) : ℝ :=
  orient 0 (f.linear (EuclideanSpace.single 0 1)) (f.linear (EuclideanSpace.single 1 1))

theorem orient_affineMap (f : Plane →ᵃ[ℝ] Plane) (a b c : Plane) :
    orient (f a) (f b) (f c) = orientationScale f * orient a b c := by
  have decomposition (y x : Plane) : y - x =
      (y 0 - x 0) • (EuclideanSpace.single 0 1 : Plane) +
        (y 1 - x 1) • (EuclideanSpace.single 1 1 : Plane) := by
    ext i
    fin_cases i <;> simp
  have difference (y x : Plane) : f y - f x =
      (y 0 - x 0) • f.linear (EuclideanSpace.single 0 1) +
        (y 1 - x 1) • f.linear (EuclideanSpace.single 1 1) := by
    change f y -ᵥ f x = _
    rw [← f.linear_apply_vsub]
    change f.linear (y - x) = _
    rw [decomposition, map_add, map_smul, map_smul]
  change (f b - f a) 0 * (f c - f a) 1 - (f b - f a) 1 * (f c - f a) 0 = _
  rw [difference, difference]
  simp only [orientationScale, orient, PiLp.add_apply, PiLp.smul_apply,
    PiLp.zero_apply, smul_eq_mul, sub_zero]
  ring

/-- The same signed area scale acts on tangent vectors, without a translation term. -/
theorem orient_affine_linear (f : Plane →ᵃ[ℝ] Plane) (x y : Plane) :
    orient 0 (f.linear x) (f.linear y) = orientationScale f * orient 0 x y := by
  have first := f.linear_apply_vsub x 0
  have last := f.linear_apply_vsub y 0
  change f.linear (x - 0) = f x - f 0 at first
  change f.linear (y - 0) = f y - f 0 at last
  rw [sub_zero] at first last
  have equal : orient 0 (f.linear x) (f.linear y) = orient (f 0) (f x) (f y) := by
    rw [first, last]
    simp only [orient, PiLp.sub_apply, PiLp.zero_apply, sub_zero]
  exact equal.trans (orient_affineMap f 0 x y)

theorem orientationScale_ne_zero (f : Plane ≃ᵃⁱ[ℝ] Plane) :
    orientationScale f.toAffineMap ≠ 0 := by
  have nonzero : orient (0 : Plane) (EuclideanSpace.single 0 1)
      (EuclideanSpace.single 1 1) ≠ 0 := by norm_num [orient]
  have mapped := orient_map_ne_zero f nonzero
  have identity : orient (f 0) (f (EuclideanSpace.single 0 1))
      (f (EuclideanSpace.single 1 1)) = orientationScale f.toAffineMap *
        orient 0 (EuclideanSpace.single 0 1) (EuclideanSpace.single 1 1) :=
    orient_affineMap f.toAffineMap _ _ _
  rw [identity] at mapped
  exact (mul_ne_zero_iff.mp mapped).1

theorem orient_mul_pos_map (f : Plane ≃ᵃⁱ[ℝ] Plane) {a b c d e g : Plane}
    (positive : 0 < orient a b c * orient d e g) :
    0 < orient (f a) (f b) (f c) * orient (f d) (f e) (f g) := by
  have first : orient (f a) (f b) (f c) = orientationScale f.toAffineMap * orient a b c :=
    orient_affineMap f.toAffineMap a b c
  have second : orient (f d) (f e) (f g) = orientationScale f.toAffineMap * orient d e g :=
    orient_affineMap f.toAffineMap d e g
  rw [first, second]
  have product := mul_pos (sq_pos_of_ne_zero (orientationScale_ne_zero f)) positive
  convert product using 1
  ring

end Unfoldings
