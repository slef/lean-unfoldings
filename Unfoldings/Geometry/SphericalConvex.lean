module

public import Unfoldings.Cap.Gnomonic

/-!
# Convex normal regions in gnomonic coordinates

Spherical convexity is closure under normalized nonnegative combinations of unit
vectors. Its inverse image in the height-one chart is an ordinary convex set.
Closed spherical regions give closed planar selections without any polygonal or
nondegeneracy requirement on the region.
-/

@[expose] public section

noncomputable section

namespace Unfoldings

/-- A spherical convex region consists of unit vectors and contains the normalization
of every nonzero nonnegative combination of two of its points. -/
def SphericalConvex (region : Set Space) : Prop :=
  (∀ n ∈ region, ‖n‖ = 1) ∧
    ∀ u ∈ region, ∀ v ∈ region, ∀ a b : ℝ, 0 ≤ a → 0 ≤ b →
      a • u + b • v ≠ 0 → NormedSpace.normalize (a • u + b • v) ∈ region

namespace Cap

/-- Gnomonic inverse images are expressed using actual normalized upward normals. -/
def gnomonicRegion (region : Set Space) : Set Plane := gnomonicNormal ⁻¹' region

theorem continuous_northLift : Continuous northLift := by
  have expression (p : Plane) : northLift p = horizontalLift p + northLift 0 := by
    ext i
    fin_cases i <;> simp [northLift, horizontalLift]
  have equal : northLift = fun p => horizontalLift p + northLift 0 := funext expression
  rw [equal]
  exact horizontalLiftIsometry.continuous.add continuous_const

theorem continuous_gnomonicNormal : Continuous gnomonicNormal :=
  (continuous_northLift.norm.inv₀ (fun p =>
    (norm_pos_iff.mpr (northLift_ne_zero p)).ne')).smul continuous_northLift

theorem isClosed_gnomonicRegion {region : Set Space} (closed : IsClosed region) :
    IsClosed (gnomonicRegion region) := closed.preimage continuous_gnomonicNormal

theorem northLift_combo (p q : Plane) (a b : ℝ) (sum : a + b = 1) :
    northLift (a • p + b • q) = a • northLift p + b • northLift q := by
  ext i
  fin_cases i
  · rfl
  · rfl
  · change (1 : ℝ) = a * 1 + b * 1
    simpa only [mul_one] using sum.symm

/-- Spherical convexity becomes ordinary convexity in a gnomonic chart. -/
theorem convex_gnomonicRegion {region : Set Space} (convex : SphericalConvex region) :
    Convex ℝ (gnomonicRegion region) := by
  intro p hp q hq a b ha hb sum
  have expression :
      (a * ‖northLift p‖) • gnomonicNormal p + (b * ‖northLift q‖) • gnomonicNormal q =
        northLift (a • p + b • q) := by
    rw [mul_smul, mul_smul, gnomonicNormal, gnomonicNormal,
      NormedSpace.norm_smul_normalize, NormedSpace.norm_smul_normalize,
      northLift_combo p q a b sum]
  have member := convex.2 (gnomonicNormal p) hp (gnomonicNormal q) hq
    (a * ‖northLift p‖) (b * ‖northLift q‖)
    (mul_nonneg ha (norm_nonneg _)) (mul_nonneg hb (norm_nonneg _))
    (by rw [expression]; exact northLift_ne_zero _)
  change NormedSpace.normalize (northLift (a • p + b • q)) ∈ region
  rwa [expression] at member

/-- Selection by an actual unit upward normal equals selection by its slope coordinate. -/
theorem normal_mem_iff_slope_mem {region : Set Space} (normal : Space)
    (unit : ‖normal‖ = 1) (upward : 0 < normal 2) :
    normal ∈ region ↔ (normal 2)⁻¹ • horizontal normal ∈ gnomonicRegion region := by
  change normal ∈ region ↔ gnomonicNormal _ ∈ region
  rw [gnomonicNormal_slope normal unit upward]

end Cap
end Unfoldings
