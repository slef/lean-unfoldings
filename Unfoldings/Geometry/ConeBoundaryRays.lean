module

public import Unfoldings.Geometry.Affine
public import Unfoldings.Geometry.CyclicRays

/-!
# The two boundary directions of a planar convex cone

A nonzero boundary direction is witnessed by a supporting linear form that
vanishes there and is strictly positive at a fixed interior direction. Two
such directions on the same side of that interior ray must be positive multiples.
This includes cones with lines in their closure.
-/

@[expose] public section

namespace Unfoldings

/-- The determinant expansion in an arbitrary planar pair. -/
theorem orient_zero_balance (x y q : Plane) :
    orient 0 x q • y = orient 0 y q • x + orient 0 x y • q := by
  ext i
  fin_cases i <;> simp only [orient, PiLp.zero_apply, PiLp.smul_apply,
    PiLp.add_apply, smul_eq_mul, sub_zero]
  · change (x 0 * q 1 - x 1 * q 0) * y 0 =
      (y 0 * q 1 - y 1 * q 0) * x 0 + (x 0 * y 1 - x 1 * y 0) * q 0
    ring
  · change (x 0 * q 1 - x 1 * q 0) * y 1 =
      (y 0 * q 1 - y 1 * q 0) * x 1 + (x 0 * y 1 - x 1 * y 0) * q 1
    ring

/-- An active supporting form separates a genuine boundary direction from an interior ray. -/
theorem orient_boundary_ne_zero {x q : Plane} (nonzero : x ≠ 0)
    (f : Plane →ₗ[ℝ] ℝ) (active : f x = 0) (strict : 0 < f q) : orient 0 x q ≠ 0 := by
  intro zero
  obtain ⟨t, equal⟩ := exists_lineMap_of_orient_eq_zero nonzero.symm zero
  have image := congrArg f equal
  rw [AffineMap.lineMap_apply_module'] at image
  simp only [sub_zero, add_zero, map_smul, active, smul_eq_mul, mul_zero] at image
  exact strict.ne' image

/-- There is at most one supported boundary ray on each side of an interior ray. -/
theorem boundary_rays_same_side {x y q : Plane} (xne : x ≠ 0) (yne : y ≠ 0)
    (f g : Plane →ₗ[ℝ] ℝ) (fx : f x = 0) (gy : g y = 0)
    (fq : 0 < f q) (gq : 0 < g q) (fy : 0 ≤ f y) (gx : 0 ≤ g x)
    (side : (0 < orient 0 x q) ↔ 0 < orient 0 y q) :
    ∃ t : ℝ, 0 < t ∧ y = t • x := by
  have xq := orient_boundary_ne_zero xne f fx fq
  have yq := orient_boundary_ne_zero yne g gy gq
  have balance := orient_zero_balance x y q
  have first := congrArg f balance
  have second := congrArg g balance
  simp only [map_smul, map_add, fx, gy, smul_eq_mul, mul_zero, zero_add] at first second
  have xy : orient 0 x y = 0 := by
    rcases lt_or_gt_of_ne xq with negative | positive
    · have negative_y : orient 0 y q < 0 := lt_of_le_of_ne
        (le_of_not_gt (fun h => negative.not_gt (side.mpr h))) yq
      have one : orient 0 x y ≤ 0 := by
        have : orient 0 x q * f y ≤ 0 := mul_nonpos_of_nonpos_of_nonneg negative.le fy
        nlinarith
      have two : 0 ≤ orient 0 x y := by
        have : orient 0 y q * g x ≤ 0 := mul_nonpos_of_nonpos_of_nonneg negative_y.le gx
        nlinarith
      exact le_antisymm one two
    · have positive_y := side.mp positive
      have one : 0 ≤ orient 0 x y := by
        have : 0 ≤ orient 0 x q * f y := mul_nonneg positive.le fy
        nlinarith
      have two : orient 0 x y ≤ 0 := by
        have : 0 ≤ orient 0 y q * g x := mul_nonneg positive_y.le gx
        nlinarith
      exact le_antisymm two one
  obtain ⟨t, equal⟩ := exists_lineMap_of_orient_eq_zero xne.symm xy
  rw [AffineMap.lineMap_apply_module'] at equal
  simp only [sub_zero, add_zero] at equal
  refine ⟨t, ?_, equal⟩
  have scaling : orient 0 y q = t * orient 0 x q := by
    rw [equal]
    simp only [orient, PiLp.zero_apply, PiLp.smul_apply, smul_eq_mul, sub_zero]
    ring
  rcases lt_or_gt_of_ne xq with negative | positive
  · have negative_y : orient 0 y q < 0 := lt_of_le_of_ne
      (le_of_not_gt (fun h => negative.not_gt (side.mpr h))) yq
    nlinarith
  · have positive_y := side.mp positive
    nlinarith

/-- A genuine planar wedge contains no zero vector. -/
theorem zero_not_mem_strictRayCone {x y : Plane} (genuine : orient 0 x y ≠ 0) :
    (0 : Plane) ∉ strictRayCone x y := by
  rintro ⟨a, _, b, hb, equation⟩
  have cross := congrArg (fun z : Plane => orient 0 x z) equation
  have identity : orient 0 x (a • x + b • y) = b * orient 0 x y := by
    simp only [orient, PiLp.zero_apply, PiLp.smul_apply, PiLp.add_apply, smul_eq_mul, sub_zero]
    ring
  rw [identity] at cross
  have zero : b * orient 0 x y = 0 := by simpa only [orient_self_left] using cross.symm
  exact (mul_ne_zero hb.ne' genuine) zero

/-- Positive rescaling preserves an open two-ray cone. -/
theorem smul_mem_strictRayCone {x y z : Plane} (member : z ∈ strictRayCone x y)
    {t : ℝ} (positive : 0 < t) : t • z ∈ strictRayCone x y := by
  obtain ⟨a, ha, b, hb, rfl⟩ := member
  exact ⟨t * a, mul_pos positive ha, t * b, mul_pos positive hb,
    by rw [smul_add, smul_smul, smul_smul]⟩

/-- Disjoint wedges can meet the supported boundary of a planar cone at most twice. -/
theorem card_le_two_of_supported_boundary {I A : Type*} [Fintype I]
    (form : A → Plane →ₗ[ℝ] ℝ) (q : Plane) (strict : ∀ a, 0 < form a q)
    (left right point : I → Plane)
    (separated : Pairwise (fun i j => Disjoint
      (strictRayCone (left i) (right i)) (strictRayCone (left j) (right j))))
    (genuine : ∀ i, point i ≠ 0)
    (inside : ∀ i, point i ∈ strictRayCone (left i) (right i))
    (supported : ∀ i a, 0 ≤ form a (point i))
    (active : ∀ i, ∃ a, form a (point i) = 0) : Fintype.card I ≤ 2 := by
  classical
  let side (i : I) : Bool := decide (0 < orient 0 (point i) q)
  have injective : Function.Injective side := by
    intro i j equal
    by_contra different
    obtain ⟨a, ha⟩ := active i
    obtain ⟨b, hb⟩ := active j
    have same : (0 < orient 0 (point i) q) ↔ 0 < orient 0 (point j) q :=
      decide_eq_decide.mp equal
    obtain ⟨t, positive, equation⟩ := boundary_rays_same_side (genuine i) (genuine j)
      (form a) (form b) ha hb (strict a) (strict b) (supported j a) (supported i b) same
    have shared : point j ∈ strictRayCone (left i) (right i) := by
      rw [equation]
      exact smul_mem_strictRayCone (inside i) positive
    exact Set.disjoint_left.mp (separated different) shared (inside j)
  simpa only [Fintype.card_bool] using Fintype.card_le_of_injective side injective

end Unfoldings
