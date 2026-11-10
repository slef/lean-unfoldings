module

public import Unfoldings.Cap.NormalImage
public import Unfoldings.Geometry.ConcaveSecants

/-!
# Uniform concave vertical sections of the actual cap roof

The supporting normal slopes bound the whole roof's height variation. Along
any unit horizontal direction, all secant inclinations are antitone and their
total variation is bounded independently of the number of crossed faces.
-/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexCap C)

/-- The finite lower envelope inherits the uniform Lipschitz bound of its actual support planes. -/
theorem roofHeight_sub_le {R : ℝ} (bound : ∀ f, ‖K.normalSlope f‖ ≤ R) (p q : Plane) :
    K.roofHeight q - K.roofHeight p ≤ R * ‖q - p‖ := by
  obtain ⟨f, equal⟩ := K.exists_roofHeight_eq_supportHeight p
  have roof := K.roofHeight_le_supportHeight q f
  rw [K.supportHeight_difference f p q, ← equal] at roof
  have scalar := (neg_le_abs (inner ℝ (K.normalSlope f) (q - p))).trans
    (abs_real_inner_le_norm (K.normalSlope f) (q - p))
  exact (by linarith : K.roofHeight q - K.roofHeight p ≤
    -inner ℝ (K.normalSlope f) (q - p)).trans
      (scalar.trans (mul_le_mul_of_nonneg_right (bound f) (norm_nonneg _)))

/-- The bound applies on the footprint and to the supporting-plane envelope outside it. -/
theorem abs_roofHeight_sub_le {R : ℝ} (bound : ∀ f, ‖K.normalSlope f‖ ≤ R) (p q : Plane) :
    |K.roofHeight q - K.roofHeight p| ≤ R * ‖q - p‖ := by
  apply abs_le.mpr
  constructor
  · have reverse := K.roofHeight_sub_le bound q p
    rw [norm_sub_rev] at reverse
    linarith
  · exact K.roofHeight_sub_le bound p q

/-- A vertical section is parametrized by signed horizontal distance when the direction is unit. -/
def roofSection (p direction : Plane) (time : ℝ) : ℝ := K.roofHeight (p + time • direction)

theorem roofSection_concave (p direction : Plane) :
    ConcaveOn ℝ Set.univ (K.roofSection p direction) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb sum
  have key := K.roofHeight_concave.2 (Set.mem_univ (p + x • direction))
    (Set.mem_univ (p + y • direction)) ha hb sum
  have affine : a • (p + x • direction) + b • (p + y • direction) =
      p + (a * x + b * y) • direction := by
    calc
      _ = (a + b) • p + (a * x + b * y) • direction := by module
      _ = _ := by rw [sum, one_smul]
  rw [affine] at key
  exact key

theorem roofSection_slope_le {R : ℝ} (bound : ∀ f, ‖K.normalSlope f‖ ≤ R)
    (p direction : Plane) (unit : ‖direction‖ = 1) {a b : ℝ} (ordered : a < b) :
    |(K.roofSection p direction b - K.roofSection p direction a) / (b - a)| ≤ R := by
  have height := K.abs_roofHeight_sub_le bound (p + a • direction) (p + b • direction)
  have displacement : (p + b • direction) - (p + a • direction) = (b - a) • direction := by
    module
  rw [displacement, norm_smul, Real.norm_eq_abs, unit, mul_one] at height
  rw [abs_div, abs_of_pos (sub_pos.mpr ordered), div_le_iff₀ (sub_pos.mpr ordered)]
  exact height.trans_eq (by rw [abs_of_pos (sub_pos.mpr ordered)])

/-- The real secant inclinations of every cap section have a mesh-independent total-turn bound. -/
theorem sum_roofSection_heading_turn_le {c : ℝ} (positive : 0 < c)
    (height : ∀ f, c ≤ K.normal f 2) (p direction : Plane) (unit : ‖direction‖ = 1)
    {n : ℕ} (time : Fin (n + 2) → ℝ) (ordered : StrictMono time) :
    (∑ i : Fin n, |secantHeading (K.roofSection p direction) time i.succ -
      secantHeading (K.roofSection p direction) time i.castSucc|) ≤
        2 * Real.arctan (Real.sqrt (1 - c ^ 2) / c) :=
  sum_secantHeading_turn_le (K.roofSection_concave p direction) time ordered
    (fun i => K.roofSection_slope_le (K.normalSlope_norm_le positive height)
      p direction unit (ordered (show i.castSucc < i.succ from Fin.castSucc_lt_succ)))

end Unfoldings.ConvexCap
