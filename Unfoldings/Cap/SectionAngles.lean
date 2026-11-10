module

public import Unfoldings.Cap.RoofSections
public import Unfoldings.Cap.VerticalProduct
public import Unfoldings.Geometry.SlopeAngles

/-!
# Actual spatial turning of vertical cap sections

The real secant inclination is the actual spatial angle of successive section
directions. Thus concavity bounds the total extrinsic turning along every
finite section partition independently of how many original faces it crosses.
-/

@[expose] public section

noncomputable section

namespace Unfoldings.Cap

theorem horizontalAtHeight_norm_slopeRay (direction : Plane) (unit : ‖direction‖ = 1) (s : ℝ) :
    ‖horizontalAtHeight direction s‖ = ‖slopeRay s‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [horizontal_norm_sq, horizontal_horizontalAtHeight, height_horizontalAtHeight, unit,
    ← Complex.normSq_eq_norm_sq]
  simp only [slopeRay, Complex.normSq_mk, one_mul, sq]

theorem horizontalAtHeight_inner_unit (direction : Plane) (unit : ‖direction‖ = 1) (s t : ℝ) :
    inner ℝ (horizontalAtHeight direction s) (horizontalAtHeight direction t) = 1 + s * t := by
  rw [horizontal_inner, horizontal_horizontalAtHeight, horizontal_horizontalAtHeight,
    height_horizontalAtHeight, height_horizontalAtHeight, real_inner_self_eq_norm_sq, unit, one_pow]

/-- Genuine spatial angle of two inclinations within the same unit horizontal direction. -/
theorem angle_horizontalAtHeight (direction : Plane) (unit : ‖direction‖ = 1) (s t : ℝ) :
    InnerProductGeometry.angle (horizontalAtHeight direction s) (horizontalAtHeight direction t) =
      |Real.arctan t - Real.arctan s| := by
  calc
    _ = InnerProductGeometry.angle (slopeRay s) (slopeRay t) := by
      unfold InnerProductGeometry.angle
      rw [horizontalAtHeight_norm_slopeRay direction unit,
        horizontalAtHeight_norm_slopeRay direction unit,
        horizontalAtHeight_inner_unit direction unit, Complex.inner]
      congr 2
      simp only [slopeRay, Complex.mul_re, Complex.conj_re, Complex.conj_im]
      ring
    _ = _ := angle_slopeRay s t

end Unfoldings.Cap

namespace Unfoldings.ConvexCap

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexCap C)

def roofSectionPoint (p direction : Plane) (time : ℝ) : Space :=
  Cap.horizontalAtHeight (p + time • direction) (K.roofSection p direction time)

theorem roofSectionPoint_mem_surface (p direction : Plane) (time : ℝ)
    (inside : p + time • direction ∈ K.footprint) :
    K.roofSectionPoint p direction time ∈ K.folding.surface := by
  rw [K.surface_iff_roofHeight]
  simp only [roofSectionPoint, Cap.horizontal_horizontalAtHeight, Cap.height_horizontalAtHeight]
  exact ⟨inside, rfl⟩

theorem roofSectionPoint_sub (p direction : Plane) {a b : ℝ} (ordered : a < b) :
    K.roofSectionPoint p direction b - K.roofSectionPoint p direction a =
      (b - a) • Cap.horizontalAtHeight direction
        ((K.roofSection p direction b - K.roofSection p direction a) / (b - a)) := by
  ext i
  fin_cases i
  · change (p 0 + b * direction 0) - (p 0 + a * direction 0) = (b - a) * direction 0
    ring
  · change (p 1 + b * direction 1) - (p 1 + a * direction 1) = (b - a) * direction 1
    ring
  · change K.roofSection p direction b - K.roofSection p direction a =
      (b - a) * ((K.roofSection p direction b - K.roofSection p direction a) / (b - a))
    field_simp [(sub_pos.mpr ordered).ne']

def roofSectionSecant {n : ℕ} (p direction : Plane) (time : Fin (n + 2) → ℝ)
    (i : Fin (n + 1)) : Space :=
  K.roofSectionPoint p direction (time i.succ) - K.roofSectionPoint p direction (time i.castSucc)

/-- One section secant has its actual arctangent inclination. -/
theorem roofSectionSecant_angle {n : ℕ} (p direction : Plane) (unit : ‖direction‖ = 1)
    (time : Fin (n + 2) → ℝ) (ordered : StrictMono time) (i j : Fin (n + 1)) :
    InnerProductGeometry.angle (K.roofSectionSecant p direction time i)
      (K.roofSectionSecant p direction time j) =
        |secantHeading (K.roofSection p direction) time j -
          secantHeading (K.roofSection p direction) time i| := by
  unfold roofSectionSecant
  rw [K.roofSectionPoint_sub p direction
      (ordered (show i.castSucc < i.succ from Fin.castSucc_lt_succ)),
    K.roofSectionPoint_sub p direction
      (ordered (show j.castSucc < j.succ from Fin.castSucc_lt_succ)),
    InnerProductGeometry.angle_smul_left_of_pos _ _
      (sub_pos.mpr (ordered (show i.castSucc < i.succ from Fin.castSucc_lt_succ))),
    InnerProductGeometry.angle_smul_right_of_pos _ _
      (sub_pos.mpr (ordered (show j.castSucc < j.succ from Fin.castSucc_lt_succ)))]
  exact Cap.angle_horizontalAtHeight direction unit _ _

/-- Total actual spatial turning is uniformly small with tilt, regardless of partition size. -/
theorem sum_roofSection_spatial_turn_le {c : ℝ} (positive : 0 < c)
    (height : ∀ f, c ≤ K.normal f 2) (p direction : Plane) (unit : ‖direction‖ = 1)
    {n : ℕ} (time : Fin (n + 2) → ℝ) (ordered : StrictMono time) :
    (∑ i : Fin n, InnerProductGeometry.angle (K.roofSectionSecant p direction time i.castSucc)
      (K.roofSectionSecant p direction time i.succ)) ≤
        2 * Real.arctan (Real.sqrt (1 - c ^ 2) / c) := by
  simp only [K.roofSectionSecant_angle p direction unit time ordered]
  exact K.sum_roofSection_heading_turn_le positive height p direction unit time ordered

/-- For tilt at most phi, the total actual section turning is at most twice phi. -/
theorem sum_roofSection_spatial_turn_le_tilt {φ : ℝ} (nonnegative : 0 ≤ φ)
    (small : φ < Real.pi / 2) (tilt : K.TiltBound φ)
    (p direction : Plane) (unit : ‖direction‖ = 1)
    {n : ℕ} (time : Fin (n + 2) → ℝ) (ordered : StrictMono time) :
    (∑ i : Fin n, InnerProductGeometry.angle (K.roofSectionSecant p direction time i.castSucc)
      (K.roofSectionSecant p direction time i.succ)) ≤ 2 * φ := by
  have lower : -(Real.pi / 2) < φ := by linarith [Real.pi_pos]
  have height := Real.cos_pos_of_mem_Ioo ⟨lower, small⟩
  have bound := K.sum_roofSection_spatial_turn_le height tilt p direction unit time ordered
  rw [← Real.sin_eq_sqrt_one_sub_cos_sq nonnegative (by linarith [Real.pi_pos]),
    ← Real.tan_eq_sin_div_cos, Real.arctan_tan lower small] at bound
  exact bound

/-- A single positive tilt controls every section partition before the entire mesh is supplied. -/
theorem exists_uniform_tilt_section_turn_lt {ε : ℝ} (positive : 0 < ε) :
    ∃ φ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      ∀ {Face' : Type u} [Fintype Face'] {C' : TriangleComplex.{u, v} Face'}
        (K : ConvexCap C'), K.TiltBound φ →
        ∀ (p direction : Plane), ‖direction‖ = 1 →
          ∀ {n : ℕ} (time : Fin (n + 2) → ℝ), StrictMono time →
            (∑ i : Fin n, InnerProductGeometry.angle
              (K.roofSectionSecant p direction time i.castSucc)
              (K.roofSectionSecant p direction time i.succ)) < ε := by
  let φ : ℝ := min (ε / 4) (Real.pi / 4)
  have φpos : 0 < φ := lt_min (by positivity) (by positivity)
  have φsmall : φ < Real.pi / 2 := (min_le_right _ _).trans_lt (by linarith [Real.pi_pos])
  refine ⟨φ, ⟨φpos, φsmall⟩, fun K tilt p direction unit _ time ordered => ?_⟩
  have bound := K.sum_roofSection_spatial_turn_le_tilt φpos.le φsmall tilt p direction unit
    time ordered
  have upper : 2 * φ < ε := by
    have := min_le_left (ε / 4) (Real.pi / 4)
    change φ ≤ ε / 4 at this
    linarith
  exact bound.trans_lt upper

end Unfoldings.ConvexCap
