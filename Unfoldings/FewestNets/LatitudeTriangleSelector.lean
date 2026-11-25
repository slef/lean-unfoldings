module

public import Unfoldings.FewestNets.LatitudeStripTriangles
public import Unfoldings.FewestNets.LatitudeExitAngles
public import Unfoldings.FewestNets.ThreeExitRootSpan

/-! A horizontal-base triangle has the exact three signed outward exit directions. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FewestNets

open Real

variable (left right base apex height : ℝ)

/-- The gnomonic chart uses north-positive ordinates, so the apex has lower ordinate. -/
def latitudeSlopeTriangle : Set Plane :=
  exitHeadingChart false ⁻¹' convexHull ℝ
    ({⟨apex, base - height⟩, ⟨left, base⟩, ⟨right, base⟩} : Set ℂ)

/-- Tangent of the signed angle of the outward east normal. -/
def latitudeEastRatio : ℝ := (apex - right) / height

/-- Negative tangent of the signed angle of the outward west normal in the west chart. -/
def latitudeWestRatio : ℝ := (apex - left) / height

private theorem latitude_triangle_mem_iff (base_pos : left < right) (height_pos : 0 < height)
    (p : Plane) :
    p ∈ latitudeSlopeTriangle left right base apex height ↔
      p 1 ≤ base ∧
      p 0 + latitudeEastRatio right apex height * (p 1 - base) ≤ right ∧
      left ≤ p 0 + latitudeWestRatio left apex height * (p 1 - base) := by
  let u := latitudeEastRatio right apex height
  let v := latitudeWestRatio left apex height
  have spread : v - u = (right - left) / height := by
    dsimp only [v, u, latitudeEastRatio, latitudeWestRatio]
    rw [← sub_div]
    congr 1
    ring
  have width_pos : 0 < v - u := spread.symm ▸ div_pos (sub_pos.mpr base_pos) height_pos
  have east : u * height = apex - right := div_mul_cancel₀ _ height_pos.ne'
  have west : v * height = apex - left := div_mul_cancel₀ _ height_pos.ne'
  have membership :
      p ∈ latitudeSlopeTriangle left right base apex height ↔
        ∃ t ∈ Set.Icc (0 : ℝ) 1, p 1 = (1 - t) * base + t * (base - height) ∧
          p 0 ∈ Set.Icc ((1 - t) * left + t * apex) ((1 - t) * right + t * apex) := by
    unfold latitudeSlopeTriangle
    rw [Set.mem_preimage, mem_parameter_triangle_iff base_pos.le]
    simp only [exitHeadingChart_re, exitHeadingChart_im, Bool.false_eq_true, ↓reduceIte]
  rw [membership]
  change _ ↔ p 1 ≤ base ∧ p 0 + u * (p 1 - base) ≤ right ∧
    left ≤ p 0 + v * (p 1 - base)
  have east_bound (t : ℝ) (vertical : p 1 = (1 - t) * base + t * (base - height)) :
      p 0 + u * (p 1 - base) ≤ right ↔ p 0 ≤ (1 - t) * right + t * apex := by
    rw [show p 1 - base = -t * height by rw [vertical]; ring,
      show u * (-t * height) = -t * (apex - right) by rw [← east]; ring]
    constructor <;> intro h <;> linarith only [h]
  have west_bound (t : ℝ) (vertical : p 1 = (1 - t) * base + t * (base - height)) :
      left ≤ p 0 + v * (p 1 - base) ↔ (1 - t) * left + t * apex ≤ p 0 := by
    rw [show p 1 - base = -t * height by rw [vertical]; ring,
      show v * (-t * height) = -t * (apex - left) by rw [← west]; ring]
    constructor <;> intro h <;> linarith only [h]
  constructor
  · rintro ⟨t, time, vertical, interval⟩
    refine ⟨?_, (east_bound t vertical).mpr interval.2, (west_bound t vertical).mpr interval.1⟩
    linarith only [vertical, mul_nonneg time.1 height_pos.le]
  · rintro ⟨north, upper, lower⟩
    let t := (base - p 1) / height
    have vertical : p 1 = (1 - t) * base + t * (base - height) := by
      have eq : t * height = base - p 1 := div_mul_cancel₀ _ height_pos.ne'
      linarith only [eq]
    have high := (east_bound t vertical).mp upper
    have low := (west_bound t vertical).mp lower
    have time_le : t ≤ 1 := by
      apply le_of_not_gt
      intro long
      linarith only [low, high, mul_pos (sub_pos.mpr long) (sub_pos.mpr base_pos)]
    exact ⟨t, ⟨div_nonneg (sub_nonneg.mpr north) height_pos.le, time_le⟩, vertical, low, high⟩

/-- Unit outward normal of the east, west, or north side. -/
def latitudeTriangleNormal (i : Fin 3) : Plane :=
  ![(exitHeadingChart false).symm (polarRay (arctan (latitudeEastRatio right apex height))),
    (exitHeadingChart true).symm (polarRay (-arctan (latitudeWestRatio left apex height))),
    WithLp.toLp 2 ![0, 1]] i

/-- Supporting level in the corresponding unit outward normal. -/
def latitudeTriangleOffset (i : Fin 3) : ℝ :=
  ![cos (arctan (latitudeEastRatio right apex height)) *
      (right + latitudeEastRatio right apex height * base),
    -cos (arctan (latitudeWestRatio left apex height)) *
      (left + latitudeWestRatio left apex height * base), base] i

private theorem latitude_east_inner (p : Plane) :
    inner ℝ (latitudeTriangleNormal left right apex height 0) p =
      cos (arctan (latitudeEastRatio right apex height)) *
        (p 0 + latitudeEastRatio right apex height * p 1) := by
  let u := latitudeEastRatio right apex height
  change inner ℝ ((exitHeadingChart false).symm (polarRay (arctan u))) p = _
  rw [← (exitHeadingChart false).inner_map_map, LinearIsometryEquiv.apply_symm_apply,
    Complex.inner, Complex.mul_re, Complex.conj_re, Complex.conj_im, polarRay_re, polarRay_im,
    exitHeadingChart_re, exitHeadingChart_im, if_neg Bool.false_ne_true, cos_arctan, sin_arctan]
  ring

private theorem latitude_west_inner (p : Plane) :
    inner ℝ (latitudeTriangleNormal left right apex height 1) p =
      -cos (arctan (latitudeWestRatio left apex height)) *
        (p 0 + latitudeWestRatio left apex height * p 1) := by
  let v := latitudeWestRatio left apex height
  change inner ℝ ((exitHeadingChart true).symm (polarRay (-arctan v))) p = _
  rw [← (exitHeadingChart true).inner_map_map, LinearIsometryEquiv.apply_symm_apply,
    Complex.inner, Complex.mul_re, Complex.conj_re, Complex.conj_im, polarRay_re, polarRay_im,
    exitHeadingChart_re, exitHeadingChart_im, if_pos rfl, cos_neg, sin_neg, cos_arctan, sin_arctan]
  ring

private theorem latitude_north_inner (p : Plane) :
    inner ℝ (latitudeTriangleNormal left right apex height 2) p = p 1 := by
  change inner ℝ (WithLp.toLp 2 ![0, 1] : Plane) p = p 1
  simp [PiLp.inner_apply, Fin.sum_univ_two]

set_option maxHeartbeats 800000 in
-- Each side has its explicit trigonometric normal and affine support level.
/-- The selector has actual unit side normals in east, west, north order.
Its centroid is the interior reference even if the chart origin lies outside. -/
def latitudeTriangleSideDirections (base_pos : left < right) (height_pos : 0 < height) :
    PolygonSideDirections (Fin 3) (latitudeSlopeTriangle left right base apex height) where
  normal := latitudeTriangleNormal left right apex height
  offset := latitudeTriangleOffset left right base apex height
  unit := fun i => by
    fin_cases i
    · exact ((exitHeadingChart false).symm.norm_map _).trans (norm_polarRay _)
    · exact ((exitHeadingChart true).symm.norm_map _).trans (norm_polarRay _)
    · let north : Plane := WithLp.toLp 2 ![0, 1]
      change ‖north‖ = 1
      rw [← (exitHeadingChart false).norm_map north]
      have eq : exitHeadingChart false north = Complex.I := by
        apply Complex.ext <;> simp [north]
      rw [eq, Complex.norm_I]
  reference := WithLp.toLp 2 ![(left + right + apex) / 3, base - height / 3]
  strict := fun i => by
    fin_cases i
    · change inner ℝ (latitudeTriangleNormal left right apex height 0) _ <
        latitudeTriangleOffset left right base apex height 0
      rw [latitude_east_inner]
      change cos (arctan (latitudeEastRatio right apex height)) *
        ((left + right + apex) / 3 + latitudeEastRatio right apex height * (base - height / 3)) <
          cos (arctan (latitudeEastRatio right apex height)) *
            (right + latitudeEastRatio right apex height * base)
      apply (mul_lt_mul_iff_of_pos_left (cos_arctan_pos _)).mpr
      have eq : latitudeEastRatio right apex height * height = apex - right :=
        div_mul_cancel₀ _ height_pos.ne'
      linarith only [eq, base_pos]
    · change inner ℝ (latitudeTriangleNormal left right apex height 1) _ <
        latitudeTriangleOffset left right base apex height 1
      rw [latitude_west_inner]
      change -cos (arctan (latitudeWestRatio left apex height)) *
        ((left + right + apex) / 3 + latitudeWestRatio left apex height * (base - height / 3)) <
          -cos (arctan (latitudeWestRatio left apex height)) *
            (left + latitudeWestRatio left apex height * base)
      rw [neg_mul, neg_mul, neg_lt_neg_iff]
      apply (mul_lt_mul_iff_of_pos_left (cos_arctan_pos _)).mpr
      have eq : latitudeWestRatio left apex height * height = apex - left :=
        div_mul_cancel₀ _ height_pos.ne'
      linarith only [eq, base_pos]
    · change inner ℝ (latitudeTriangleNormal left right apex height 2) _ <
        latitudeTriangleOffset left right base apex height 2
      rw [latitude_north_inner]
      change base - height / 3 < base
      linarith only [height_pos]
  carrier_eq := by
    ext p
    rw [latitude_triangle_mem_iff left right base apex height base_pos height_pos]
    have east : inner ℝ (latitudeTriangleNormal left right apex height 0) p ≤
        latitudeTriangleOffset left right base apex height 0 ↔
        p 0 + latitudeEastRatio right apex height * (p 1 - base) ≤ right := by
      rw [latitude_east_inner]
      change cos (arctan (latitudeEastRatio right apex height)) *
        (p 0 + latitudeEastRatio right apex height * p 1) ≤
          cos (arctan (latitudeEastRatio right apex height)) *
            (right + latitudeEastRatio right apex height * base) ↔ _
      rw [mul_le_mul_iff_of_pos_left (cos_arctan_pos _)]
      constructor <;> intro h <;> linarith only [h]
    have west : inner ℝ (latitudeTriangleNormal left right apex height 1) p ≤
        latitudeTriangleOffset left right base apex height 1 ↔
        left ≤ p 0 + latitudeWestRatio left apex height * (p 1 - base) := by
      rw [latitude_west_inner]
      change -cos (arctan (latitudeWestRatio left apex height)) *
        (p 0 + latitudeWestRatio left apex height * p 1) ≤
          -cos (arctan (latitudeWestRatio left apex height)) *
            (left + latitudeWestRatio left apex height * base) ↔ _
      rw [neg_mul, neg_mul, neg_le_neg_iff, mul_le_mul_iff_of_pos_left (cos_arctan_pos _)]
      constructor <;> intro h <;> linarith only [h]
    have north : inner ℝ (latitudeTriangleNormal left right apex height 2) p ≤
        latitudeTriangleOffset left right base apex height 2 ↔ p 1 ≤ base := by
      rw [latitude_north_inner]
      rfl
    constructor
    · rintro ⟨up, e, w⟩ i
      fin_cases i
      · exact east.mpr e
      · exact west.mpr w
      · exact north.mpr up
    · intro all
      exact ⟨north.mp (all 2), east.mp (all 0), west.mp (all 1)⟩

theorem latitudeTriangle_east_arg (base_pos : left < right) (height_pos : 0 < height) :
    (exitHeadingChart false
        ((latitudeTriangleSideDirections left right base apex height base_pos height_pos).normal 0)).arg =
      arctan (latitudeEastRatio right apex height) := by
  change (exitHeadingChart false ((exitHeadingChart false).symm (polarRay _))).arg = _
  rw [LinearIsometryEquiv.apply_symm_apply]
  exact Circle.arg_exp (by linarith only [(arctan_mem_Ioo (latitudeEastRatio right apex height)).1,
    pi_pos]) (by linarith only [(arctan_mem_Ioo (latitudeEastRatio right apex height)).2, pi_pos])

theorem latitudeTriangle_west_arg (base_pos : left < right) (height_pos : 0 < height) :
    (exitHeadingChart true
        ((latitudeTriangleSideDirections left right base apex height base_pos height_pos).normal 1)).arg =
      -arctan (latitudeWestRatio left apex height) := by
  change (exitHeadingChart true ((exitHeadingChart true).symm (polarRay _))).arg = _
  rw [LinearIsometryEquiv.apply_symm_apply]
  exact Circle.arg_exp (by linarith only [(arctan_mem_Ioo (latitudeWestRatio left apex height)).2,
    pi_pos]) (by linarith only [(arctan_mem_Ioo (latitudeWestRatio left apex height)).1, pi_pos])

theorem latitudeTriangle_north_arg (base_pos : left < right) (height_pos : 0 < height)
    (side : Bool) :
    (exitHeadingChart side
        ((latitudeTriangleSideDirections left right base apex height base_pos height_pos).normal 2)).arg =
      π / 2 :=
  ConvexRoof.ThreeExitComponentRouting.north_arg side

end Unfoldings.FewestNets
