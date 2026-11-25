module

public import Unfoldings.Cap.Gnomonic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Linarith

/-! Unit latitude sites and the literal east, south, and outward gnomonic chart. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FewestNets

open Real

/-- A unit sphere point with the stated colatitude and longitude. -/
def latitudeSite (colatitude longitude : ℝ) : Space :=
  WithLp.toLp 2 ![sin colatitude * cos longitude, sin colatitude * sin longitude, cos colatitude]

/-- The tangent direction of increasing longitude. -/
def latitudeEast (longitude : ℝ) : Space :=
  WithLp.toLp 2 ![-sin longitude, cos longitude, 0]

/-- The tangent direction of increasing colatitude. -/
def latitudeSouth (colatitude longitude : ℝ) : Space :=
  WithLp.toLp 2 ![cos colatitude * cos longitude, cos colatitude * sin longitude, -sin colatitude]

def latitudeAxes (ell longitude : ℝ) : Fin 3 → Space :=
  ![latitudeEast longitude, latitudeSouth ell longitude, latitudeSite ell longitude]

theorem latitudeAxes_orthonormal (ell longitude : ℝ) : Orthonormal ℝ (latitudeAxes ell longitude) := by
  rw [orthonormal_iff_ite]
  intro i j
  have colatitude := sin_sq_add_cos_sq ell
  have meridian := sin_sq_add_cos_sq longitude
  have radial := congrArg (fun p : ℝ => sin ell ^ 2 * p) meridian
  have south := congrArg (fun p : ℝ => cos ell ^ 2 * p) meridian
  have mixed := congrArg (fun p : ℝ => (sin ell * cos ell) * p) meridian
  fin_cases i <;> fin_cases j <;>
    simp only [latitudeAxes, latitudeEast, latitudeSouth, latitudeSite, PiLp.inner_apply,
      Fin.sum_univ_three, Real.inner_apply] <;> norm_num <;>
    nlinarith only [colatitude, meridian, radial, south, mixed]

theorem latitudeSite_unit (ell longitude : ℝ) : ‖latitudeSite ell longitude‖ = 1 :=
  (latitudeAxes_orthonormal ell longitude).1 2

/-- Read the east, south, and radial components in a linear isometry. -/
def latitudeBasis (ell longitude : ℝ) : OrthonormalBasis (Fin 3) ℝ Space :=
  (basisOfOrthonormalOfCardEqFinrank (latitudeAxes_orthonormal ell longitude)
    (finrank_euclideanSpace (𝕜 := ℝ) (ι := Fin 3)).symm).toOrthonormalBasis (by
      rw [coe_basisOfOrthonormalOfCardEqFinrank]
      exact latitudeAxes_orthonormal ell longitude)

def latitudeFrame (ell longitude : ℝ) : Space ≃ₗᵢ[ℝ] Space :=
  (latitudeBasis ell longitude).repr

theorem latitudeFrame_coordinate (ell longitude : ℝ) (p : Space) (i : Fin 3) :
    latitudeFrame ell longitude p i = inner ℝ (latitudeAxes ell longitude i) p := by
  rw [latitudeFrame, OrthonormalBasis.repr_apply_apply]
  have eq : ⇑(latitudeBasis ell longitude) = latitudeAxes ell longitude := by
    simp [latitudeBasis]
  rw [congrFun eq i]

/-- The positive denominator in the gnomonic chart centered at the named latitude site. -/
def latitudeDenominator (ell ell' w : ℝ) : ℝ :=
  cos (ell' - ell) - sin ell' * sin ell * (1 - cos w)

/-- Exact coordinates of a displaced latitude site before the gnomonic division. -/
theorem latitudeFrame_site (ell ell' longitude w : ℝ) :
    latitudeFrame ell longitude (latitudeSite ell' (longitude + w)) =
      WithLp.toLp 2 ![sin ell' * sin w,
        sin (ell' - ell) - cos ell * sin ell' * (1 - cos w),
        latitudeDenominator ell ell' w] := by
  have longitude_sq := sin_sq_add_cos_sq longitude
  ext i
  fin_cases i <;>
    rw [latitudeFrame_coordinate] <;>
    simp only [latitudeAxes, latitudeEast, latitudeSouth, latitudeSite, latitudeDenominator,
      PiLp.inner_apply, Real.inner_apply, Fin.sum_univ_three] <;>
    norm_num <;>
    rw [cos_add longitude w, sin_add longitude w]
  · nlinarith only [congrArg (fun p : ℝ => p * (sin ell' * sin w)) longitude_sq]
  · rw [sin_sub ell' ell]
    nlinarith only [congrArg (fun p : ℝ => p * (cos ell * sin ell' * cos w)) longitude_sq]
  · rw [cos_sub ell' ell]
    nlinarith only [congrArg (fun p : ℝ => p * (sin ell * sin ell' * cos w)) longitude_sq]

/-- The paper's two gnomonic coordinates in the strip-midpoint chart. -/
theorem latitude_gnomonic_site (ell ell' longitude w : ℝ) :
    let z := latitudeFrame ell longitude (latitudeSite ell' (longitude + w))
    (z 2)⁻¹ • Cap.horizontal z = WithLp.toLp 2 ![
      (sin ell' * sin w) / latitudeDenominator ell ell' w,
      (sin (ell' - ell) - cos ell * sin ell' * (1 - cos w)) / latitudeDenominator ell ell' w] := by
  dsimp only
  rw [latitudeFrame_site]
  ext i
  fin_cases i
  · change (latitudeDenominator ell ell' w)⁻¹ * (sin ell' * sin w) = _
    rw [div_eq_mul_inv, mul_comm]
    rfl
  · change (latitudeDenominator ell ell' w)⁻¹ *
      (sin (ell' - ell) - cos ell * sin ell' * (1 - cos w)) = _
    rw [div_eq_mul_inv, mul_comm]
    rfl

end Unfoldings.FewestNets
