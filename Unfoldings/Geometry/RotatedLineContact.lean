module

public import Unfoldings.Cone.Sector
public import Unfoldings.Geometry.CircleLineContact
public import Unfoldings.Geometry.HingeCircleAngleDerivative
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars

/-! A rotating affine link moves its transverse intersection smoothly along a fixed circle. -/

@[expose] public section

noncomputable section

namespace Unfoldings

open scoped Topology RealInnerProductSpace

attribute [local instance] Complex.finrank_real_complex_fact

private theorem hasDerivAt_polarRay (θ : ℝ) :
    HasDerivAt polarRay (Complex.I * polarRay θ) θ := by
  have line : HasDerivAt (fun x : ℝ => x • Complex.I) Complex.I θ := by
    simpa only [id_eq, one_smul] using
      HasDerivAt.smul_const (hasDerivAt_id θ) Complex.I
  have exp_deriv :=
    (Complex.hasDerivAt_exp (θ • Complex.I)).hasFDerivAt.restrictScalars ℝ
  have h := exp_deriv.comp_hasDerivAt θ line
  have curve (x : ℝ) : Complex.exp (x • Complex.I) = polarRay x := by
    rw [Complex.real_smul]
    rfl
  have h' : HasDerivAt (fun x : ℝ => Complex.exp (x • Complex.I))
      (Complex.I • Complex.exp (θ • Complex.I)) θ := h
  simpa only [smul_eq_mul, curve] using h'

/-- Rotating an affine link and sliding on it gives the velocity decomposition
used in the hinge-circle angular speed bound. -/
theorem hasDerivAt_rotatedSlide (h a v : ℂ) {s : ℝ → ℝ} {t ds : ℝ}
    (slide : HasDerivAt s ds t) :
    HasDerivAt (fun θ => h + polarRay θ * (a + s θ • v))
      (Complex.orientation.rightAngleRotation (polarRay t * (a + s t • v)) +
        ds • (polarRay t * v)) t := by
  have d := (hasDerivAt_polarRay t).mul ((slide.smul_const v).const_add a)
  have add := d.const_add h
  convert add using 1
  simp only [Complex.rightAngleRotation, Complex.real_smul]
  ring

/-- The chosen contact on a rotating supporting line of a suffix edge. Both
`a` and the line direction `v` are given in the coordinates before rotation. -/
def rotatingLineCircleParameter (h a v : ℂ) (r θ : ℝ) : ℝ :=
  outwardCircleLineParameter (h + polarRay θ * a) (polarRay θ * v) r

/-- The corresponding actual point on the rotated line. -/
def rotatingLineCircleContact (h a v : ℂ) (r θ : ℝ) : ℂ :=
  h + polarRay θ * a + rotatingLineCircleParameter h a v r θ • (polarRay θ * v)

theorem rotatingLineCircleContact_eq (h a v : ℂ) (r θ : ℝ) :
    rotatingLineCircleContact h a v r θ =
      h + polarRay θ * (a + rotatingLineCircleParameter h a v r θ • v) := by
  simp only [rotatingLineCircleContact, Complex.real_smul, mul_add]
  ring

theorem continuous_rotatingLineCircleParameter (h a v : ℂ) (r : ℝ) (v_ne : v ≠ 0) :
    Continuous (rotatingLineCircleParameter h a v r) := by
  have ray : Continuous polarRay := continuous_subtype_val.comp Circle.exp.continuous
  let u (θ : ℝ) := h + polarRay θ * a
  let d (θ : ℝ) := polarRay θ * v
  have cu : Continuous u := continuous_const.add (ray.mul continuous_const)
  have cd : Continuous d := ray.mul continuous_const
  have cdisc : Continuous (fun θ => circleLineDiscriminant (u θ) (d θ) r) :=
    ((cu.inner cd).pow 2).add ((cd.norm.pow 2).mul (continuous_const.sub (cu.norm.pow 2)))
  exact ((cu.inner cd).neg.add (Real.continuous_sqrt.comp cdisc)).div
    (cd.norm.pow 2) (fun θ => pow_ne_zero _ (norm_ne_zero_iff.mpr
      (mul_ne_zero (polarRay_ne_zero θ) v_ne)))

theorem continuous_rotatingLineCircleContact (h a v : ℂ) (r : ℝ) (v_ne : v ≠ 0) :
    Continuous (rotatingLineCircleContact h a v r) := by
  have ray : Continuous polarRay := continuous_subtype_val.comp Circle.exp.continuous
  rw [show rotatingLineCircleContact h a v r =
    fun θ => h + polarRay θ * (a + rotatingLineCircleParameter h a v r θ • v)
    from funext (rotatingLineCircleContact_eq h a v r)]
  exact continuous_const.add (ray.mul (continuous_const.add
    ((continuous_rotatingLineCircleParameter h a v r v_ne).smul continuous_const)))

/-- The formula recovers any contact with positive radial incidence. -/
theorem rotatingLineCircleParameter_eq_of_contact {h a v p : ℂ} {r θ t : ℝ}
    (point : p = h + polarRay θ * (a + t • v)) (on_circle : ‖p‖ = r)
    (outward : 0 < inner ℝ p (polarRay θ * v)) :
    rotatingLineCircleParameter h a v r θ = t := by
  have eq : h + polarRay θ * a + t • (polarRay θ * v) = p := by
    rw [point]
    simp only [Complex.real_smul, mul_add]
    ring
  apply outwardCircleLineParameter_eq
  · rwa [eq]
  · rwa [eq]

/-- A transverse rotating-line contact satisfies the sharp local angular bound
whenever its radial incidence has margin `m` and its hinge is inside the circle. -/
theorem exists_rotatingLineCircleContact_angle_derivative_le {h a v : ℂ} {r t s₀ m : ℝ}
    (r_pos : 0 < r) (m_pos : 0 < m) (v_ne : v ≠ 0) (hinge : ‖h‖ ≤ r)
    (on_circle : ‖h + polarRay t * (a + s₀ • v)‖ = r)
    (margin : m * (r * ‖polarRay t * v‖) ≤
      inner ℝ (h + polarRay t * (a + s₀ • v)) (polarRay t * v)) :
    ∃ rate ≤ 2 / m, HasDerivAt
      (fun θ => Complex.arg (rotatingLineCircleContact h a v r θ /
        rotatingLineCircleContact h a v r t)) rate t := by
  let u (θ : ℝ) := h + polarRay θ * a
  let d (θ : ℝ) := polarRay θ * v
  let s (θ : ℝ) := outwardCircleLineParameter (u θ) (d θ) r
  have express (θ s₁ : ℝ) : u θ + s₁ • d θ = h + polarRay θ * (a + s₁ • v) := by
    simp only [u, d, Complex.real_smul, mul_add]
    ring
  have du : DifferentiableAt ℝ u t :=
    (((hasDerivAt_polarRay t).mul_const a).const_add h).differentiableAt
  have dd : DifferentiableAt ℝ d t := ((hasDerivAt_polarRay t).mul_const v).differentiableAt
  have direction : d t ≠ 0 := mul_ne_zero (polarRay_ne_zero t) v_ne
  have contact : ‖u t + s₀ • d t‖ = r := by rwa [express]
  have trans : 0 < inner ℝ (u t + s₀ • d t) (d t) := by
    rw [express]
    exact (mul_pos m_pos (mul_pos r_pos (norm_pos_iff.mpr direction))).trans_le margin
  have ds := differentiableAt_outwardCircleLineParameter du dd contact trans
  have s_eq : s t = s₀ := outwardCircleLineParameter_eq contact trans
  let f := rotatingLineCircleContact h a v r
  have describe (θ : ℝ) : f θ = h + polarRay θ * (a + s θ • v) := express θ (s θ)
  have derivative := hasDerivAt_rotatedSlide h a v ds.hasDerivAt
  have hf : HasDerivAt f
      (Complex.orientation.rightAngleRotation (f t - h) + deriv s t • d t) t := by
    have w : f t - h = polarRay t * (a + s t • v) := by rw [describe, add_sub_cancel_left]
    rw [w]
    exact derivative.congr_of_eventuallyEq (Filter.Eventually.of_forall describe)
  have at_contact : f t = h + polarRay t * (a + s₀ • v) := by rw [describe, s_eq]
  have radius : ‖f t‖ = r := by rw [at_contact]; exact on_circle
  have norm_nonzero : f t ≠ 0 := norm_ne_zero_iff.mp (radius.trans_ne r_pos.ne')
  have disc : 0 < circleLineDiscriminant (u t) (d t) r := by
    rw [circleLineDiscriminant_eq contact]
    exact sq_pos_of_pos trans
  have continuous_disc : ContinuousAt (fun θ => circleLineDiscriminant (u θ) (d θ) r) t := by
    unfold circleLineDiscriminant
    exact ((du.continuousAt.inner dd.continuousAt).pow 2).add
      ((dd.continuousAt.norm.pow 2).mul (continuousAt_const.sub (du.continuousAt.norm.pow 2)))
  have positive_disc : ∀ᶠ θ in 𝓝 t, 0 ≤ circleLineDiscriminant (u θ) (d θ) r := by
    have h : ∀ᶠ θ in 𝓝 t, 0 < circleLineDiscriminant (u θ) (d θ) r :=
      continuous_disc (Ioi_mem_nhds disc)
    exact h.mono fun _ hz => hz.le
  have constant : ∀ᶠ θ in 𝓝 t, ‖f θ‖ = ‖f t‖ := by
    filter_upwards [positive_disc] with θ positive
    rw [radius]
    exact norm_outwardCircleLineContact r_pos.le positive
      (mul_ne_zero (polarRay_ne_zero θ) v_ne)
  have margin' : m * (‖f t‖ * ‖d t‖) ≤ inner ℝ (f t) (d t) := by
    rw [radius, at_contact]
    exact margin
  have inside : ‖h‖ ≤ ‖f t‖ := radius.symm ▸ hinge
  have derivative_angle := hasDerivAt_circleContact_angle hf norm_nonzero constant
  refine ⟨_, ?_, derivative_angle⟩
  rw [← derivative_angle.deriv]
  exact circleContact_angle_derivative_le hf norm_nonzero constant m_pos direction inside
    margin' rfl

end Unfoldings
