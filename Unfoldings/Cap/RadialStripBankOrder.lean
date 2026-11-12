module

public import Unfoldings.Cap.RadialStripPointOrder
public import Unfoldings.Cap.StripCircleBanks
public import Unfoldings.Cap.RadialStripCircleBanks
public import Unfoldings.Geometry.BankRadialOrder

/-! The actual lower bank precedes the upper bank on each nonempty source-circle slice. -/

@[expose] public section

noncomputable section

namespace Unfoldings

namespace MonotoneStrip

/-- An empty circle slice or an interval with actual endpoints in the lower/upper order. -/
def HasOrientedBankCircleInterval (S : MonotoneStrip) (G : ℂ → ℂ) (center : ℂ)
    (cutoff radius : ℝ) : Prop :=
  quadrantCirclePoint center radius ⁻¹' (G '' S.openSlab 0 cutoff) = ∅ ∨
    ∃ slice : S.BankCircleSlice G center cutoff radius,
      (G (S.lower.point slice.lowerHeight) - center).re <
        (G (S.upper.point slice.upperHeight) - center).re

theorem lower_point_re_le_or_im_le (S : MonotoneStrip) (h : ℝ) {z : ℂ}
    (member : z ∈ S.carrier) : (S.lower.point h).re ≤ z.re ∨ z.im ≤ (S.lower.point h).im := by
  rcases le_total h (z.re + z.im) with before | after
  · exact Or.inl ((S.lower.coordinate_mono before).trans member.1)
  · right
    have bound := S.lower.complement_mono after
    change z.im ≤ h - S.lower.coordinate h
    linarith [member.1]

end MonotoneStrip

namespace ConvexCap.RadialCutForest.RadialStripTraceData

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexCap C} {source : Plane} {cuts : Set Plane} {N : K.RadialCutForest source cuts}
  {t : ℝ} {positive : 0 < t} {small : t < 1} {D : FacewiseDevelopment C N.retain}
  {calibration : Plane ≃ₗᵢ[ℝ] ℂ} {i : FiveSector} {S : MonotoneStrip} {ε cutoff : ℝ}

variable (data : N.RadialStripTraceData positive small D calibration i S ε cutoff)

/-- Radial progress excludes comparable physical endpoints. A mixed-coordinate
connector and the actual chart bounds then give the oriented circle order. -/
theorem bank_circle_order {μ : ℝ} (nonnegative : 0 ≤ ε) (small_error : ε < 1 / 2)
    (numerical : ε * (1 + ε) < μ - ε)
    (linear_error : ∀ f z,
      ‖(D.coordinatePlacement K calibration (fiveSectorFrame t positive small i).place f).linear z -
        z‖ ≤ ε * ‖z‖)
    (margin : ∀ z ∈ S.carrier, 0 ≤ z.re + z.im →
      μ * (z.re + z.im) ≤ z.re ∧ μ * (z.re + z.im) ≤ z.im)
    {l u radius : ℝ} (radius_positive : 0 < radius)
    (first : S.lower.point l ∈ closure data.strictDomain)
    (last : S.upper.point u ∈ closure data.strictDomain)
    (first_radius : ‖data.value (S.lower.point l) - data.center‖ = radius)
    (last_radius : ‖data.value (S.upper.point u) - data.center‖ = radius)
    (different : data.value (S.lower.point l) ≠ data.value (S.upper.point u)) :
    (data.value (S.lower.point l) - data.center).re <
        (data.value (S.upper.point u) - data.center).re ∧
      (data.value (S.upper.point u) - data.center).im <
        (data.value (S.lower.point l) - data.center).im := by
  let p := S.lower.point l
  let q := S.upper.point u
  have ppositive := data.closed_height_pos_of_norm first
    (by rw [first_radius]; exact radius_positive)
  have qpositive := data.closed_height_pos_of_norm last
    (by rw [last_radius]; exact radius_positive)
  have genuine : p ≠ q := fun equal => different (congrArg data.value equal)
  have not_forward : ¬ (p.re ≤ q.re ∧ p.im ≤ q.im) := by
    rintro ⟨horizontal, vertical⟩
    have height : p.re + p.im < q.re + q.im := by
      by_contra nonpositive
      exact genuine (Complex.ext (by linarith) (by linarith))
    have strict := data.norm_lt_of_coordinates_le nonnegative numerical linear_error margin
      first last ppositive horizontal vertical height
    rw [first_radius, last_radius] at strict
    exact (lt_irrefl _ strict).elim
  have not_backward : ¬ (q.re ≤ p.re ∧ q.im ≤ p.im) := by
    rintro ⟨horizontal, vertical⟩
    have height : q.re + q.im < p.re + p.im := by
      by_contra nonpositive
      exact genuine (Complex.ext (by linarith) (by linarith))
    have strict := data.norm_lt_of_coordinates_le nonnegative numerical linear_error margin
      last first qpositive horizontal vertical height
    rw [first_radius, last_radius] at strict
    exact (lt_irrefl _ strict).elim
  have physical : p.re ≤ q.re ∧ q.im ≤ p.im := by
    rcases S.lower_point_re_le_or_im_le l (data.closed_bounded last).1 with horizontal | vertical
    · exact ⟨horizontal, (lt_of_not_ge (fun opposite => not_forward ⟨horizontal, opposite⟩)).le⟩
    · exact ⟨(lt_of_not_ge (fun opposite => not_backward ⟨opposite, vertical⟩)).le, vertical⟩
  have signed := data.signed_lt_of_opposite_coordinates small_error linear_error
    first last physical.1 physical.2 genuine
  have close_margin : ε < μ := by nlinarith [sq_nonneg ε]
  have pquadrant := data.strict_quadrant_of_closed_margin close_margin margin first ppositive
  have qquadrant := data.strict_quadrant_of_closed_margin close_margin margin last qpositive
  let x := data.value p - data.center
  let y := data.value q - data.center
  have alternative : x.re ≤ y.re ∨ y.im ≤ x.im := by
    by_contra neither
    push Not at neither
    dsimp only [x, y] at neither
    simp only [Complex.sub_re, Complex.sub_im] at neither
    linarith [neither.1, neither.2]
  have identity (z : ℂ) : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    ring
  have radii : x.re ^ 2 + x.im ^ 2 = y.re ^ 2 + y.im ^ 2 := by
    rw [← identity, ← identity]
    change ‖data.value p - data.center‖ ^ 2 = ‖data.value q - data.center‖ ^ 2
    rw [first_radius, last_radius]
  have ordered := quadrant_circle_order pquadrant.1.le pquadrant.2.le
    qquadrant.1.le qquadrant.2.le radii alternative
  have re_ne : x.re ≠ y.re := by
    intro equal
    have imaginary : x.im = y.im := by nlinarith [pquadrant.2, qquadrant.2]
    have actual : x = y := Complex.ext equal imaginary
    apply different
    have cancel := congrArg (fun z : ℂ => z + data.center) actual
    simpa only [x, y, sub_add_cancel] using cancel
  have im_ne : y.im ≠ x.im := by
    intro equal
    have real : x.re = y.re := by nlinarith [pquadrant.1, qquadrant.1]
    exact re_ne real
  exact ⟨lt_of_le_of_ne ordered.1 re_ne, lt_of_le_of_ne ordered.2 im_ne⟩

/-- The interval has the actual lower/upper orientation, with no minimum/maximum ambiguity. -/
theorem oriented_circle_slice {μ : ℝ} (nonnegative : 0 ≤ ε) (small_error : ε < 1 / 2)
    (numerical : ε * (1 + ε) < μ - ε)
    (linear_error : ∀ f z,
      ‖(D.coordinatePlacement K calibration (fiveSectorFrame t positive small i).place f).linear z -
        z‖ ≤ ε * ‖z‖)
    (margin : ∀ z ∈ S.carrier, 0 ≤ z.re + z.im →
      μ * (z.re + z.im) ≤ z.re ∧ μ * (z.re + z.im) ≤ z.im)
    {radius : ℝ} (radius_positive : 0 < radius)
    (slice : S.BankCircleSlice data.value data.center cutoff radius) :
    quadrantCirclePoint data.center radius ⁻¹' (data.value '' S.openSlab 0 cutoff) =
      Set.Ioo (data.value (S.lower.point slice.lowerHeight) - data.center).re
        (data.value (S.upper.point slice.upperHeight) - data.center).re := by
  have order := data.bank_circle_order nonnegative small_error numerical linear_error margin
    radius_positive slice.lower_closed slice.upper_closed slice.lower_radius slice.upper_radius
    slice.distinct
  simpa only [min_eq_left order.1.le, max_eq_right order.1.le] using slice.interval

/-- Actual strip data determine an oriented interval or an empty slice on every
controlled source circle. Endpoint order is proved rather than supplied. -/
theorem oriented_circle_interval {μ : ℝ} (nonnegative : 0 ≤ ε) (small_error : ε < 1 / 2)
    (numerical : ε * (1 + ε) < μ - ε)
    (linear_error : ∀ f z,
      ‖(D.coordinatePlacement K calibration (fiveSectorFrame t positive small i).place f).linear z -
        z‖ ≤ ε * ‖z‖)
    (margin : ∀ z ∈ S.carrier, 0 ≤ z.re + z.im →
      μ * (z.re + z.im) ≤ z.re ∧ μ * (z.re + z.im) ≤ z.im)
    {radius : ℝ} (radius_positive : 0 < radius)
    (far : radius < (1 / 2 - ε) * cutoff) :
    S.HasOrientedBankCircleInterval data.value data.center cutoff radius := by
  classical
  rcases Set.eq_empty_or_nonempty (quadrantCirclePoint data.center radius ⁻¹'
      (data.value '' S.openSlab 0 cutoff)) with empty | nonempty
  · exact Or.inl empty
  have close_margin : ε < μ := by nlinarith [sq_nonneg ε]
  have image_quadrant : ∀ z ∈ data.value '' S.openSlab 0 cutoff,
      0 < (z - data.center).re ∧ 0 < (z - data.center).im := by
    rintro z ⟨p, member, rfl⟩
    exact data.strict_quadrant_of_margin close_margin margin member
  have meets := nonempty.image (quadrantCirclePoint data.center radius)
  rw [quadrantCirclePoint_image_preimage data.center radius_positive image_quadrant] at meets
  obtain ⟨slice⟩ := data.circle_slice close_margin margin radius_positive far meets
  exact Or.inr ⟨slice, (data.bank_circle_order nonnegative small_error numerical linear_error
    margin radius_positive slice.lower_closed slice.upper_closed slice.lower_radius
    slice.upper_radius slice.distinct).1⟩

end ConvexCap.RadialCutForest.RadialStripTraceData
end Unfoldings
