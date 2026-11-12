module

public import Unfoldings.Cap.RadialStripTraceData
public import Unfoldings.Geometry.MonotoneStripTopology

/-! Actual strip data give source values, closed distance bounds, and quadrant margins. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap.RadialCutForest.RadialStripTraceData

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexCap C} {source : Plane} {cuts : Set Plane} {N : K.RadialCutForest source cuts}
  {t : ℝ} {positive : 0 < t} {small : t < 1} {D : FacewiseDevelopment C N.retain}
  {calibration : Plane ≃ₗᵢ[ℝ] ℂ} {i : FiveSector} {S : MonotoneStrip} {ε cutoff : ℝ}

def center (_data : N.RadialStripTraceData positive small D calibration i S ε cutoff) : ℂ :=
  D.centeredMap K source calibration (fiveSectorFrame t positive small i).place 0

def strictDomain
    (_data : N.RadialStripTraceData positive small D calibration i S ε cutoff) : Set ℂ :=
  {z | z ∈ S.strictCarrier ∧ z.re + z.im ∈ Set.Icc 0 cutoff}

variable (data : N.RadialStripTraceData positive small D calibration i S ε cutoff)

theorem source_error_closure {z : ℂ} (member : z ∈ closure data.strictDomain) :
    ‖(data.value z - data.center) - z‖ ≤ ε * (z.re + z.im) := by
  have closed : IsClosed {z : ℂ | ‖(data.value z - data.center) - z‖ ≤ ε * (z.re + z.im)} :=
    isClosed_le (((data.continuous.sub continuous_const).sub continuous_id).norm)
      ((Complex.continuous_re.add Complex.continuous_im).const_mul ε)
  have bound : data.strictDomain ⊆
      {z : ℂ | ‖(data.value z - data.center) - z‖ ≤ ε * (z.re + z.im)} := by
    intro z member
    have result := data.source_error z member.1 member.2
    rw [data.equal member] at result
    exact result
  exact closure_minimal bound closed member

theorem source_value_of_active {active : ℂ} (member : active ∈ data.strictDomain) :
    data.value 0 = data.center := (data.traces active member).1

theorem source_bank_values {active : ℂ} (member : active ∈ data.strictDomain) :
    data.value (S.lower.point 0) = data.center ∧ data.value (S.upper.point 0) = data.center := by
  have lower : S.lower.point 0 = (0 : ℂ) := by
    apply Complex.ext
    · exact data.lower_source
    · change 0 - S.lower.coordinate 0 = 0
      rw [data.lower_source, sub_self]
  have upper : S.upper.point 0 = (0 : ℂ) := by
    apply Complex.ext
    · exact data.upper_source
    · change 0 - S.upper.coordinate 0 = 0
      rw [data.upper_source, sub_self]
  rw [lower, upper, data.source_value_of_active member]
  exact ⟨rfl, rfl⟩

/-- Closed trace points at a large physical height stay far from the actual developed source. -/
theorem closed_distance_lower {z : ℂ} (member : z ∈ closure data.strictDomain) :
    (1 / 2 - ε) * (z.re + z.im) ≤ ‖data.value z - data.center‖ := by
  have error := data.source_error_closure member
  have horizontal := (le_abs_self z.re).trans (Complex.abs_re_le_norm z)
  have vertical := (le_abs_self z.im).trans (Complex.abs_im_le_norm z)
  have triangle := norm_add_le (z - (data.value z - data.center)) (data.value z - data.center)
  rw [sub_add_cancel, norm_sub_rev] at triangle
  nlinarith

theorem strict_quadrant_of_margin {μ : ℝ} (small_error : ε < μ)
    (margin : ∀ z ∈ S.carrier, 0 ≤ z.re + z.im →
      μ * (z.re + z.im) ≤ z.re ∧ μ * (z.re + z.im) ≤ z.im)
    {z : ℂ} (member : z ∈ S.openSlab 0 cutoff) :
    0 < (data.value z - data.center).re ∧ 0 < (data.value z - data.center).im := by
  have in_domain : z ∈ data.strictDomain := ⟨member.1, member.2.1.le, member.2.2.le⟩
  have error := data.source_error_closure (subset_closure in_domain)
  have coordinates := margin z ⟨member.1.1.le, member.1.2.le⟩ member.2.1.le
  have horizontal := (abs_le.mp ((Complex.abs_re_le_norm _).trans error)).1
  have vertical := (abs_le.mp ((Complex.abs_im_le_norm _).trans error)).1
  simp only [Complex.sub_re] at horizontal
  simp only [Complex.sub_im] at vertical
  have gap := mul_pos (sub_pos.mpr small_error) member.2.1
  simp only [Complex.sub_re, Complex.sub_im]
  constructor <;> nlinarith [coordinates.1, coordinates.2]

/-- Only approached end-level points enter this exclusion. A permanently collapsed
future tail need not have the strip's coherent source or distance bounds. -/
theorem end_levels_avoid_circle {active : ℂ} (member : active ∈ data.strictDomain)
    {radius : ℝ} (positive : 0 < radius) (far : radius < (1 / 2 - ε) * cutoff)
    {z : ℂ} (closed : z ∈ closure data.strictDomain)
    (end_level : z.re + z.im = 0 ∨ z.re + z.im = cutoff) :
    ‖data.value z - data.center‖ ≠ radius := by
  rcases end_level with first | last
  · have subset : data.strictDomain ⊆ S.carrier :=
      fun _ inside => ⟨inside.1.1.le, inside.1.2.le⟩
    have carrier := closure_minimal subset S.isClosed_carrier closed
    change S.lower.coordinate (z.re + z.im) ≤ z.re ∧
      z.re ≤ S.upper.coordinate (z.re + z.im) at carrier
    rw [first, data.lower_source, data.upper_source] at carrier
    have zero : z = 0 := Complex.ext (by
      change z.re = 0
      linarith [carrier.1, carrier.2]) (by
      change z.im = 0
      linarith [carrier.1, carrier.2])
    intro equal
    rw [zero, data.source_value_of_active member, sub_self, norm_zero] at equal
    exact (ne_of_gt positive) equal.symm
  · intro equal
    have lower := data.closed_distance_lower closed
    rw [last, equal] at lower
    exact (not_le_of_gt far) lower

end Unfoldings.ConvexCap.RadialCutForest.RadialStripTraceData
