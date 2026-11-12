module

public import Unfoldings.Cap.RadialStripTraceVisibility
public import Unfoldings.Geometry.RecoverableStripInitialClosure
public import Unfoldings.Geometry.NearIdentityRadial
public import Unfoldings.Geometry.NearIdentityMargins
public import Unfoldings.Geometry.MonotoneStripBoundedInjective

/-! Actual strip traces preserve radial progress and signed order between closed points. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap.RadialCutForest.RadialStripTraceData

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexCap C} {source : Plane} {cuts : Set Plane} {N : K.RadialCutForest source cuts}
  {t : ℝ} {positive : 0 < t} {small : t < 1} {D : FacewiseDevelopment C N.retain}
  {calibration : Plane ≃ₗᵢ[ℝ] ℂ} {i : FiveSector} {S : MonotoneStrip} {ε cutoff : ℝ}

variable (data : N.RadialStripTraceData positive small D calibration i S ε cutoff)

theorem closed_bounded {z : ℂ} (member : z ∈ closure data.strictDomain) :
    z ∈ S.boundedCarrier 0 cutoff := by
  have inside : data.strictDomain ⊆ S.boundedCarrier 0 cutoff :=
    fun _ inside => ⟨⟨inside.1.1.le, inside.1.2.le⟩, inside.2⟩
  exact closure_minimal inside (S.isClosed_boundedCarrier 0 cutoff) member

theorem closed_initial {q z : ℂ} (endpoint : q ∈ closure data.strictDomain)
    (member : z ∈ S.carrier) (height : z.re + z.im ∈ Set.Icc 0 (q.re + q.im)) :
    z ∈ closure data.strictDomain :=
  S.carrier_mem_closure_before_closed_height data.finite_coherentSet data.pinches
    endpoint member height

theorem closed_height_pos_of_norm {z : ℂ} (member : z ∈ closure data.strictDomain)
    (away : 0 < ‖data.value z - data.center‖) : 0 < z.re + z.im := by
  have bounded := data.closed_bounded member
  by_contra nonpositive
  have zero_height : z.re + z.im = 0 := le_antisymm (le_of_not_gt nonpositive) bounded.2.1
  have carrier := bounded.1
  change S.lower.coordinate (z.re + z.im) ≤ z.re ∧
    z.re ≤ S.upper.coordinate (z.re + z.im) at carrier
  rw [zero_height, data.lower_source, data.upper_source] at carrier
  have zero : z = 0 := by
    apply Complex.ext
    · change z.re = 0
      linarith [carrier.1, carrier.2]
    · change z.im = 0
      linarith [carrier.1, carrier.2]
  have error := data.source_error_closure member
  rw [zero_height, mul_zero, zero, sub_zero] at error
  rw [zero] at away
  exact (not_le_of_gt away) error

theorem strict_quadrant_of_closed_margin {μ : ℝ} (small_error : ε < μ)
    (margin : ∀ z ∈ S.carrier, 0 ≤ z.re + z.im →
      μ * (z.re + z.im) ≤ z.re ∧ μ * (z.re + z.im) ≤ z.im)
    {z : ℂ} (member : z ∈ closure data.strictDomain) (height : 0 < z.re + z.im) :
    0 < (data.value z - data.center).re ∧ 0 < (data.value z - data.center).im := by
  have error := data.source_error_closure member
  have coordinates := margin z (data.closed_bounded member).1 height.le
  have horizontal := (abs_le.mp ((Complex.abs_re_le_norm _).trans error)).1
  have vertical := (abs_le.mp ((Complex.abs_im_le_norm _).trans error)).1
  simp only [Complex.sub_re] at horizontal
  simp only [Complex.sub_im] at vertical
  have gap := mul_pos (sub_pos.mpr small_error) height
  simp only [Complex.sub_re, Complex.sub_im]
  constructor <;> nlinarith [coordinates.1, coordinates.2]

/-- Coordinate-comparable closed points move strictly outward. This applies to
arbitrary monotone connectors, not only the two banks. -/
theorem norm_lt_of_coordinates_le {μ : ℝ} (nonnegative : 0 ≤ ε)
    (numerical : ε * (1 + ε) < μ - ε)
    (linear_error : ∀ f z,
      ‖(D.coordinatePlacement K calibration (fiveSectorFrame t positive small i).place f).linear z -
        z‖ ≤ ε * ‖z‖)
    (margin : ∀ z ∈ S.carrier, 0 ≤ z.re + z.im →
      μ * (z.re + z.im) ≤ z.re ∧ μ * (z.re + z.im) ≤ z.im)
    {p q : ℂ} (first : p ∈ closure data.strictDomain) (last : q ∈ closure data.strictDomain)
    (start : 0 < p.re + p.im) (horizontal : p.re ≤ q.re) (vertical : p.im ≤ q.im)
    (ordered : p.re + p.im < q.re + q.im) :
    ‖data.value p - data.center‖ < ‖data.value q - data.center‖ := by
  let frame := (fiveSectorFrame t positive small i).place
  let A := fun f => (D.centeredCoordinatePlacement K source calibration frame f).toAffineMap
  have pb := data.closed_bounded first
  have qb := data.closed_bounded last
  have μpositive : 0 < μ := by nlinarith [sq_nonneg ε]
  have coordinates := margin p pb.1 start.le
  have physical_re : 0 ≤ p.re := (mul_nonneg μpositive.le start.le).trans coordinates.1
  have physical_im : 0 ≤ p.im := (mul_nonneg μpositive.le start.le).trans coordinates.2
  have physical_norm : ‖p‖ ≤ p.re + p.im := by
    simpa only [abs_of_nonneg physical_re, abs_of_nonneg physical_im] using
      Complex.norm_le_abs_re_add_abs_im p
  have error := data.source_error_closure first
  have re_error := (abs_le.mp ((Complex.abs_re_le_norm _).trans error)).1
  have im_error := (abs_le.mp ((Complex.abs_im_le_norm _).trans error)).1
  simp only [Complex.sub_re] at re_error
  simp only [Complex.sub_im] at im_error
  have horizontal_margin : (μ - ε) * (p.re + p.im) ≤ (data.value p - data.center).re := by
    simp only [Complex.sub_re]
    nlinarith [coordinates.1]
  have vertical_margin : (μ - ε) * (p.re + p.im) ≤ (data.value p - data.center).im := by
    simp only [Complex.sub_im]
    nlinarith [coordinates.2]
  have size : ‖data.value p - data.center‖ ≤ (1 + ε) * (p.re + p.im) := by
    have triangle := norm_add_le (data.value p - data.center - p) p
    rw [sub_add_cancel] at triangle
    nlinarith
  let P := S.increasingPath pb.1 qb.1 horizontal vertical
  have inside (r : unitInterval) : P r ∈ closure data.strictDomain := by
    have bounded := S.increasingPath_mem_bounded
      (show p ∈ S.boundedCarrier 0 (q.re + q.im) from ⟨pb.1, pb.2.1, ordered.le⟩)
      (show q ∈ S.boundedCarrier 0 (q.re + q.im) from ⟨qb.1, qb.2.1, le_rfl⟩)
      horizontal vertical r
    exact data.closed_initial last bounded.1 bounded.2
  apply finite_near_identity_selection_radial A
    (fun f => (A f).continuous_of_finiteDimensional) data.center nonnegative start numerical
    (fun f z => linear_error f z) horizontal_margin vertical_margin size P
    (data.continuous.comp P.continuous) _
    (S.increasingPath_re_mono pb.1 qb.1 horizontal vertical)
    (S.increasingPath_im_mono pb.1 qb.1 horizontal vertical) ordered
  intro r
  obtain ⟨f, _, _, value⟩ := data.visible_closure (inside r)
  exact ⟨f, value⟩

/-- A right/down displacement increases the signed output coordinate, even across
arbitrarily many actual face switches and coherent pinches. -/
theorem signed_lt_of_opposite_coordinates (small_error : ε < 1 / 2)
    (linear_error : ∀ f z,
      ‖(D.coordinatePlacement K calibration (fiveSectorFrame t positive small i).place f).linear z -
        z‖ ≤ ε * ‖z‖)
    {p q : ℂ} (first : p ∈ closure data.strictDomain) (last : q ∈ closure data.strictDomain)
    (horizontal : p.re ≤ q.re) (vertical : q.im ≤ p.im)
    (different : p ≠ q) :
    (data.value p).re - (data.value p).im < (data.value q).re - (data.value q).im := by
  let frame := (fiveSectorFrame t positive small i).place
  let A := fun f => (D.centeredCoordinatePlacement K source calibration frame f).toAffineMap
  obtain ⟨c, cpositive, bounds⟩ := exists_common_affine_cone_bound A
    (fun f => affineAxisMargins_pos_of_linear_error (A f) small_error (fun z => linear_error f z))
  have pb := data.closed_bounded first
  have qb := data.closed_bounded last
  have inside (r : unitInterval) : Path.segment p q r ∈ closure data.strictDomain := by
    rcases le_total (p.re + p.im) (q.re + q.im) with before | after
    · have bounded := S.segmentPath_mem_bounded
        (show p ∈ S.boundedCarrier 0 (q.re + q.im) from ⟨pb.1, pb.2.1, before⟩)
        (show q ∈ S.boundedCarrier 0 (q.re + q.im) from ⟨qb.1, qb.2.1, le_rfl⟩)
        horizontal vertical r
      exact data.closed_initial last bounded.1 bounded.2
    · have bounded := S.segmentPath_mem_bounded
        (show p ∈ S.boundedCarrier 0 (p.re + p.im) from ⟨pb.1, pb.2.1, le_rfl⟩)
        (show q ∈ S.boundedCarrier 0 (p.re + p.im) from ⟨qb.1, qb.2.1, after⟩)
        horizontal vertical r
      exact data.closed_initial first bounded.1 bounded.2
  have selection : ∀ z ∈ closure data.strictDomain, ∃ f, data.value z = A f z := by
    intro z member
    obtain ⟨f, _, _, value⟩ := data.visible_closure member
    exact ⟨f, value⟩
  have bound := finite_selection_bound_along_path_on (closure data.strictDomain)
    (fun f => A f) (fun f => (A f).continuous_of_finiteDimensional)
    data.continuous.continuousOn selection (fun f => (bounds f).2)
    (Path.segment p q) inside (MonotoneStrip.segment_re_mono horizontal)
    (MonotoneStrip.segment_neg_im_mono vertical)
  simp only [neg_mul, one_mul] at bound
  have gap : 0 < (q.re - q.im) - (p.re - p.im) := by
    by_contra nonpositive
    apply different
    apply Complex.ext <;> linarith
  exact sub_pos.mp ((mul_pos cpositive gap).trans_le bound)

end Unfoldings.ConvexCap.RadialCutForest.RadialStripTraceData
