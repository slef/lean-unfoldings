module

public import Unfoldings.Cap.CenteredTraceSourceError
public import Unfoldings.Geometry.HeightGraphRadial

/-! Actual visible bank traces progress radially under uniform chart and sector margins. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FacewiseDevelopment

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {retain : Set C.Seam} (D : FacewiseDevelopment C retain) (K : ConvexCap C)

/-- Position error and linear chart error supply the positive radial tests. The trace
may switch actual faces at arbitrary points, including coherent branch endpoints. -/
theorem centered_visible_heightGraph_radial (q : Plane) (calibration frame : Plane ≃ₗᵢ[ℝ] ℂ)
    {c b μ : ℝ} (nonnegative : 0 ≤ c)
    (linear_error : ∀ f z, ‖(D.coordinatePlacement K calibration frame f).linear z - z‖ ≤ c * ‖z‖)
    (S : MonotoneStrip) (E : Set ℂ)
    (first : S.lower.coordinate 0 = 0) (last : S.upper.coordinate 0 = 0)
    (pinches : S.RecoverablePinchesIn E 0 b)
    (inside : ∀ z, (z ∈ S.strictCarrier ∨ z ∈ E) → z.re + z.im ∈ Set.Icc 0 b →
      q + frame.symm z ∈ K.footprint ∧ D.ProjectedCoherentAt K (q + frame.symm z))
    {G : ℂ → ℂ} (continuous : Continuous G)
    (equal : Set.EqOn (D.centeredMap K q calibration frame) G
      {z | z ∈ S.strictCarrier ∧ z.re + z.im ∈ Set.Icc 0 b})
    (H : MonotoneHeightGraph) {a d : ℝ} (positive : 0 < a) (ordered : a < d)
    (small : c * (1 + 2 * c) < μ - 2 * c)
    (coordinates : μ * a ≤ (H.point a).re ∧ μ * a ≤ (H.point a).im)
    (norm_bound : ‖H.point a‖ ≤ a)
    (traces : ∀ h ∈ Set.Icc a d, D.TraceVisibleAt K q calibration frame G
      {z | z ∈ S.strictCarrier ∧ z.re + z.im ∈ Set.Icc 0 b} (H.point h)) :
    ‖G (H.point a) - D.centeredMap K q calibration frame 0‖ <
      ‖G (H.point d) - D.centeredMap K q calibration frame 0‖ := by
  have visible := traces a ⟨le_rfl, ordered.le⟩
  have source_error := D.centered_trace_source_error K q calibration frame nonnegative
    linear_error S E first last pinches inside continuous equal
    (D.traceVisibleAt_mem_closure K q calibration frame visible)
  rw [H.point_height] at source_error
  let w := G (H.point a) - D.centeredMap K q calibration frame 0
  change ‖w - H.point a‖ ≤ 2 * c * a at source_error
  have horizontal := (abs_le.mp ((Complex.abs_re_le_norm _).trans source_error)).1
  have vertical := (abs_le.mp ((Complex.abs_im_le_norm _).trans source_error)).1
  simp only [Complex.sub_re] at horizontal
  simp only [Complex.sub_im] at vertical
  have margins : (μ - 2 * c) * a ≤ w.re ∧ (μ - 2 * c) * a ≤ w.im := by
    constructor <;> nlinarith [coordinates.1, coordinates.2]
  have size : ‖w‖ ≤ (1 + 2 * c) * a := by
    have triangle := norm_add_le (w - H.point a) (H.point a)
    rw [sub_add_cancel] at triangle
    nlinarith
  let A := fun f => (D.centeredCoordinatePlacement K q calibration frame f).toAffineMap
  apply H.finite_near_identity_selection_radial A
    (fun f => (A f).continuous_of_finiteDimensional) G continuous
    (D.centeredMap K q calibration frame 0) ordered nonnegative positive small
    (fun f z => linear_error f z) margins.1 margins.2 size
  intro h member
  obtain ⟨f, _, _, value⟩ := traces h member
  exact ⟨f, value⟩

end Unfoldings.FacewiseDevelopment
