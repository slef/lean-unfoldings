module

public import Unfoldings.Cap.CenteredMapSourceError
public import Unfoldings.Cap.CenteredTraceValues

/-! Actual source-position error extends to every visible one-sided strip-trace point. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FacewiseDevelopment

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {retain : Set C.Seam} (D : FacewiseDevelopment C retain) (K : ConvexCap C)

theorem traceVisibleAt_mem_closure (q : Plane) (calibration frame : Plane ≃ₗᵢ[ℝ] ℂ)
    {G : ℂ → ℂ} {domain : Set ℂ} {z : ℂ}
    (trace : D.TraceVisibleAt K q calibration frame G domain z) : z ∈ closure domain := by
  obtain ⟨_, _, approach, _⟩ := trace
  exact closure_mono Set.inter_subset_left approach

theorem centered_trace_source_error (q : Plane) (calibration frame : Plane ≃ₗᵢ[ℝ] ℂ)
    {c b : ℝ} (nonnegative : 0 ≤ c)
    (linear_error : ∀ f z, ‖(D.coordinatePlacement K calibration frame f).linear z - z‖ ≤ c * ‖z‖)
    (S : MonotoneStrip) (E : Set ℂ)
    (first : S.lower.coordinate 0 = 0) (last : S.upper.coordinate 0 = 0)
    (pinches : S.RecoverablePinchesIn E 0 b)
    (inside : ∀ z, (z ∈ S.strictCarrier ∨ z ∈ E) → z.re + z.im ∈ Set.Icc 0 b →
      q + frame.symm z ∈ K.footprint ∧ D.ProjectedCoherentAt K (q + frame.symm z))
    {G : ℂ → ℂ} (continuous : Continuous G)
    (equal : Set.EqOn (D.centeredMap K q calibration frame) G
      {z | z ∈ S.strictCarrier ∧ z.re + z.im ∈ Set.Icc 0 b})
    {z : ℂ} (member : z ∈ closure {z | z ∈ S.strictCarrier ∧ z.re + z.im ∈ Set.Icc 0 b}) :
    ‖(G z - D.centeredMap K q calibration frame 0) - z‖ ≤ 2 * c * (z.re + z.im) := by
  let bounds := {z : ℂ |
    ‖(G z - D.centeredMap K q calibration frame 0) - z‖ ≤ 2 * c * (z.re + z.im)}
  have closed : IsClosed bounds := isClosed_le
    ((continuous.sub continuous_const).sub continuous_id).norm
    (continuous_const.mul (Complex.continuous_re.add Complex.continuous_im))
  apply closure_minimal (t := bounds) ?_ closed member
  intro w hw
  change ‖(G w - D.centeredMap K q calibration frame 0) - w‖ ≤ 2 * c * (w.re + w.im)
  rw [← equal hw]
  exact D.centeredMap_source_error (K := K) q calibration frame nonnegative linear_error
    S E first last pinches inside hw.1 hw.2

end Unfoldings.FacewiseDevelopment
