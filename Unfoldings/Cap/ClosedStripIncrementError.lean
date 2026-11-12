module

public import Unfoldings.Cap.RadialStripPointOrder
public import Unfoldings.Geometry.FiniteSelectionError

/-! Quantitative closed-trace progress through arbitrary actual face switches and vertices. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap.RadialCutForest.RadialStripTraceData

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexCap C} {source : Plane} {cuts : Set Plane} {N : K.RadialCutForest source cuts}
  {t : ℝ} {positive : 0 < t} {small : t < 1} {D : FacewiseDevelopment C N.retain}
  {calibration : Plane ≃ₗᵢ[ℝ] ℂ} {i : FiveSector} {S : MonotoneStrip} {ε cutoff : ℝ}
  (data : N.RadialStripTraceData positive small D calibration i S ε cutoff)

/-- Increment error, rather than only source error, extends to every comparable closed pair.
No vertex-height or circle-radius exclusions are used. -/
theorem closed_increment_error (nonnegative : 0 ≤ ε)
    (linear_error : ∀ f z,
      ‖(D.coordinatePlacement K calibration (fiveSectorFrame t positive small i).place f).linear z -
        z‖ ≤ ε * ‖z‖)
    {p q : ℂ} (first : p ∈ closure data.strictDomain) (last : q ∈ closure data.strictDomain)
    (horizontal : p.re ≤ q.re) (vertical : p.im ≤ q.im) :
    ‖(data.value q - q) - (data.value p - p)‖ ≤
      2 * ε * ((q.re + q.im) - (p.re + p.im)) := by
  let frame := (fiveSectorFrame t positive small i).place
  let A := fun f => (D.centeredCoordinatePlacement K source calibration frame f).toAffineMap
  have pb := data.closed_bounded first
  have qb := data.closed_bounded last
  have height : p.re + p.im ≤ q.re + q.im := add_le_add horizontal vertical
  let P := S.increasingPath pb.1 qb.1 horizontal vertical
  have inside (r : unitInterval) : P r ∈ closure data.strictDomain := by
    have bounded := S.increasingPath_mem_bounded
      (show p ∈ S.boundedCarrier 0 (q.re + q.im) from ⟨pb.1, pb.2.1, height⟩)
      (show q ∈ S.boundedCarrier 0 (q.re + q.im) from ⟨qb.1, qb.2.1, le_rfl⟩)
      horizontal vertical r
    exact data.closed_initial last bounded.1 bounded.2
  apply finite_selection_error_along_path (fun f z => A f z)
    (fun f => (A f).continuous_of_finiteDimensional) ε
    (fun f _ _ hre him => affine_near_identity_cone_error (A f) nonnegative
      (fun z => linear_error f z) hre him) P (data.continuous.comp P.continuous) _
    (S.increasingPath_re_mono pb.1 qb.1 horizontal vertical)
    (S.increasingPath_im_mono pb.1 qb.1 horizontal vertical)
  intro r
  obtain ⟨f, _, _, value⟩ := data.visible_closure (inside r)
  exact ⟨f, value⟩

/-- A positive physical margin in each coordinate gives strict developed progress,
even if either endpoint is an actual cut vertex. -/
theorem closed_coordinates_strict_of_increment_margin (nonnegative : 0 ≤ ε)
    (linear_error : ∀ f z,
      ‖(D.coordinatePlacement K calibration (fiveSectorFrame t positive small i).place f).linear z -
        z‖ ≤ ε * ‖z‖)
    {p q : ℂ} (first : p ∈ closure data.strictDomain) (last : q ∈ closure data.strictDomain)
    (horizontal : p.re ≤ q.re) (vertical : p.im ≤ q.im)
    (ordered : p.re + p.im < q.re + q.im)
    {μ : ℝ} (numerical : 2 * ε < μ)
    (re_margin : μ * ((q.re + q.im) - (p.re + p.im)) ≤ q.re - p.re)
    (im_margin : μ * ((q.re + q.im) - (p.re + p.im)) ≤ q.im - p.im) :
    (data.value p).re < (data.value q).re ∧ (data.value p).im < (data.value q).im := by
  have error := data.closed_increment_error nonnegative linear_error first last horizontal vertical
  have real_bound := (abs_le.mp ((Complex.abs_re_le_norm _).trans error)).1
  have imaginary_bound := (abs_le.mp ((Complex.abs_im_le_norm _).trans error)).1
  have strict := mul_lt_mul_of_pos_right numerical (sub_pos.mpr ordered)
  simp only [Complex.sub_re] at real_bound
  simp only [Complex.sub_im] at imaginary_bound
  constructor <;> linarith

end Unfoldings.ConvexCap.RadialCutForest.RadialStripTraceData
