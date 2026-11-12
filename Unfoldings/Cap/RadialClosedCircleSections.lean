module

public import Unfoldings.Cap.ClosedStripCircleSection
public import Unfoldings.Cap.ClosedCirclePinches
public import Unfoldings.Geometry.StripSlabApproach

/-! Every actual approached circle point supplies a closed section, without exceptional radii. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap.RadialCutForest.RadialStripTraceData

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexCap C} {source : Plane} {cuts : Set Plane} {N : K.RadialCutForest source cuts}
  {D : FacewiseDevelopment C N.retain} {t : ℝ} {positive : 0 < t} {small : t < 1}
  {calibration : Plane ≃ₗᵢ[ℝ] ℂ} {i : FiveSector} {S : MonotoneStrip} {ε cutoff : ℝ}
  (data : N.RadialStripTraceData positive small D calibration i S ε cutoff)

/-- Controlled closed circle points occur strictly between the source and cutoff heights. -/
theorem closed_circle_height_mem_Ioo {radius : ℝ} (radius_positive : 0 < radius)
    (far : radius < (1 / 2 - ε) * cutoff)
    {z : ℂ} (closed : z ∈ closure data.strictDomain)
    (size : ‖data.value z - data.center‖ = radius) :
    z.re + z.im ∈ Set.Ioo 0 cutoff := by
  have positive_height := data.closed_height_pos_of_norm closed (by rwa [size])
  obtain ⟨active, member⟩ := closure_nonempty_iff.mp ⟨z, closed⟩
  have before : z.re + z.im < cutoff :=
    lt_of_le_of_ne (data.closed_bounded closed).2.2 (fun equal =>
      data.end_levels_avoid_circle member radius_positive far closed (Or.inr equal) size)
  exact ⟨positive_height, before⟩

/-- At a controlled positive circle, both open and closed physical slab conventions agree. -/
theorem closed_circle_point_mem_closure_openSlab {radius : ℝ} (radius_positive : 0 < radius)
    (far : radius < (1 / 2 - ε) * cutoff)
    {z : ℂ} (closed : z ∈ closure data.strictDomain)
    (size : ‖data.value z - data.center‖ = radius) : z ∈ closure (S.openSlab 0 cutoff) :=
  S.mem_closure_openSlab_of_height closed
    (data.closed_circle_height_mem_Ioo radius_positive far closed size)

/-- A closed-only pinch is retained as a degenerate section, rather than discarded as an
exceptional radius. A genuine open circle intersection gives the existing nonempty slice. -/
theorem closed_circle_section_of_approached_point {μ : ℝ} (small_error : ε < μ)
    (margin : ∀ z ∈ S.carrier, 0 ≤ z.re + z.im →
      μ * (z.re + z.im) ≤ z.re ∧ μ * (z.re + z.im) ≤ z.im)
    {radius : ℝ} (radius_positive : 0 < radius)
    (far : radius < (1 / 2 - ε) * cutoff)
    {z : ℂ} (approached : z ∈ closure (S.openSlab 0 cutoff))
    (size : ‖data.value z - data.center‖ = radius) :
    Nonempty (S.ClosedBankCircleSection data.value data.center cutoff radius) := by
  by_cases meets : (data.value '' S.openSlab 0 cutoff ∩
      {z | ‖z - data.center‖ = radius}).Nonempty
  · obtain ⟨slice⟩ := data.circle_slice small_error margin radius_positive far meets
    exact ⟨slice.toClosedSection⟩
  · have empty := Set.not_nonempty_iff_eq_empty.mp meets
    have pinch := data.closed_circle_point_is_pinch_of_empty radius_positive far empty approached
      size
    have subset : S.openSlab 0 cutoff ⊆ data.strictDomain :=
      fun _ member => ⟨member.1, member.2.1.le, member.2.2.le⟩
    have closed := closure_mono subset approached
    have bounded := data.closed_bounded closed
    refine ⟨{
      lowerHeight := z.re + z.im
      upperHeight := z.re + z.im
      lower_bounds := bounded.2
      upper_bounds := bounded.2
      lower_closed := ?_
      upper_closed := ?_
      lower_radius := ?_
      upper_radius := ?_ }⟩
    · rw [← pinch.2.1]
      exact closed
    · rw [← pinch.2.2]
      exact closed
    · rwa [← pinch.2.1]
    · rwa [← pinch.2.2]

/-- On an absent open circle all approached contacts coincide physically, even at a cut vertex. -/
theorem closed_circle_preimages_eq_of_empty {radius : ℝ} (radius_positive : 0 < radius)
    (far : radius < (1 / 2 - ε) * cutoff)
    (empty : data.value '' S.openSlab 0 cutoff ∩ {z | ‖z - data.center‖ = radius} = ∅)
    {x y : ℂ} (first : x ∈ closure (S.openSlab 0 cutoff))
    (last : y ∈ closure (S.openSlab 0 cutoff))
    (first_size : ‖data.value x - data.center‖ = radius)
    (last_size : ‖data.value y - data.center‖ = radius) : x = y := by
  have first_pinch := data.closed_circle_point_is_pinch_of_empty radius_positive far empty first
    first_size
  have last_pinch := data.closed_circle_point_is_pinch_of_empty radius_positive far empty last
    last_size
  have subset : S.openSlab 0 cutoff ⊆ data.strictDomain :=
    fun _ member => ⟨member.1, member.2.1.le, member.2.2.le⟩
  have first_closed := closure_mono subset first
  have last_closed := closure_mono subset last
  obtain ⟨active, member⟩ := closure_nonempty_iff.mp ⟨x, first_closed⟩
  have source_values := data.source_bank_values member
  have heights := data.radial.closed_bank_circle_height_unique data.continuous S.lower (Or.inl rfl)
    source_values.1 (data.closed_bounded first_closed).2.1 (data.closed_bounded last_closed).2.1
    radius_positive (first_pinch.2.1 ▸ first_closed) (last_pinch.2.1 ▸ last_closed)
    (first_pinch.2.1 ▸ first_size) (last_pinch.2.1 ▸ last_size)
  exact first_pinch.2.1.trans ((congrArg S.lower.point heights).trans last_pinch.2.1.symm)

/-- A closed-only circle section is exactly one developed point. -/
theorem closed_circle_image_eq_singleton_of_empty {radius : ℝ} (radius_positive : 0 < radius)
    (far : radius < (1 / 2 - ε) * cutoff)
    (empty : data.value '' S.openSlab 0 cutoff ∩ {z | ‖z - data.center‖ = radius} = ∅)
    {x : ℂ} (closed : x ∈ closure (S.openSlab 0 cutoff))
    (size : ‖data.value x - data.center‖ = radius) :
    data.value '' closure (S.openSlab 0 cutoff) ∩ {z | ‖z - data.center‖ = radius} =
      {data.value x} := by
  ext z
  constructor
  · rintro ⟨⟨y, approached, rfl⟩, y_size⟩
    rw [data.closed_circle_preimages_eq_of_empty radius_positive far empty approached closed
      y_size size]
    exact Set.mem_singleton _
  · intro member
    rw [Set.mem_singleton_iff.mp member]
    exact ⟨⟨x, closed, rfl⟩, size⟩

end Unfoldings.ConvexCap.RadialCutForest.RadialStripTraceData
