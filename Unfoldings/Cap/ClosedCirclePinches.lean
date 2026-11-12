module

public import Unfoldings.Cap.ActiveBankCircleCrossing
public import Unfoldings.Cap.RadialStripPointOrder
public import Unfoldings.Cap.RegularCircleRadius
public import Unfoldings.Cap.RadialStripCircleBanks
public import Unfoldings.Geometry.AffineGraphPinches

/-! An approached point on an absent controlled circle is a genuine physical strip pinch. -/

@[expose] public section

namespace Unfoldings.ConvexCap.RadialCutForest.RadialStripTraceData

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexCap C} {source : Plane} {cuts : Set Plane} {N : K.RadialCutForest source cuts}
  {D : FacewiseDevelopment C N.retain} {t : ℝ} {positive : 0 < t} {small : t < 1}
  {calibration : Plane ≃ₗᵢ[ℝ] ℂ} {i : FiveSector} {S : MonotoneStrip} {ε cutoff : ℝ}

/-- No exceptional radii are removed. The only approached contacts left when the
open slice is empty have coincident physical lower and upper bank coordinates. -/
theorem closed_circle_point_is_pinch_of_empty
    (data : N.RadialStripTraceData positive small D calibration i S ε cutoff)
    {radius : ℝ} (radius_positive : 0 < radius)
    (far : radius < (1 / 2 - ε) * cutoff)
    (empty : data.value '' S.openSlab 0 cutoff ∩ {z | ‖z - data.center‖ = radius} = ∅)
    {z : ℂ} (approached : z ∈ closure (S.openSlab 0 cutoff))
    (size : ‖data.value z - data.center‖ = radius) :
    S.lower.coordinate (z.re + z.im) = S.upper.coordinate (z.re + z.im) ∧
      z = S.lower.point (z.re + z.im) ∧ z = S.upper.point (z.re + z.im) := by
  have subset : S.openSlab 0 cutoff ⊆ data.strictDomain :=
    fun _ member => ⟨member.1, member.2.1.le, member.2.2.le⟩
  have closed := closure_mono subset approached
  obtain ⟨active, active_member⟩ := closure_nonempty_iff.mp ⟨z, closed⟩
  have avoid := data.end_levels_avoid_circle active_member radius_positive far closed
  have height_positive := data.closed_height_pos_of_norm closed
    (by rw [size]; exact radius_positive)
  have height_before : z.re + z.im < cutoff :=
    lt_of_le_of_ne (data.closed_bounded closed).2.2
      (fun equal => avoid (Or.inr equal) size)
  have impossible : ¬ (data.value '' S.openSlab 0 cutoff ∩
      {z | ‖z - data.center‖ = radius}).Nonempty := by
    rw [empty]
    exact Set.not_nonempty_empty
  have outside : z ∉ S.openSlab 0 cutoff :=
    fun member => impossible ⟨data.value z, ⟨z, member, rfl⟩, size⟩
  have boundary : z ∈ frontier (S.openSlab 0 cutoff) :=
    ⟨approached, by simpa only [(S.isOpen_openSlab 0 cutoff).interior_eq] using outside⟩
  have no_width : ¬ S.lower.coordinate (z.re + z.im) < S.upper.coordinate (z.re + z.im) := by
    intro width
    rcases S.frontier_openSlab_cases 0 cutoff boundary with lower | upper | start | finish
    · apply impossible
      exact data.radial.circle_nonempty_at_closed_active_bank data.continuous S.lower
        (Or.inl rfl) ⟨height_positive, height_before⟩ (by rwa [← lower])
        (by rwa [← lower]) width
    · apply impossible
      exact data.radial.circle_nonempty_at_closed_active_bank data.continuous S.upper
        (Or.inr rfl) ⟨height_positive, height_before⟩ (by rwa [← upper])
        (by rwa [← upper]) width
    · exact avoid (Or.inl start) size
    · exact avoid (Or.inr finish) size
  have zero := le_antisymm (S.ordered (z.re + z.im)) (le_of_not_gt no_width)
  have member := (S.closure_openSlab_subset 0 cutoff approached).1
  have lower_coordinate : S.lower.coordinate (z.re + z.im) = z.re :=
    le_antisymm member.1 (member.2.trans_eq zero.symm)
  have upper_coordinate : S.upper.coordinate (z.re + z.im) = z.re :=
    zero.symm.trans lower_coordinate
  exact ⟨zero, (S.lower.point_eq_of_coordinate z lower_coordinate).symm,
    (S.upper.point_eq_of_coordinate z upper_coordinate).symm⟩

/-- In the actual mesh, an empty-circle contact is an approached cut vertex. -/
theorem closed_circle_empty_point_on_cut_vertex
    (data : N.RadialStripTraceData positive small D calibration i S ε cutoff)
    (pinches : S.ApproachedPinchesIn
      (Set.range (fun w : {w : C.Vertex Set.univ // K.projectedVertex w ∈ cuts} =>
        (fiveSectorFrame t positive small i).place (K.projectedVertex w.val - source))) 0 cutoff)
    {radius : ℝ} (radius_positive : 0 < radius)
    (far : radius < (1 / 2 - ε) * cutoff)
    (empty : data.value '' S.openSlab 0 cutoff ∩ {z | ‖z - data.center‖ = radius} = ∅)
    {z : ℂ} (approached : z ∈ closure (S.openSlab 0 cutoff))
    (size : ‖data.value z - data.center‖ = radius) :
    ∃ w : C.Vertex Set.univ, K.projectedVertex w ∈ cuts ∧
      source + (fiveSectorFrame t positive small i).place.symm z = K.projectedVertex w := by
  have pinch := data.closed_circle_point_is_pinch_of_empty radius_positive far empty approached size
  have subset : S.openSlab 0 cutoff ⊆ data.strictDomain :=
    fun _ member => ⟨member.1, member.2.1.le, member.2.2.le⟩
  have closed := closure_mono subset approached
  obtain ⟨active, active_member⟩ := closure_nonempty_iff.mp ⟨z, closed⟩
  have height_positive := data.closed_height_pos_of_norm closed
    (by rw [size]; exact radius_positive)
  have height_before : z.re + z.im < cutoff :=
    lt_of_le_of_ne (data.closed_bounded closed).2.2
      (fun equal => data.end_levels_avoid_circle active_member radius_positive far closed
        (Or.inr equal) size)
  have approached_bank : S.lower.point (z.re + z.im) ∈ closure S.strictCarrier := by
    rw [← pinch.2.1]
    exact closure_mono (fun _ member => member.1) approached
  obtain ⟨w, at_w⟩ := pinches _ ⟨height_positive, height_before⟩ pinch.1 approached_bank
  refine ⟨w.val, w.property, ?_⟩
  rw [← pinch.2.1] at at_w
  rw [← at_w, LinearIsometryEquiv.symm_apply_apply]
  abel

/-- The additional maximal-radius exception is unnecessary for an approached point:
an absent circle through such a point already belongs to the actual vertex-radius set. -/
theorem closed_circle_empty_radius_mem_vertexRadii
    (data : N.RadialStripTraceData positive small D calibration i S ε cutoff)
    (pinches : S.ApproachedPinchesIn
      (Set.range (fun w : {w : C.Vertex Set.univ // K.projectedVertex w ∈ cuts} =>
        (fiveSectorFrame t positive small i).place (K.projectedVertex w.val - source))) 0 cutoff)
    {radius : ℝ} (radius_positive : 0 < radius)
    (far : radius < (1 / 2 - ε) * cutoff)
    (empty : data.value '' S.openSlab 0 cutoff ∩ {z | ‖z - data.center‖ = radius} = ∅)
    {z : ℂ} (approached : z ∈ closure (S.openSlab 0 cutoff))
    (size : ‖data.value z - data.center‖ = radius) :
    radius ∈ D.fiveSectorVertexRadii K source calibration positive small := by
  obtain ⟨w, _, physical⟩ := data.closed_circle_empty_point_on_cut_vertex pinches
    radius_positive far empty approached size
  have subset : S.openSlab 0 cutoff ⊆ data.strictDomain :=
    fun _ member => ⟨member.1, member.2.1.le, member.2.2.le⟩
  obtain ⟨f, _, _, value⟩ := data.visible_closure (closure_mono subset approached)
  let frame := (fiveSectorFrame t positive small i).place
  have inverse : frame.symm z = K.projectedVertex w - source := by
    rw [← physical]
    abel
  have input : z = frame (K.projectedVertex w - source) := by
    simpa only [frame.apply_symm_apply] using congrArg frame inverse
  refine ⟨(i, f, w), ?_⟩
  change ‖D.centeredCoordinatePlacement K source calibration frame f
      (frame (K.projectedVertex w - source)) -
    D.centeredMap K source calibration frame 0‖ = radius
  rw [← input, ← value]
  exact size

/-- Every approached nonvertex circle point has an actual open strip slice. -/
theorem circle_nonempty_of_approached_point_off_vertexRadii
    (data : N.RadialStripTraceData positive small D calibration i S ε cutoff)
    (pinches : S.ApproachedPinchesIn
      (Set.range (fun w : {w : C.Vertex Set.univ // K.projectedVertex w ∈ cuts} =>
        (fiveSectorFrame t positive small i).place (K.projectedVertex w.val - source))) 0 cutoff)
    {radius : ℝ} (radius_positive : 0 < radius)
    (far : radius < (1 / 2 - ε) * cutoff)
    (outside : radius ∉ D.fiveSectorVertexRadii K source calibration positive small)
    {z : ℂ} (approached : z ∈ closure (S.openSlab 0 cutoff))
    (size : ‖data.value z - data.center‖ = radius) :
    (data.value '' S.openSlab 0 cutoff ∩ {z | ‖z - data.center‖ = radius}).Nonempty := by
  by_contra absent
  have empty := Set.not_nonempty_iff_eq_empty.mp absent
  exact outside (data.closed_circle_empty_radius_mem_vertexRadii pinches radius_positive far
    empty approached size)

/-- Any approached nonvertex circle point supplies the actual slice used by the
waterfall survivor order and the closed-contact comparisons. -/
theorem circle_slice_of_approached_point_off_vertexRadii
    (data : N.RadialStripTraceData positive small D calibration i S ε cutoff)
    (pinches : S.ApproachedPinchesIn
      (Set.range (fun w : {w : C.Vertex Set.univ // K.projectedVertex w ∈ cuts} =>
        (fiveSectorFrame t positive small i).place (K.projectedVertex w.val - source))) 0 cutoff)
    {μ : ℝ} (small_error : ε < μ)
    (margin : ∀ z ∈ S.carrier, 0 ≤ z.re + z.im →
      μ * (z.re + z.im) ≤ z.re ∧ μ * (z.re + z.im) ≤ z.im)
    {radius : ℝ} (radius_positive : 0 < radius)
    (far : radius < (1 / 2 - ε) * cutoff)
    (outside : radius ∉ D.fiveSectorVertexRadii K source calibration positive small)
    {z : ℂ} (approached : z ∈ closure (S.openSlab 0 cutoff))
    (size : ‖data.value z - data.center‖ = radius) :
    Nonempty (S.BankCircleSlice data.value data.center cutoff radius) :=
  data.circle_slice small_error margin radius_positive far
    (data.circle_nonempty_of_approached_point_off_vertexRadii pinches radius_positive far
      outside approached size)

end Unfoldings.ConvexCap.RadialCutForest.RadialStripTraceData
