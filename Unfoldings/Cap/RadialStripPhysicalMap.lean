module

public import Unfoldings.Cap.RadialStripTraceBounds
public import Unfoldings.Topology.CompactImageFrontier

/-! Express every actual strip and source-circle slice in one common developed plane. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap.RadialCutForest.RadialStripTraceData

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexCap C} {source : Plane} {cuts : Set Plane} {N : K.RadialCutForest source cuts}
  {t : ℝ} {positive : 0 < t} {small : t < 1} {D : FacewiseDevelopment C N.retain}
  {calibration : Plane ≃ₗᵢ[ℝ] ℂ} {i : FiveSector} {S : MonotoneStrip} {ε cutoff : ℝ}

def physicalDomain
    (_data : N.RadialStripTraceData positive small D calibration i S ε cutoff) : Set Plane :=
  (fun p => (fiveSectorFrame t positive small i).place (p - source)) ⁻¹' S.openSlab 0 cutoff

def outputFrame
    (_data : N.RadialStripTraceData positive small D calibration i S ε cutoff) :
    Plane ≃ₗᵢ[ℝ] ℂ :=
  calibration.trans (Complex.orthonormalBasisOneI.repr.trans
    (fiveSectorFrame t positive small i).place)

variable (data : N.RadialStripTraceData positive small D calibration i S ε cutoff)

theorem isOpen_physicalDomain : IsOpen data.physicalDomain :=
  (S.isOpen_openSlab 0 cutoff).preimage
    ((fiveSectorFrame t positive small i).place.continuous.comp
      (continuous_id.sub continuous_const))

theorem center_eq_outputFrame : data.center = data.outputFrame (D.projectedMap K source) := by
  change D.centeredMap K source calibration _ 0 = _
  simp only [FacewiseDevelopment.centeredMap, map_zero, add_zero]
  rfl

theorem physical_value {p : Plane} (member : p ∈ data.physicalDomain) :
    data.value ((fiveSectorFrame t positive small i).place (p - source)) =
      data.outputFrame (D.projectedMap K p) := by
  let frame := (fiveSectorFrame t positive small i).place
  have strict : frame (p - source) ∈ data.strictDomain :=
    ⟨member.1, member.2.1.le, member.2.2.le⟩
  have input : source + frame.symm (frame (p - source)) = p := by
    rw [frame.symm_apply_apply]
    abel
  rw [← data.equal strict, FacewiseDevelopment.centeredMap, input]
  rfl

theorem physical_injective : Set.InjOn (D.projectedMap K) data.physicalDomain := by
  intro p first q last equal
  have first_closed : (fiveSectorFrame t positive small i).place (p - source) ∈
      closure data.strictDomain := subset_closure ⟨first.1, first.2.1.le, first.2.2.le⟩
  have last_closed : (fiveSectorFrame t positive small i).place (q - source) ∈
      closure data.strictDomain := subset_closure ⟨last.1, last.2.1.le, last.2.2.le⟩
  have same := data.closed_injective first_closed last_closed
    ((data.physical_value first).trans
      ((congrArg data.outputFrame equal).trans (data.physical_value last).symm))
  exact sub_left_injective ((fiveSectorFrame t positive small i).place.injective same)

theorem physical_distance {p : Plane} (member : p ∈ data.physicalDomain) :
    ‖data.value ((fiveSectorFrame t positive small i).place (p - source)) - data.center‖ =
      ‖D.projectedMap K p - D.projectedMap K source‖ := by
  rw [data.physical_value member, data.center_eq_outputFrame, ← data.outputFrame.map_sub,
    data.outputFrame.norm_map]

theorem image_physicalDomain :
    D.projectedMap K '' data.physicalDomain = data.outputFrame.symm ''
      (data.value '' S.openSlab 0 cutoff) := by
  let frame := (fiveSectorFrame t positive small i).place
  ext p
  constructor
  · rintro ⟨q, member, rfl⟩
    refine ⟨data.value (frame (q - source)), ⟨frame (q - source), member, rfl⟩, ?_⟩
    rw [data.physical_value member, data.outputFrame.symm_apply_apply]
  · rintro ⟨_, ⟨z, member, rfl⟩, rfl⟩
    let q := source + frame.symm z
    have at_q : frame (q - source) = z := by
      simp only [q, add_sub_cancel_left, frame.apply_symm_apply]
    have inside : q ∈ data.physicalDomain := by
      change frame (q - source) ∈ S.openSlab 0 cutoff
      rwa [at_q]
    refine ⟨q, inside, ?_⟩
    rw [← at_q, data.physical_value inside, data.outputFrame.symm_apply_apply]

theorem outputFrame_symm_source_distance (z : ℂ) :
    ‖data.outputFrame.symm z - D.projectedMap K source‖ = ‖z - data.center‖ := by
  calc
    _ = ‖data.outputFrame (data.outputFrame.symm z - D.projectedMap K source)‖ :=
      (data.outputFrame.norm_map _).symm
    _ = _ := by
      rw [map_sub, data.outputFrame.apply_symm_apply, ← data.center_eq_outputFrame]

theorem circle_image_physicalDomain (radius : ℝ) :
    (D.projectedMap K '' data.physicalDomain ∩
      {p | ‖p - D.projectedMap K source‖ = radius}) =
    data.outputFrame.symm '' (data.value '' S.openSlab 0 cutoff ∩
      {z | ‖z - data.center‖ = radius}) := by
  rw [data.image_physicalDomain]
  ext p
  constructor
  · rintro ⟨⟨z, member, rfl⟩, size⟩
    exact ⟨z, ⟨member, (data.outputFrame_symm_source_distance z).symm.trans size⟩, rfl⟩
  · rintro ⟨z, ⟨member, size⟩, rfl⟩
    exact ⟨⟨z, member, rfl⟩, (data.outputFrame_symm_source_distance z).trans size⟩

theorem isOpen_image_openSlab : IsOpen (data.value '' S.openSlab 0 cutoff) := by
  let patch : C(S.openSlab 0 cutoff, ℂ) :=
    ⟨fun z => data.value z.val, data.continuous.comp continuous_subtype_val⟩
  have injective : Function.Injective patch := by
    intro x y equal
    apply Subtype.ext
    exact data.closed_injective
      (subset_closure ⟨x.property.1, x.property.2.1.le, x.property.2.2.le⟩)
      (subset_closure ⟨y.property.1, y.property.2.1.le, y.property.2.2.le⟩) equal
  have range : Set.range patch = data.value '' S.openSlab 0 cutoff := by
    ext z
    constructor
    · rintro ⟨x, equal⟩
      exact ⟨x.val, x.property, equal⟩
    · rintro ⟨x, member, equal⟩
      exact ⟨⟨x, member⟩, equal⟩
  rw [← range]
  exact PlanarTopology.isOpen_complex_range_of_continuous_injective
    (S.isOpen_openSlab 0 cutoff) patch injective

theorem isOpen_image_physicalDomain : IsOpen (D.projectedMap K '' data.physicalDomain) := by
  rw [data.image_physicalDomain]
  exact data.outputFrame.symm.toHomeomorph.isOpenMap _ data.isOpen_image_openSlab

end Unfoldings.ConvexCap.RadialCutForest.RadialStripTraceData
