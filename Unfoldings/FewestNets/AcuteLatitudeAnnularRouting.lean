module

public import Unfoldings.FewestNets.AcuteLatitudeOrientedChart
public import Unfoldings.FewestNets.AcuteLatitudeSelectedRoofs
public import Unfoldings.FewestNets.AcuteLatitudeRouting

/-! Actual annular components have the revised three-exit routing and curvature budgets. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FewestNets

open Real MeasureTheory AcuteLatitudeGrid
open scoped ENNReal

/-- The area of every oriented annular selector bounds the curvature budget
available for its entire affine-floor roof. -/
theorem volume_acuteLatitudeAnnular_le {a left right base apex height : ℝ}
    (positive : 0 < a) (small : a ≤ π / 6) (base_order : left ≤ right)
    (height_pos : 0 < height) (width : right - left < 1.010 * spacing a)
    (altitude : height < 1.052 * radius a) :
    volume (latitudeSlopeTriangle left right base apex height) <
      ENNReal.ofReal (0.0163 * a) := by
  rw [volume_latitudeSlopeTriangle base_order height_pos]
  have a_small : a < 0.524 := by linarith only [small, pi_lt_d6]
  have bh : (right - left) * height < 1.010 * spacing a * (1.052 * radius a) :=
    mul_lt_mul'' width altitude (sub_nonneg.mpr base_order) height_pos.le
  have br := spacing_mul_radius positive
  have tight : (right - left) * height / 2 < 0.0163 * a := by
    have scaled := mul_lt_mul_of_pos_right a_small positive
    nlinarith only [bh, br, scaled, positive]
  exact (ENNReal.ofReal_lt_ofReal_iff (show 0 < 0.0163 * a by positivity)).mpr tight

end Unfoldings.FewestNets

namespace Unfoldings.SpatialFolding.ConvexBoundary

open Real Cap MeasureTheory FewestNets AcuteLatitudeGrid
open scoped ENNReal

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {F : SpatialFolding C} (P : F.ConvexBoundary) (N : F.SupportingNormals)

/-- Place an actual annular component in the three-exit chart. The resulting
roof component is on the original faces, with the area and heading bounds
used for its graft. -/
theorem exists_acuteLatitude_annular_label_routing_selected {a : ℝ}
    (positive : 0 < a) (small : a ≤ π / 6)
    (placement : Space ≃ₗᵢ[ℝ] Space) (label : Face → Selector a)
    (chosen : ∀ f, placement (N.normal f) ∈ selectorSphere positive small (label f))
    (generic : ∀ f (i : ChordFace a) j, (chordBasis positive small i).coord j
      (placement (N.normal f)) ≠ 0)
    (angles : ∀ f i, (C.triangle f).cornerAngle i ≤ π / 2 - a)
    (k : AnnularTriangle a) (seed : Face) (seed_label : label seed = .inr k) :
    ∃ (frame : Space ≃ₗᵢ[ℝ] Space) (left right base apex height : ℝ)
      (base_pos : left < right) (height_pos : 0 < height),
      let normals := N.rotate frame
      let roof := (P.rotate frame).upperRoof normals
      let region := latitudeSlopeTriangle left right base apex height
      let B := latitudeTriangleSideDirections left right base apex height base_pos height_pos
      let compact := isCompact_latitudeSlopeTriangle left right base apex height
      ∃ (start : normals.UpperFace) (present : region.Nonempty)
        (H : ThreeExitStemWindows) (R : roof.ThreeExitComponentRouting start B compact present H),
        start.val = seed ∧ roof.normalSlope start ∈ region ∧
        Subtype.val '' roof.selectionComponent region start =
          ((C.labeledSeamGraph label).connectedComponentMk seed).supp ∧
        volume region < ENNReal.ofReal (0.0163 * a) ∧
        (∀ p ∈ region, ‖p‖ ≤ tan (0.568 * radius a)) ∧
        ∀ r : {r // r ∈ R.stems.choice.parents.roots},
          let exit := (R.rootHeadingChart r (R.rootExitDirection r)).arg
          let lo := R.rootWindowStart r
          max (lo + H.width) exit - min lo exit ≤ π / 2 - 0.170 * a := by
  obtain ⟨E, left, right, base, apex, height, reimage, width_low, width_high, height_low,
    height_high, east, west, radius_bound, _⟩ := exists_annularRoutingChart positive small k
  let frame := (placement.trans (selectorFrame (.inr k))).trans (horizontalChartIsometry E)
  let normals := N.rotate frame
  let roof := (P.rotate frame).upperRoof normals
  let region := latitudeSlopeTriangle left right base apex height
  have triangle : E '' selectorSlopes positive small (.inr k) = region := reimage
  obtain ⟨selected, no_boundary, upper⟩ :=
    P.acuteLatitude_reoriented_upperRoof_data N positive small placement label chosen generic (.inr k) E
  change (∀ f : normals.UpperFace, roof.normalSlope f ∈ E '' selectorSlopes positive small (.inr k)
    ↔ label f.val = .inr k) at selected
  change (∀ f : normals.UpperFace, roof.normalSlope f ∉
    frontier (E '' selectorSlopes positive small (.inr k))) at no_boundary
  rw [triangle] at selected no_boundary
  let start : normals.UpperFace := ⟨seed, upper seed seed_label⟩
  have present : roof.normalSlope start ∈ region := (selected start).mpr seed_label
  have original (f : normals.UpperFace) (i : Fin 3) :
      (normals.upperComplex.triangle f).cornerAngle i ≤ π / 2 - a := angles f.val i
  have base_pos := sub_pos.mp ((mul_pos (by norm_num : 0 < (0.8 : ℝ))
    (spacing_pos positive)).trans width_low)
  have height_pos := (mul_pos (by norm_num : 0 < (0.883 : ℝ)) (radius_pos positive)).trans height_low
  have tilt_pos : 0 < 0.568 * radius a := mul_pos (by norm_num) (radius_pos positive)
  obtain ⟨H, R, root⟩ := roof.exists_acuteLatitudeTriangleRouting start positive small tilt_pos
    le_rfl height_low width_high east west base_pos height_pos radius_bound no_boundary present original
  refine ⟨frame, left, right, base, apex, height, base_pos, height_pos, start,
    Set.nonempty_of_mem present, H, R, rfl, present, ?_, ?_, radius_bound, root⟩
  · exact P.upperRoof_selectionComponent_image_eq_labeled_component N label (.inr k)
      frame selected upper start seed_label
  · exact volume_acuteLatitudeAnnular_le positive small base_pos.le height_pos width_high height_high

/-- An annular component has its original three-exit routing and quantitative budgets. -/
theorem exists_acuteLatitude_annular_label_routing {a : ℝ}
    (positive : 0 < a) (small : a ≤ π / 6)
    (placement : Space ≃ₗᵢ[ℝ] Space) (label : Face → Selector a)
    (chosen : ∀ f, placement (N.normal f) ∈ selectorSphere positive small (label f))
    (generic : ∀ f (i : ChordFace a) j, (chordBasis positive small i).coord j
      (placement (N.normal f)) ≠ 0)
    (angles : ∀ f i, (C.triangle f).cornerAngle i ≤ π / 2 - a)
    (k : AnnularTriangle a) (seed : Face) (seed_label : label seed = .inr k) :
    ∃ (frame : Space ≃ₗᵢ[ℝ] Space) (left right base apex height : ℝ)
      (base_pos : left < right) (height_pos : 0 < height),
      let normals := N.rotate frame
      let roof := (P.rotate frame).upperRoof normals
      let region := latitudeSlopeTriangle left right base apex height
      let B := latitudeTriangleSideDirections left right base apex height base_pos height_pos
      let compact := isCompact_latitudeSlopeTriangle left right base apex height
      ∃ (start : normals.UpperFace) (present : region.Nonempty)
        (H : ThreeExitStemWindows) (R : roof.ThreeExitComponentRouting start B compact present H),
        start.val = seed ∧
        Subtype.val '' roof.selectionComponent region start =
          ((C.labeledSeamGraph label).connectedComponentMk seed).supp ∧
        volume region < ENNReal.ofReal (0.0163 * a) ∧
        (∀ p ∈ region, ‖p‖ ≤ tan (0.568 * radius a)) ∧
        ∀ r : {r // r ∈ R.stems.choice.parents.roots},
          let exit := (R.rootHeadingChart r (R.rootExitDirection r)).arg
          let lo := R.rootWindowStart r
          max (lo + H.width) exit - min lo exit ≤ π / 2 - 0.170 * a := by
  obtain ⟨frame, left, right, base, apex, height, base_pos, height_pos,
    start, present, H, R, seed_eq, _, component, area, radius_bound, root⟩ :=
    P.exists_acuteLatitude_annular_label_routing_selected N positive small placement label
      chosen generic angles k seed seed_label
  exact ⟨frame, left, right, base, apex, height, base_pos, height_pos,
    start, present, H, R, seed_eq, component, area, radius_bound, root⟩

end Unfoldings.SpatialFolding.ConvexBoundary
