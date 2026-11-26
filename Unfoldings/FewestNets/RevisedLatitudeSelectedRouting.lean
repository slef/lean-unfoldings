module

public import Unfoldings.FewestNets.RevisedLatitudeAnnularArea
public import Unfoldings.FewestNets.RevisedLatitudeSelectedRoofs

/-! The actual revised annular components have the full three-exit margin. -/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialFolding.ConvexBoundary

open FewestNets RevisedLatitudeGrid Cap Real MeasureTheory
open scoped ENNReal

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {F : SpatialFolding C} (P : F.ConvexBoundary) (N : F.SupportingNormals)

set_option maxHeartbeats 2000000 in
/-- An actual annular label produces a reoriented chart, its routed original
component, and a strict margin above its projection and normal-area budget. -/
theorem exists_revisedLatitude_annular_label_routing {a : ℝ}
    (positive : 0 < a) (small : a ≤ π / 6)
    (placement : Space ≃ₗᵢ[ℝ] Space) (label : Face → Selector a)
    (chosen : ∀ f, placement (N.normal f) ∈ selectorSphere positive small (label f))
    (generic : ∀ f (i : (rings a).ChordFace) j,
      (LatitudeRings.chordBasis (rings_oriented positive small) i).coord j
        (placement (N.normal f)) ≠ 0)
    (angles : ∀ f i, (C.triangle f).cornerAngle i ≤ π / 2 - a)
    (k : AnnularTriangle a) (seed : Face) (seed_label : label seed = .inr k) :
    ∃ (D : AnnularChartData positive small k) (bp : -D.halfBase < D.halfBase) (φ σ : ℝ),
      let frame := (placement.trans (selectorFrame (.inr k))).trans
        (horizontalChartIsometry D.reorient)
      let normals := N.rotate frame
      let roof := (P.rotate frame).upperRoof normals
      let S := latitudeSlopeTriangle (-D.halfBase) D.halfBase D.base D.apex D.height
      let B := latitudeTriangleSideDirections (-D.halfBase) D.halfBase D.base D.apex D.height bp D.height_pos
      let compact := isCompact_latitudeSlopeTriangle (-D.halfBase) D.halfBase D.base D.apex D.height
      ∃ (start : normals.UpperFace) (present : S.Nonempty)
        (H : ThreeExitStemWindows) (R : roof.ThreeExitComponentRouting start B compact present H),
        roof.normalSlope start ∈ S ∧
        Subtype.val '' roof.selectionComponent S start =
          ((C.labeledSeamGraph label).connectedComponentMk seed).supp ∧
        0 < φ ∧ φ ≤ 0.297 ∧
        (∀ p ∈ S, ‖p‖ ≤ tan φ) ∧
        (2 * arcsin ((1 - cos φ) / (1 + cos φ)) +
          (solidAngleMeasure (gnomonicNormal '' S)).toReal +
          (spacing a / (2 * 0.9612)) * ordinateBound a (isPolarStrip a k.1.val) < σ) ∧
        0 ≤ π / 2 - σ ∧
        (∀ r : {r // r ∈ R.stems.choice.parents.roots},
          let exit := (R.rootHeadingChart r (R.rootExitDirection r)).arg
          let lo := R.rootWindowStart r
          max (lo + H.width) exit - min lo exit ≤ π / 2 - σ) := by
  obtain ⟨D⟩ := exists_annularChartData positive small k
  obtain ⟨φ, φpos, φsmall, distortion, radius⟩ := D.exists_tilt
  let frame := (placement.trans (selectorFrame (.inr k))).trans
    (horizontalChartIsometry D.reorient)
  let normals := N.rotate frame
  let roof := (P.rotate frame).upperRoof normals
  let S := latitudeSlopeTriangle (-D.halfBase) D.halfBase D.base D.apex D.height
  have triangle : D.reorient '' selectorSlopes positive small (.inr k) = S := D.selector_eq
  obtain ⟨selected, generic_local, upper⟩ :=
    P.revisedLatitude_reoriented_upperRoof_data N positive small placement label chosen generic
      (.inr k) D.reorient
  change (∀ f : normals.UpperFace, roof.normalSlope f ∈
    D.reorient '' selectorSlopes positive small (.inr k) ↔ label f.val = .inr k) at selected
  change (∀ f : normals.UpperFace, roof.normalSlope f ∉
    frontier (D.reorient '' selectorSlopes positive small (.inr k))) at generic_local
  rw [triangle] at selected generic_local
  let start : normals.UpperFace := ⟨seed, upper seed seed_label⟩
  have present : roof.normalSlope start ∈ S := (selected start).mpr seed_label
  have original (f : normals.UpperFace) (i : Fin 3) :
      (normals.upperComplex.triangle f).cornerAngle i ≤ π / 2 - a := angles f.val i
  have bp := neg_lt_self D.base_pos
  obtain ⟨bound, east, west⟩ := D.side_ratios
  obtain ⟨σ, reserve, H, R, span_nonneg, span⟩ :=
    roof.exists_revisedLatitudeTriangleRouting start (isPolarStrip a k.1.val)
      positive small (relativeStep_bounds positive small).1 (relativeStep_bounds positive small).2
      φpos φsmall distortion bp D.height_pos bound east west radius generic_local present original
  have selected_components :=
    P.upperRoof_selectionComponent_image_eq_labeled_component N label (.inr k)
      frame selected upper start seed_label
  refine ⟨D, bp, φ, σ, start, Set.nonempty_of_mem present, H, R, present, selected_components,
    φpos, φsmall, radius, ?_, span_nonneg, span⟩
  have angular := (revised_projection_allowance_le_sq φpos.le φsmall).trans distortion
  have area := D.area_budget
  linarith only [angular, area, reserve]

end Unfoldings.SpatialFolding.ConvexBoundary
