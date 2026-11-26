module

public import Unfoldings.FewestNets.RevisedLatitudeSelectors
public import Unfoldings.FewestNets.RevisedLatitudePolarNet
public import Unfoldings.FewestNets.UpperRoofComponentTransfer
public import Unfoldings.Cap.HorizontalChartIsometry

/-! A label in the revised spherical mesh selects the exact original component in its upper roof. -/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialFolding.ConvexBoundary

open Real Cap FewestNets RevisedLatitudeGrid
open AcuteLatitudeGrid (polarFrame polarRadius polarRadius_pos polarRadius_lt)

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {F : SpatialFolding C} (P : F.ConvexBoundary) (N : F.SupportingNormals)

variable {a : ℝ} (positive : 0 < a) (small : a ≤ π / 6)
  (placement : Space ≃ₗᵢ[ℝ] Space) (label : Face → Selector a)
  (chosen : ∀ f, placement (N.normal f) ∈ selectorSphere positive small (label f))
  (generic : ∀ f (i : (rings a).ChordFace) j, (LatitudeRings.chordBasis (rings_oriented positive small) i).coord j
    (placement (N.normal f)) ≠ 0)

private theorem selectorSlopes_closed (key : Selector a) :
    IsClosed (selectorSlopes positive small key) := by
  rcases key with _ | k
  · change IsClosed (regularSlopePolygon polarFrame (rowSize a 0) (tan (polarRadius a)))
    have sides := le_trans (show 3 ≤ 6 by decide) (polarSize_bounds positive small).1
    have radius := tan_pos_of_pos_of_lt_pi_div_two (polarRadius_pos positive)
      (show polarRadius a < π / 2 by linarith only [polarRadius_lt small, pi_gt_d2])
    rw [(rowSize_at_poles (a := a)).1]
    exact (regularPolygonSideDirections polarFrame sides radius).isClosed
  · exact ((Set.finite_range _).isCompact_convexHull ℝ).isClosed

include chosen generic in
/-- All faces with this label are actual upper faces, with the matching strict local selector. -/
theorem revisedLatitude_upperRoof_data (key : Selector a) :
    let frame := placement.trans (selectorFrame key)
    let normals := N.rotate frame
    let roof := (P.rotate frame).upperRoof normals
    let region := selectorSlopes positive small key
    (∀ f : normals.UpperFace, roof.normalSlope f ∈ region ↔ label f.val = key) ∧
      (∀ f : normals.UpperFace, roof.normalSlope f ∉ frontier region) ∧
      ∀ f, label f = key → 0 < normals.normal f 2 := by
  classical
  let frame := placement.trans (selectorFrame key)
  let normals := N.rotate frame
  let roof := (P.rotate frame).upperRoof normals
  let region := selectorSlopes positive small key
  have exact_coord (f : normals.UpperFace) :
      gnomonicNormal (roof.normalSlope f) = selectorFrame key (placement (N.normal f.val)) :=
    roof.gnomonicNormal_normalSlope f
  have label_selection (f : normals.UpperFace) : roof.normalSlope f ∈ region ↔ label f.val = key := by
    constructor
    · intro inside
      have belongs : placement (N.normal f.val) ∈ selectorSphere positive small key := by
        change selectorFrame key (placement (N.normal f.val)) ∈ gnomonicNormal '' region
        rw [← exact_coord]
        exact ⟨roof.normalSlope f, inside, rfl⟩
      exact selectorSphere_unique positive small (chosen f.val) belongs (generic f.val)
    · intro selected
      have belongs : placement (N.normal f.val) ∈ selectorSphere positive small key :=
        selected ▸ chosen f.val
      change selectorFrame key (placement (N.normal f.val)) ∈ gnomonicNormal '' region at belongs
      rw [← exact_coord] at belongs
      obtain ⟨x, inside, equal⟩ := belongs
      rwa [gnomonicNormal_injective equal] at inside
  refine ⟨label_selection, ?_, ?_⟩
  · intro f border
    have member := (selectorSlopes_closed positive small key).frontier_subset border
    have avoids (c : (rings a).ChordFace) (j : Fin 3) :
        (LatitudeRings.chordBasis (rings_oriented positive small) c).coord j
          ((selectorFrame key).symm (gnomonicNormal (roof.normalSlope f))) ≠ 0 := by
      rw [exact_coord, (selectorFrame key).symm_apply_apply]
      exact generic f.val c j
    have inside := mem_interior_selectorSlopes_of_avoids_edges positive small key
      (roof.normalSlope f) member avoids
    exact border.2 inside
  · intro f selected
    have inside : placement (N.normal f) ∈ selectorSphere positive small key := selected ▸ chosen f
    obtain ⟨p, _, equal⟩ := inside
    change 0 < selectorFrame key (placement (N.normal f)) 2
    rw [← equal]
    exact gnomonicNormal_upward p

include chosen generic in
/-- Reorient the slope selector and the physical roof together. -/
theorem revisedLatitude_reoriented_upperRoof_data (key : Selector a) (E : Plane ≃ₗᵢ[ℝ] Plane) :
    let frame := (placement.trans (selectorFrame key)).trans (horizontalChartIsometry E)
    let normals := N.rotate frame
    let roof := (P.rotate frame).upperRoof normals
    let region := E '' selectorSlopes positive small key
    (∀ f : normals.UpperFace, roof.normalSlope f ∈ region ↔ label f.val = key) ∧
      (∀ f : normals.UpperFace, roof.normalSlope f ∉ frontier region) ∧
      ∀ f, label f = key → 0 < normals.normal f 2 := by
  let frame := placement.trans (selectorFrame key)
  let moved := frame.trans (horizontalChartIsometry E)
  let normals := N.rotate frame
  let roof := (P.rotate frame).upperRoof normals
  let newNormals := N.rotate moved
  let newRoof := (P.rotate moved).upperRoof newNormals
  let region := selectorSlopes positive small key
  obtain ⟨selected, interior_label, positives⟩ :=
    P.revisedLatitude_upperRoof_data N positive small placement label chosen generic key
  have height (f : Face) : newNormals.normal f 2 = normals.normal f 2 := rfl
  let old (f : newNormals.UpperFace) : normals.UpperFace := ⟨f.val, height f.val ▸ f.property⟩
  have slope (f : newNormals.UpperFace) : newRoof.normalSlope f = E (roof.normalSlope (old f)) := by
    apply gnomonicNormal_injective
    rw [← horizontalChartIsometry_gnomonicNormal]
    exact (newRoof.gnomonicNormal_normalSlope f).trans
      (congrArg (horizontalChartIsometry E) (roof.gnomonicNormal_normalSlope (old f))).symm
  refine ⟨?_, ?_, fun f hf => (height f).symm ▸ positives f hf⟩
  · intro f
    change newRoof.normalSlope f ∈ E '' region ↔ _
    rw [slope, E.injective.mem_set_image]
    exact selected (old f)
  · intro f
    change newRoof.normalSlope f ∉ frontier (E '' region)
    rw [slope]
    change E.toHomeomorph (roof.normalSlope (old f)) ∉ frontier (E.toHomeomorph '' region)
    rw [← E.toHomeomorph.image_frontier, E.toHomeomorph.injective.mem_set_image]
    exact interior_label (old f)

include P N positive small placement chosen generic in
/-- Each component with a polar label has a net of the original input triangles. -/
theorem hasOriginalEdgeNet_of_revisedLatitude_polar_label (pole : Fin 2)
    (angles : ∀ f i, (C.triangle f).cornerAngle i ≤ π / 2 - a)
    (seed : Face) (seed_label : label seed = .inl pole) :
    C.HasOriginalEdgeNet ((C.labeledSeamGraph label).connectedComponentMk seed).supp := by
  classical
  let frame := placement.trans (selectorFrame (a := a) (.inl pole))
  let normals := N.rotate frame
  let roof := (P.rotate frame).upperRoof normals
  let region := regularSlopePolygon polarFrame (polarSize a) (tan (polarRadius a))
  obtain ⟨selected, no_boundary, upper⟩ :=
    P.revisedLatitude_upperRoof_data N positive small placement label chosen generic (.inl pole)
  let start : normals.UpperFace := ⟨seed, upper seed seed_label⟩
  have original (f : normals.UpperFace) (i : Fin 3) :
      (normals.upperComplex.triangle f).cornerAngle i ≤ π / 2 - a := angles f.val i
  have inside : roof.normalSlope start ∈ region := by
    change roof.normalSlope start ∈ regularSlopePolygon polarFrame (polarSize a) (tan (polarRadius a))
    rw [show polarSize a = rowSize a 0 from (rowSize_at_poles (a := a)).1.symm]
    exact (selected start).mpr seed_label
  have net := roof.hasOriginalEdgeNet_of_revisedLatitudePolarSelector
    polarFrame positive small (by
      intro f regular
      apply no_boundary f
      change roof.normalSlope f ∈ frontier
        (regularSlopePolygon polarFrame (rowSize a 0) (tan (polarRadius a)))
      simpa only [(rowSize_at_poles (a := a)).1] using regular) original start inside
  have same := P.upperRoof_selectionComponent_image_eq_labeled_component N label (.inl pole)
    frame selected upper start seed_label
  exact same ▸ C.hasOriginalEdgeNet_of_restrictFaces _ _ net

end Unfoldings.SpatialFolding.ConvexBoundary
