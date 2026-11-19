module

public import Unfoldings.Roof.CompatibleContourSourceOnlyGaps
public import Unfoldings.Geometry.OrientedBankGapSourceChart
public import Unfoldings.Cone.ComplementarySectorRadial
public import Unfoldings.Metric.CenteredBallChartRestriction
public import Unfoldings.Roof.CompatibleContourBankAgreement

/-! The revised gap has its original source defect as a physical metric sector. -/

@[expose] public section

noncomputable section

open scoped NNReal ENNReal

namespace Unfoldings.ConvexRoof

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexRoof C)
  {slopes : Set Plane} (compact : IsCompact slopes) (nonempty : slopes.Nonempty)
  {boundary : (frontier slopes).Nonempty} {a β : ℝ}
  (R : K.CompatiblePotentialRouting {f | K.normalSlope f ∈ slopes}
    (K.clippedExtension slopes compact nonempty) boundary a β)
  (no_boundary : ∀ f, K.normalSlope f ∉ frontier slopes)
  (level : ℝ)
  (higher : ∀ v, (K.clippedExtension slopes compact nonempty).height (K.projectedVertex v) < level)
  (M : (K.clippedExtension slopes compact nonempty).FiniteSlopeModel)
  (positive : 0 < a) (inner_disk : Metric.ball (0 : Plane) a ⊆ slopes)
  (beta : 0 ≤ β) (acute : β < Real.pi / 2)

local notation "T" => K.compatibleCutMesh compact nonempty R no_boundary level higher M
  positive inner_disk
local notation "Fcut" => K.compatibleMeshForest compact nonempty R no_boundary level higher
  M positive inner_disk beta acute

local instance sourceOnlySourceChartIndexFintype : Fintype (T).Index :=
  @Fintype.ofFinite _ (T).finite

include beta acute

local notation "SourceAt[" q "," i "]" => TriangleComplex.contourOriginalVertex
  (SpatialEnvelope.Triangulation.pairedComplex
    (SpatialEnvelope.ConstrainedTriangulation.toTriangulation T))
  (PotentialCutForest.selection Fcut) q i
local notation "D" => SpatialEnvelope.Triangulation.pairedComplex
  (SpatialEnvelope.ConstrainedTriangulation.toTriangulation T)
local notation "Selection" => PotentialCutForest.selection Fcut
local notation "VertexAt[" q "," e "]" => TriangleComplex.positiveContourVertex D Selection q e

local notation "Event[" q "]" => TriangleComplex.PositiveContourSource D Selection q
local notation "BankAt[" q "," h "," e "]" =>
  K.compatibleContourSourceBank compact nonempty R no_boundary level higher M positive inner_disk
    beta acute q h e
local notation "Defect[" q "," e "]" => TriangleComplex.interiorAngularDefect D Set.univ
  VertexAt[q,e]

local notation "MovedAt[" q "," h "," e "]" =>
  K.compatibleContourSourceOnlyBank compact nonempty R no_boundary level higher M positive
    inner_disk beta acute q h e

/-- At the actual source-only tip, the whole intrinsic ball has precisely its original
defect aperture and its original first bank as the normalized axis. -/
theorem compatibleContourSourceOnlyGap_source_sector_chart
    (contour : (T).pairedComplex.BoundaryContour
      ((T).pairedComplex.selectedRetain (Fcut).selection))
    (starts : SourceAt[contour,0] ∈ (Fcut).parents.roots)
    (event : Event[contour])
    (G : OrientedBankGap BankAt[contour,starts,event] MovedAt[contour,starts,event]) :
    let first := BankAt[contour,starts,event]
    let d := first.chain.edge 0
    let e := (MovedAt[contour,starts,event]).chain.edge 0
    let r := min ‖d‖ ‖e‖
    0 < r ∧ initialGapAngle d e = Defect[contour,event] ∧ Defect[contour,event] < Real.pi ∧
      ∃ A : Metric.eball (G.model.edgePoint false 0 0) (ENNReal.ofReal r) ≃ᵢ
        Metric.ball (initialGapSectorOrigin d e) r,
        ∀ y, first.start + (d / (‖d‖ : ℂ)) * (A y).val.val = y.val.val := by
  let first := BankAt[contour,starts,event]
  let second := MovedAt[contour,starts,event]
  let d := first.chain.edge 0
  let e := second.chain.edge 0
  let v := VertexAt[contour,event]
  let κ := Defect[contour,event]
  have d_ne : d ≠ 0 := by
    apply norm_ne_zero_iff.mp
    have length := K.compatibleContourSourceBank_edge_length compact nonempty R no_boundary level
      higher M positive inner_disk beta acute contour starts event 0
    exact length.trans_ne ((D).boundaryBankLength_pos _).ne'
  have rotated : e = complexRotation κ d := first.rotateSuffix_zero_edge κ 0
  have e_ne : e ≠ 0 := rotated.symm ▸ by
    simpa only [map_zero] using (complexRotation κ).injective.ne d_ne
  obtain ⟨positive, bounds, chart⟩ := G.exists_model_source_chart d_ne e_ne
  have internal : ¬ (D).IsBoundaryVertex Set.univ v := fun boundary =>
    (D).positiveContourVertex_nonroot Selection contour event ((Fcut).boundary_roots boundary)
  have kappa_small : κ < 2 * Real.pi := by
    change (D).interiorAngularDefect Set.univ v < _
    rw [TriangleComplex.interiorAngularDefect, ite_eq_right internal]
    exact sub_lt_self _ ((D).totalAngle_pos Set.univ v)
  change initialGapAngle d e ∈ Set.Ioo (0 : ℝ) Real.pi at bounds
  have exact_angle := initialGapAngle_rotated_of_bounds d d_ne event.property.2 kappa_small
    (rotated ▸ bounds)
  exact ⟨positive, (congrArg (initialGapAngle d) rotated).trans exact_angle.1,
    exact_angle.2, chart⟩

/-- The two original gap banks give exact arclengths in the intrinsic angular sector,
using the original source defect for its width. -/
theorem compatibleContourSourceOnlyGap_source_angular_chart
    (contour : (T).pairedComplex.BoundaryContour
      ((T).pairedComplex.selectedRetain (Fcut).selection))
    (starts : SourceAt[contour,0] ∈ (Fcut).parents.roots)
    (event : Event[contour])
    (G : OrientedBankGap BankAt[contour,starts,event] MovedAt[contour,starts,event]) :
    let d := (BankAt[contour,starts,event]).chain.edge 0
    let κ := Defect[contour,event]
    let x := G.model.edgePoint false 0 0
    0 < ‖d‖ ∧ ∃ chart : Metric.eball x (ENNReal.ofReal ‖d‖) ≃ᵢ
      Metric.eball (closedAngularSectorOrigin (le_of_lt event.property.2)) (ENNReal.ofReal ‖d‖),
      ∀ (side : Bool) (t : unitInterval)
        (near : edist (G.model.edgePoint side 0 t) x < ENNReal.ofReal ‖d‖),
        (chart ⟨G.model.edgePoint side 0 t, near⟩).val.val =
          if side then (t.val * ‖d‖) • polarRay κ else (t.val * ‖d‖ : ℝ) := by
  let first := BankAt[contour,starts,event]
  let second := MovedAt[contour,starts,event]
  let d := first.chain.edge 0
  let e := second.chain.edge 0
  let κ := Defect[contour,event]
  have same_start : second.start = first.start := first.rotateSuffix_start 0 κ
  have rotated : e = complexRotation κ d := first.rotateSuffix_zero_edge κ 0
  have length : ‖e‖ = ‖d‖ := (congrArg norm rotated).trans ((complexRotation κ).norm_map d)
  have radius : min ‖d‖ ‖e‖ = ‖d‖ := min_eq_left length.ge
  have result := K.compatibleContourSourceOnlyGap_source_sector_chart compact nonempty R
    no_boundary level higher M positive inner_disk beta acute contour starts event G
  change 0 < min ‖d‖ ‖e‖ ∧ initialGapAngle d e = κ ∧ κ < Real.pi ∧ _ at result
  rw [radius] at result
  obtain ⟨rpos, angle, small, chart, physical⟩ := result
  have d_ne : d ≠ 0 := norm_pos_iff.mp rpos
  have e_ne : e ≠ 0 := norm_pos_iff.mp (length.trans_gt rpos)
  let X := planarSector (initialGapAngle d e)
  have convex : Convex ℝ X := convex_planarSector _
  let E : X ≃ᵢ PolygonalPoint X :=
    ⟨⟨PolygonalPoint.includeConvex X (Set.Subset.refl X),
      fun z => ⟨z.val, z.property⟩, fun _ => rfl, fun _ => rfl⟩,
      PolygonalPoint.includeConvex_isometry X convex (Set.Subset.refl X)⟩
  let B := E.trans (PolygonalPoint.congrIsometryEquiv
    (show X = closedAngularSector κ by
      change planarSector (initialGapAngle d e) = _
      rw [angle]
      exact planarSector_eq_closedAngularSector event.property.2 small))
  have center : B (initialGapSectorOrigin d e) =
      closedAngularSectorOrigin (le_of_lt event.property.2) := by
    apply PolygonalPoint.ext
    rw [IsometryEquiv.trans_apply, PolygonalPoint.congrIsometryEquiv_val]
    rfl
  let balls := basedEBallIsometry B (initialGapSectorOrigin d e) _ center (ENNReal.ofReal ‖d‖)
  let charts := chart.trans ((metricBallEBallEquiv (initialGapSectorOrigin d e) ‖d‖).trans balls)
  refine ⟨rpos, charts, ?_⟩
  intro side t near
  have image := G.source_chart_bank_coordinates same_start d_ne e_ne chart physical side t near
  change (chart ⟨G.model.edgePoint side 0 t, near⟩).val.val = _ at image
  change (B (chart ⟨G.model.edgePoint side 0 t, near⟩).val).val = _
  rw [IsometryEquiv.trans_apply, PolygonalPoint.congrIsometryEquiv_val]
  change (chart ⟨G.model.edgePoint side 0 t, near⟩).val.val = _
  rw [image, angle, length]

end Unfoldings.ConvexRoof
