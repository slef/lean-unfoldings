module

public import Unfoldings.Roof.CompatibleContourSourceOnlyGaps
public import Unfoldings.Geometry.OrientedBankGapSourceChart
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

end Unfoldings.ConvexRoof
