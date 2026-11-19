module

public import Unfoldings.Geometry.SourceOpeningBankGap
public import Unfoldings.Roof.CompatibleContourBendAngles
public import Unfoldings.Roof.CompatibleContourGapSourceSector

/-! The new saved-frontier gap spends only the defect at the fresh source. -/

@[expose] public section

noncomputable section

open scoped NNReal

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

local instance sourceOnlyContourGapIndexFintype : Fintype (T).Index :=
  @Fintype.ofFinite _ (T).finite

include beta acute

local notation "SourceAt[" q "," i "]" => TriangleComplex.contourOriginalVertex
  (SpatialEnvelope.Triangulation.pairedComplex
    (SpatialEnvelope.ConstrainedTriangulation.toTriangulation T))
  (PotentialCutForest.selection Fcut) q i
local notation "ChainAt[" q "," h "," i "," hf "," n "," hn "]" =>
  K.compatibleMeshFreshSourceBankChain compact nonempty R no_boundary level higher M positive
    inner_disk beta acute q h i hf n hn

local notation "D" => SpatialEnvelope.Triangulation.pairedComplex
  (SpatialEnvelope.ConstrainedTriangulation.toTriangulation T)
local notation "Selection" => PotentialCutForest.selection Fcut
local notation "LengthAt[" q "," e "]" => TriangleComplex.positiveContourBankLength D Selection q e
local notation "SpanAt[" q "," e "]" => TriangleComplex.positiveContourBank_span D Selection q e
local notation "VertexAt[" q "," e "]" => TriangleComplex.positiveContourVertex D Selection q e

local notation "Event[" q "]" => TriangleComplex.PositiveContourSource D Selection q
local notation "BankAt[" q "," h "," e "]" =>
  K.compatibleContourSourceBank compact nonempty R no_boundary level higher M positive inner_disk
    beta acute q h e
local notation "FrontierAt[" q "," i "]" => TriangleComplex.contourFrontier D Selection q i
local notation "RetainAt[" q "," i "]" => TriangleComplex.processedParentRetain D Selection
  FrontierAt[q,i]
local notation "Defect[" q "," e "]" => TriangleComplex.interiorAngularDefect D Set.univ
  VertexAt[q,e]

/-- The saved-frontier cut exposes only one newly processed vertex at a positive source. -/
theorem compatibleContourFreshSource_processed
    (contour : (T).pairedComplex.BoundaryContour
      ((T).pairedComplex.selectedRetain (Fcut).selection))
    (starts : SourceAt[contour,0] ∈ (Fcut).parents.roots) (event : Event[contour]) :
    (FrontierAt[contour,event.val.succ]).processed =
      insert VertexAt[contour,event] (FrontierAt[contour,event.val.castSucc]).processed := by
  let F := FrontierAt[contour,event.val.castSucc]
  let v := VertexAt[contour,event]
  have time : F.contactTime v ≤ 1 :=
    (D).rim_contour_contactTime_le_one_of_boundary_roots Selection (Fcut).boundary_roots
      contour starts event.val.castSucc
  have nonzero : F.contactTime v ≠ 0 :=
    fun h => event.property.1 ((F.contactTime_eq_zero_iff v).mp h)
  rw [(D).contourFrontier_succ]
  exact F.process_processed_eq_insert (show F.contactTime v = 1 by omega)

/-- In the saved-frontier insertion the old stem is already processed. Its second bank
is obtained from the rolled reference bank by opening only at the fresh source. -/
def compatibleContourSourceOnlyBank
    (contour : (T).pairedComplex.BoundaryContour
      ((T).pairedComplex.selectedRetain (Fcut).selection))
    (starts : SourceAt[contour,0] ∈ (Fcut).parents.roots) (event : Event[contour]) :
    PolygonalRay ℂ (LengthAt[contour,event] + 1) :=
  (BankAt[contour,starts,event]).rotateSuffix 0 Defect[contour,event]

local notation "MovedAt[" q "," h "," e "]" =>
  K.compatibleContourSourceOnlyBank compact nonempty R no_boundary level higher M positive
    inner_disk beta acute q h e

/-- A single positive tilt constructs every source-only gap with strict radial edge
bearings at its finite bends. Its two occupied angles sum to a full turn. -/
theorem exists_uniform_contourSourceOnlyGap_geometry {b : ℝ} (bpos : 0 < b) (ratio : a ≤ b)
    (upper : ∀ p ∈ slopes, ‖p‖ ≤ b)
    (small : 2 * annularHistoryAngle (a / b) β < Real.pi / 2) :
    ∃ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), ∀ ψ ∈ Set.Ioc (0 : ℝ) θ,
      (∀ i, Real.cos ψ ≤ (M.plane i).normal 2) →
      ∀ (contour : (T).pairedComplex.BoundaryContour
          ((T).pairedComplex.selectedRetain (Fcut).selection))
        (starts : SourceAt[contour,0] ∈ (Fcut).parents.roots) (event : Event[contour]),
        let first := BankAt[contour,starts,event]
        let second := MovedAt[contour,starts,event]
        OrientedBankGap first second ∧ ∀ k : Fin (LengthAt[contour,event]),
          let r := first.chain.vertex k.succ.castSucc - first.start
          let q := second.chain.vertex k.succ.castSucc - second.start
          let retain := RetainAt[contour,event.val.succ]
          let chain := ChainAt[contour,starts,event.val,event.property.1,LengthAt[contour,event],
            SpanAt[contour,event]]
          let angle := (D).totalAngle retain ((D).boundaryEndVertex retain (chain.point k.succ))
          0 < inner ℝ r (first.chain.edge k.succ) ∧
          0 < inner ℝ q (second.chain.edge k.succ) ∧
          radialLeftCornerWidth r (first.chain.edge k.castSucc) (first.chain.edge k.succ) = angle ∧
          radialRightCornerWidth q (second.chain.edge k.castSucc) (second.chain.edge k.succ) =
            2 * Real.pi - angle := by
  obtain ⟨θ, bounds, geometry⟩ := K.exists_uniform_contourGap_corner_geometry compact nonempty R
    no_boundary level higher M positive inner_disk beta acute bpos ratio upper small
  refine ⟨θ, bounds, ?_⟩
  intro ψ psi_bounds normal contour starts event
  obtain ⟨old, corners⟩ := geometry ψ psi_bounds normal contour starts event
  let first := BankAt[contour,starts,event]
  let κ := Defect[contour,event]
  have defect_bound := (K.compatibleContourGap_source_angle_and_lt_pi compact nonempty R
    no_boundary level higher M positive inner_disk beta acute contour starts event old).2
  refine ⟨first.orientedGap_rotateSuffix_zero old.first_outward old.first_nonzero
    event.property.2 defect_bound, ?_⟩
  intro k
  have rpos := (corners k).1
  have qpos : 0 < inner ℝ ((first.rotateSuffix 0 κ).chain.vertex k.succ.castSucc -
      (first.rotateSuffix 0 κ).start) ((first.rotateSuffix 0 κ).chain.edge k.succ) := by
    rw [first.rotateSuffix_zero_vertex_sub_start, first.rotateSuffix_zero_edge,
      LinearIsometry.inner_map_map]
    exact rpos
  have width := K.compatibleContourGap_first_bend_aperture compact nonempty R no_boundary
    level higher M positive inner_disk beta acute contour starts event k old rpos
  refine ⟨rpos, qpos, width, ?_⟩
  have sum := PolygonalRay.sourceOpening_corner_widths_add (B := first) κ k
  dsimp only [compatibleContourSourceOnlyBank] at sum width ⊢
  rw [width] at sum
  linarith only [sum]

end Unfoldings.ConvexRoof
