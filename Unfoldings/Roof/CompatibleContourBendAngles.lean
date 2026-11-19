module

public import Unfoldings.Complex.BoundaryChainLeftAperture
public import Unfoldings.Roof.CompatibleContourGapBends

/-! The canonical bend apertures use the actual saved-frontier fan and processed curvature. -/

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
local notation "conforming" => K.compatibleCutMesh_conforming compact nonempty R no_boundary
  level higher M positive inner_disk
local notation "inside" => K.compatible_section_interior compact nonempty R level higher M
local notation "Fcut" => K.compatibleMeshForest compact nonempty R no_boundary level higher
  M positive inner_disk beta acute

local instance compatibleContourBendAngleIndexFintype : Fintype (T).Index :=
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
local notation "OpenedAt[" q "," h "," e "]" =>
  K.compatibleContourOpenedBank compact nonempty R no_boundary level higher M positive inner_disk
    beta acute q h e
local notation "OpeningsAt[" q "," e "]" => PolygonalChain.castOpenings SpanAt[q,e]
  (TriangleComplex.contourRootwardOpenings D Selection q (Fin.succ (Subtype.val e)) VertexAt[q,e])

local notation "P" => PotentialCutForest.parents Fcut
local notation "FrontierAt[" q "," i "]" => TriangleComplex.contourFrontier D Selection q i
local notation "RetainAt[" q "," i "]" => TriangleComplex.processedParentRetain D Selection
  FrontierAt[q,i]
/-- The first occupied bend aperture is the actual saved-frontier fan angle. The original
uncut total-angle bound applies because each bend comes strictly before the root. -/
theorem compatibleContourSourceBank_first_bend_aperture
    (contour : (T).pairedComplex.BoundaryContour
      ((T).pairedComplex.selectedRetain (Fcut).selection))
    (starts : SourceAt[contour,0] ∈ (Fcut).parents.roots)
    (event : Event[contour]) (k : Fin (LengthAt[contour,event]))
    (outward : (BankAt[contour,starts,event]).Outward)
    (outgoing_radial : let bank := BankAt[contour,starts,event]
      0 < inner ℝ (bank.chain.vertex k.succ.castSucc - bank.start) (bank.chain.edge k.succ)) :
    let bank := BankAt[contour,starts,event]
    let retain := RetainAt[contour,event.val.succ]
    let chain := ChainAt[contour,starts,event.val,event.property.1,LengthAt[contour,event],
      SpanAt[contour,event]]
    radialLeftCornerWidth (bank.chain.vertex k.succ.castSucc - bank.start)
      (bank.chain.edge k.castSucc) (bank.chain.edge k.succ) =
        (D).totalAngle retain ((D).boundaryEndVertex retain (chain.point k.succ)) := by
  let m := LengthAt[contour,event]
  let chain := ChainAt[contour,starts,event.val,event.property.1,m,SpanAt[contour,event]]
  let bank := BankAt[contour,starts,event]
  let retain := RetainAt[contour,event.val.succ]
  let w := (D).boundaryEndVertex retain (chain.point k.succ)
  let v := VertexAt[contour,event]
  have incoming : 0 < inner ℝ (bank.chain.vertex k.succ.castSucc - bank.start)
      (bank.chain.edge k.castSucc) := by
    have genuine : bank.chain.vertex k.castSucc.castSucc ≠ bank.chain.vertex k.castSucc.succ :=
      Ne.symm (sub_ne_zero.mp ((D).boundaryChainRoll_edge_ne_zero chain k.castSucc))
    simpa only [PolygonalChain.edge, Fin.succ_castSucc] using
      bank.inner_terminal_edge_pos outward k.castSucc genuine
  have original : (D).vertexForgetCuts (Set.subset_univ retain) w =
      (P).parent^[k.succ.val] v :=
    K.compatibleMeshFreshSourceBankChain_original compact nonempty R no_boundary level higher M
      positive inner_disk beta acute contour starts event.val event.property.1 m
      SpanAt[contour,event] k.succ
  have before : k.succ.val < (P).distanceToRoot v := by
    rw [SpanAt[contour,event]]
    exact k.succ.isLt
  have internal : ¬ (D).IsBoundaryVertex Set.univ
      ((D).vertexForgetCuts (Set.subset_univ retain) w) := by
    intro boundary
    exact (P).iterate_lt_distanceToRoot_not_mem v before
      (original ▸ (Fcut).boundary_roots boundary)
  let cap := (T).toTriangulation.normalizedCap conforming inside
  have small : (D).totalAngle retain w ≤ 2 * Real.pi :=
    le_trans ((D).totalAngle_le_forgetCuts (Set.subset_univ retain) w)
      (cap.totalAngle_le_two_pi _ internal)
  exact (D).boundaryChainRoll_left_aperture chain k _ incoming outgoing_radial small

/-- The original cumulative model uses the same first bank and its exact retained aperture. -/
theorem compatibleContourGap_first_bend_aperture
    (contour : (T).pairedComplex.BoundaryContour
      ((T).pairedComplex.selectedRetain (Fcut).selection))
    (starts : SourceAt[contour,0] ∈ (Fcut).parents.roots)
    (event : Event[contour]) (k : Fin (LengthAt[contour,event]))
    (gap : OrientedBankGap BankAt[contour,starts,event] OpenedAt[contour,starts,event])
    (outgoing_radial : let bank := BankAt[contour,starts,event]
      0 < inner ℝ (bank.chain.vertex k.succ.castSucc - bank.start) (bank.chain.edge k.succ)) :
    let bank := BankAt[contour,starts,event]
    let retain := RetainAt[contour,event.val.succ]
    let chain := ChainAt[contour,starts,event.val,event.property.1,LengthAt[contour,event],
      SpanAt[contour,event]]
    radialLeftCornerWidth (bank.chain.vertex k.succ.castSucc - bank.start)
      (bank.chain.edge k.castSucc) (bank.chain.edge k.succ) =
        (D).totalAngle retain ((D).boundaryEndVertex retain (chain.point k.succ)) :=
  K.compatibleContourSourceBank_first_bend_aperture compact nonempty R no_boundary level higher M
    positive inner_disk beta acute contour starts event k gap.first_outward outgoing_radial

local notation "WeightAt[" F "," v "]" =>
  AscendingParents.ParentFrontier.processedDescendantWeight F
    (TriangleComplex.interiorAngularDefect D Set.univ) v

/-- Each real bank heading is the original processed curvature of the subtree above
that edge, with the vertex taken directly from the named parent orbit. -/
theorem compatibleContourOpenedBank_heading_eq_processedWeight
    (contour : (T).pairedComplex.BoundaryContour
      ((T).pairedComplex.selectedRetain (Fcut).selection))
    (event : Event[contour]) (i : Fin (LengthAt[contour,event] + 1)) :
    PolygonalChain.openingHeading OpeningsAt[contour,event] i =
      WeightAt[FrontierAt[contour,event.val.succ],(P).parent^[i.val] VertexAt[contour,event]] := by
  let v := VertexAt[contour,event]
  let F := FrontierAt[contour,event.val.succ]
  let w := (D).interiorAngularDefect Set.univ
  let n := (P).distanceToRoot v
  let span := SpanAt[contour,event]
  let events := (D).contourRootwardOpenings Selection contour event.val.succ v
  have same {m : ℕ} (eq : n = m) (i : Fin m) :
      PolygonalChain.openingHeading (PolygonalChain.castOpenings eq events) i =
        PolygonalChain.openingHeading events (Fin.cast eq.symm i) := by
    subst m
    rw [show PolygonalChain.castOpenings rfl events = events from List.map_id' events]
    rfl
  change PolygonalChain.openingHeading (PolygonalChain.castOpenings span events) i =
    F.processedDescendantWeight w ((P).parent^[i.val] v)
  rw [same]
  let seeds := ((D).selectedContourSeeds Selection contour).take event.val.succ.val
  change PolygonalChain.openingHeading
    ((P).historyOpenings seeds ⟨(P).root v, (P).root_mem v⟩ ((P).rootwardVertexPath v)
      ((P).rootwardVertexPath_last v) w) (Fin.cast span.symm i) = _
  rw [(P).historyOpenings_heading _ _ _ _ _ ((P).rootwardVertexPath_ancestor v)]
  rfl

/-- The second occupied bend aperture is the saved-frontier fan's full-turn
complement plus the difference of the two original processed subtree charges. -/
theorem compatibleContourGap_second_bend_aperture
    (contour : (T).pairedComplex.BoundaryContour
      ((T).pairedComplex.selectedRetain (Fcut).selection))
    (starts : SourceAt[contour,0] ∈ (Fcut).parents.roots)
    (event : Event[contour]) (k : Fin (LengthAt[contour,event]))
    (gap : OrientedBankGap BankAt[contour,starts,event] OpenedAt[contour,starts,event])
    (outgoing_radial : let first := BankAt[contour,starts,event]
      0 < inner ℝ (first.chain.vertex k.succ.castSucc - first.start)
        (first.chain.edge k.succ))
    (apertures : let first := BankAt[contour,starts,event]
      let second := OpenedAt[contour,starts,event]
      radialLeftCornerWidth (first.chain.vertex k.succ.castSucc - first.start)
        (first.chain.edge k.castSucc) (first.chain.edge k.succ) +
          radialRightCornerWidth (second.chain.vertex k.succ.castSucc - second.start)
            (second.chain.edge k.castSucc) (second.chain.edge k.succ) =
        2 * Real.pi + (PolygonalChain.openingHeading OpeningsAt[contour,event] k.succ -
          PolygonalChain.openingHeading OpeningsAt[contour,event] k.castSucc)) :
    let second := OpenedAt[contour,starts,event]
    let retain := RetainAt[contour,event.val.succ]
    let chain := ChainAt[contour,starts,event.val,event.property.1,LengthAt[contour,event],
      SpanAt[contour,event]]
    let F := FrontierAt[contour,event.val.succ]
    let v := VertexAt[contour,event]
    radialRightCornerWidth (second.chain.vertex k.succ.castSucc - second.start)
      (second.chain.edge k.castSucc) (second.chain.edge k.succ) =
        2 * Real.pi - (D).totalAngle retain ((D).boundaryEndVertex retain (chain.point k.succ)) +
          (WeightAt[F,(P).parent^[k.succ.val] v] - WeightAt[F,(P).parent^[k.castSucc.val] v]) := by
  have first := K.compatibleContourGap_first_bend_aperture compact nonempty R no_boundary level
    higher M positive inner_disk beta acute contour starts event k gap outgoing_radial
  have heading := K.compatibleContourOpenedBank_heading_eq_processedWeight compact nonempty R
    no_boundary level higher M positive inner_disk beta acute contour event
  dsimp only at first apertures ⊢
  rw [first, heading, heading] at apertures
  linarith [apertures]

end Unfoldings.ConvexRoof
