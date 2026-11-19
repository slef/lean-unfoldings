module

public import Unfoldings.Geometry.OpeningCornerTurns
public import Unfoldings.Roof.CompatibleContourGapModels
public import Unfoldings.Roof.CompatibleFreshSourceGapGeometry

/-! At every finite bend the canonical gap has a controlled pair of occupied apertures. -/

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
local notation "Q" => SpatialEnvelope.Triangulation.roof
  (SpatialEnvelope.ConstrainedTriangulation.toTriangulation T) conforming inside
local notation "Fcut" => K.compatibleMeshForest compact nonempty R no_boundary level higher
  M positive inner_disk beta acute

local instance compatibleContourGapBendIndexFintype : Fintype (T).Index :=
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

/-- One tilt gives the actual canonical gap geometry together with the exact real
aperture change at every interior bend. Both chart radii point strictly along the
outgoing bank edges. -/
theorem exists_uniform_contourGap_corner_geometry {b : ℝ} (bpos : 0 < b) (ratio : a ≤ b)
    (upper : ∀ p ∈ slopes, ‖p‖ ≤ b)
    (small : 2 * annularHistoryAngle (a / b) β < Real.pi / 2) :
    ∃ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), ∀ ψ ∈ Set.Ioc (0 : ℝ) θ,
      (∀ i, Real.cos ψ ≤ (M.plane i).normal 2) →
      ∀ (contour : (T).pairedComplex.BoundaryContour
          ((T).pairedComplex.selectedRetain (Fcut).selection))
        (starts : SourceAt[contour,0] ∈ (Fcut).parents.roots)
        (event : Event[contour]),
        let first := BankAt[contour,starts,event]
        let second := OpenedAt[contour,starts,event]
        let events := OpeningsAt[contour,event]
        OrientedBankGap first second ∧ ∀ k : Fin (LengthAt[contour,event]),
          let r := first.chain.vertex k.succ.castSucc - first.start
          let q := second.chain.vertex k.succ.castSucc - second.start
          0 < inner ℝ r (first.chain.edge k.succ) ∧
          0 < inner ℝ q (second.chain.edge k.succ) ∧
          radialLeftCornerWidth r (first.chain.edge k.castSucc) (first.chain.edge k.succ) +
            radialRightCornerWidth q (second.chain.edge k.castSucc) (second.chain.edge k.succ) =
            2 * Real.pi + (PolygonalChain.openingHeading events k.succ -
              PolygonalChain.openingHeading events k.castSucc) := by
  obtain ⟨θ, bounds, gaps⟩ := K.exists_uniform_freshSource_gap_geometry_with_controls compact
    nonempty R no_boundary level higher M positive inner_disk beta acute bpos ratio upper small
  refine ⟨θ, bounds, ?_⟩
  intro ψ psi_bounds normal contour starts event
  let m := LengthAt[contour,event]
  let chain := ChainAt[contour,starts,event.val,event.property.1,m,SpanAt[contour,event]]
  let path := (T).pairedComplex.boundaryChainRoll chain
  obtain ⟨gap, γ, gamma_positive, gamma_small, budget, margin⟩ :=
    gaps ψ psi_bounds normal contour starts event.val event.property.1 m SpanAt[contour,event]
      event.property.2
  refine ⟨gap, ?_⟩
  intro k
  have genuine (i : Fin (m + 1)) : path.vertex i.castSucc ≠ path.vertex i.succ := by
    intro equal
    apply (T).pairedComplex.boundaryChainRoll_edge_ne_zero chain i
    change path.edge i = 0
    rw [PolygonalChain.edge, equal, sub_self]
  exact path.terminalEdge_openings_corner_geometry OpeningsAt[contour,event] genuine
    gap.first_outward gamma_positive gamma_small budget margin k

end Unfoldings.ConvexRoof
