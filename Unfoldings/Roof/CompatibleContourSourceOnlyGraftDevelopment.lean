module

public import Unfoldings.Roof.CompatibleContourSourceOnlyGraftCollapse
public import Unfoldings.Roof.CompatibleContourSourceOnlyGraftFlatness
public import Unfoldings.Roof.CompatibleContourSourceOnlyTailAddressCoverage
public import Unfoldings.Roof.CompatibleContourSourceOnlyTerminalFiber
public import Unfoldings.Roof.CompatibleContourSourceOnlyVertexFiber
public import Unfoldings.Metric.FlatPlanarCollapse

/-! Global planar development of the actual saved-frontier source-only graft. -/

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

local instance sourceOnlyGraftDevelopmentIndexFintype : Fintype (T).Index :=
  @Fintype.ofFinite _ (T).finite

include beta acute

local notation "D" => SpatialEnvelope.Triangulation.pairedComplex
  (SpatialEnvelope.ConstrainedTriangulation.toTriangulation T)
local notation "Selection" => PotentialCutForest.selection Fcut
variable (contour :
    (K.compatibleCutMesh compact nonempty R no_boundary level higher M positive
      inner_disk).pairedComplex.BoundaryContour
    ((K.compatibleCutMesh compact nonempty R no_boundary level higher M positive
      inner_disk).pairedComplex.selectedRetain
      (K.compatibleMeshForest compact nonempty R no_boundary level higher M positive
        inner_disk beta acute).selection))
  (starts : (K.compatibleCutMesh compact nonempty R no_boundary level higher M positive
      inner_disk).pairedComplex.contourOriginalVertex
      (K.compatibleMeshForest compact nonempty R no_boundary level higher M positive
        inner_disk beta acute).selection contour 0 ∈
      (K.compatibleMeshForest compact nonempty R no_boundary level higher M positive
        inner_disk beta acute).parents.roots)
  (W : R.WholeCutModel M)
  (geometry : ∀ event : (K.compatibleCutMesh compact nonempty R no_boundary level higher M
      positive inner_disk).pairedComplex.PositiveContourSource
      (K.compatibleMeshForest compact nonempty R no_boundary level higher M positive
        inner_disk beta acute).selection contour,
    OrientedBankGap
      (K.compatibleContourSourceBank compact nonempty R no_boundary level higher M positive
        inner_disk beta acute contour starts event)
      (K.compatibleContourSourceOnlyBank compact nonempty R no_boundary level higher M positive
        inner_disk beta acute contour starts event))

local instance sourceOnlyGraftDevelopmentWholeFintype : Fintype W.Index := W.finiteIndex

local notation "Event" => TriangleComplex.PositiveContourSource D Selection contour
local notation "models" => (fun event : Event => OrientedBankGap.model (geometry event))
local notation "Stack" => K.compatibleContourBankStack compact nonempty R no_boundary level higher
  M positive inner_disk beta acute contour
local notation "Pieces" => polygonalBankStackPiece W.Cut
  (fun event : Event => BankGapModel.region (models event))
local notation "Base" => K.compatibleContourSourceOnlyBaseMark compact nonempty R no_boundary
  level higher M positive inner_disk beta acute contour starts W
local notation "Gap" => K.compatibleContourSourceOnlyGapMark compact nonempty R no_boundary level
  higher M positive inner_disk beta acute contour starts models

local notation "Attachment" => K.compatibleContourBankAttachment compact nonempty R no_boundary
  level higher M positive inner_disk beta acute
local notation "ParamAt" => K.compatibleContourBankParameter compact nonempty R no_boundary
  level higher M positive inner_disk beta acute
local notation "LengthAt[" e "]" => TriangleComplex.positiveContourBankLength D Selection contour e
local notation "BankAt[" e "]" => K.compatibleContourSourceBank compact nonempty R no_boundary
  level higher M positive inner_disk beta acute contour starts e
local notation "SpatialAt[" e "]" => K.compatibleContourPhysicalBank compact nonempty R no_boundary
  level higher M positive inner_disk beta acute contour starts e
local notation "Index" => K.compatibleContourSourceOnlyCellIndex compact nonempty R no_boundary
  level higher M positive inner_disk beta acute contour starts W models
local notation "Cells" => K.compatibleContourSourceOnlyCells compact nonempty R no_boundary level
  higher M positive inner_disk beta acute contour starts W models
local notation "Raw" => MetricGluing.NestedCell (fun i j => Cells i j)
local notation "Seams" => K.compatibleContourSourceOnlyClosedSeams compact nonempty R no_boundary
  level higher M positive inner_disk beta acute contour starts W models

local notation "Graft" => K.compatibleContourSourceOnlyGraft compact nonempty R no_boundary
  level higher M positive inner_disk beta acute contour starts W models
local notation "FoldAt[" e "]" => K.compatibleContourSourceOnlyFrontierMap compact nonempty R
  no_boundary level higher M positive inner_disk beta acute contour starts models e
local notation "L" => MetricGluing.bankStackLeft Pieces Stack Base Gap
local notation "Rgt" => MetricGluing.bankStackRight Pieces Stack Base Gap
local notation "Banks" => MetricGluing.bankSeams L Rgt

local notation "Surface" => SpatialEnvelope.wholeSurface M.plane

local notation "Point" => MetricGluing.point Pieces Banks
local notation "Phys" => K.compatibleContourPhysicalAttachmentPoint compact nonempty R no_boundary
  level higher M positive inner_disk beta acute contour starts W

local notation "Height" => SlopeEnvelope.height (K.clippedExtension slopes compact nonempty)

local notation "Conforming" => K.compatibleCutMesh_conforming compact nonempty R no_boundary
  level higher M positive inner_disk
local notation "Inside" => K.compatible_section_interior compact nonempty R level higher M
local notation "Q" => SpatialEnvelope.Triangulation.roof
  (SpatialEnvelope.ConstrainedTriangulation.toTriangulation T) Conforming Inside
local notation "VertexAt[" v "]" => ConvexRoof.projectedVertex Q v

local notation "Terminal" => TriangleComplex.ContourTerminalEdge D Selection
local notation "RootAt[" e "]" => K.compatibleMeshTerminalRoot compact nonempty R no_boundary
  level higher M positive inner_disk beta acute (Subtype.val e)
  (TriangleComplex.contourTerminalEdge_positive D Selection e)

set_option maxHeartbeats 3300000 in
/-- Every full fiber of the actual marked spatial collapse is contractible. -/
theorem compatibleContourSourceOnlyCollapse_contractibleFiber
    (f : Graft → Space) (image : Set.range f ⊆ Surface)
    (roof : ∀ x : W.Cut, f (Point ⟨none, x⟩) = (W.partition.restoreCut R.carrier x).val)
    (boundary_gap : ∀ (e : Event) (x : PolygonalPoint (models e).region)
      (h : x.val ∈ frontier (models e).region),
      f (Point ⟨some e, x⟩) = (FoldAt[e] ⟨x.val, h⟩).val)
    (marked : ∀ e : Event, (models e).HasMarkedCollapseFibers (SpatialAt[e])
      (fun y => f (Point ⟨some e, y⟩)))
    (p : Space) (hp : p ∈ Surface) : ContractibleSpace {x : Graft | f x = p} := by
  by_cases on_cut : Cap.horizontal p ∈ R.carrier
  · obtain ⟨x, hx⟩ := W.partition.restoreCut_surjective R.carrier ⟨p, hp⟩
    have hroof : f (Point ⟨none, x⟩) = p := (roof x).trans (congrArg PolygonalPoint.val hx)
    have projected : Cap.horizontal (W.partition.restoreCut R.carrier x).val =
        Cap.horizontal p := congrArg Cap.horizontal (congrArg PolygonalPoint.val hx)
    have named (b : Attachment) (flag : Bool) (t : ParamAt b) (name : Base b flag t = x) :
        Cap.horizontal p = Phys b t := by
      have h := K.compatibleContourSourceOnlyCollapse_mark_horizontal compact nonempty R no_boundary
        level higher M positive inner_disk beta acute contour starts W models geometry f roof
        boundary_gap ⟨b, none, flag, t⟩ trivial
      exact (congrArg Cap.horizontal ((congrArg (fun y => f (Point ⟨none, y⟩)) name).trans hroof)).symm.trans h
    by_cases below : Height (Cap.horizontal p) < level
    · obtain ⟨e, flag, t, at_x⟩ := K.compatibleContourParentMark_exists_of_mem_cut_below compact
        nonempty R no_boundary level higher M positive inner_disk beta acute contour starts W
        x (projected.symm ▸ on_cut) (projected.symm ▸ below)
      have pos := named (.inl e) flag t at_x
      have line := K.compatibleContourPhysicalAttachmentPoint_finite compact nonempty R no_boundary
        level higher M positive inner_disk beta acute contour starts W e t
      by_cases zero : t = 0
      · subst t
        have at_e : Cap.horizontal p = VertexAt[e.val] :=
          (pos.trans line).trans (AffineMap.lineMap_apply_zero ..)
        exact K.compatibleContourSourceOnlyCollapse_fiber_of_vertex compact nonempty R no_boundary
          level higher M positive inner_disk beta acute contour starts W geometry f image roof
          boundary_gap marked e p hp at_e
      by_cases one : t = 1
      · subst t
        have at_parent : Cap.horizontal p = VertexAt[(Fcut).parents.parent e.val] :=
          (pos.trans line).trans (AffineMap.lineMap_apply_one ..)
        have parent_nonroot : (Fcut).parents.parent e.val ∉ (Fcut).parents.roots := by
          intro root
          let terminal : Terminal := ⟨e.val, e.property, root⟩
          have mark := K.compatibleContourTerminalMark_zero compact nonempty R no_boundary level
            higher M positive inner_disk beta acute contour starts W terminal false
          have join : Phys (.inr terminal) 0 = Phys (.inl e) 1 :=
            congrArg (fun y : W.Cut => Cap.horizontal (W.partition.restoreCut R.carrier y).val) mark
          have zero_time := K.compatibleContourPhysicalAttachmentPoint_tail_zero compact nonempty R
            no_boundary level higher M positive inner_disk beta acute contour starts W terminal
          exact below.ne ((congrArg Height (pos.trans (join.symm.trans zero_time))).trans
            (R.terminalPoint_level level higher RootAt[terminal]))
        exact K.compatibleContourSourceOnlyCollapse_fiber_of_vertex compact nonempty R no_boundary
          level higher M positive inner_disk beta acute contour starts W geometry f image roof
          boundary_gap marked ⟨_, parent_nonroot⟩ p hp at_parent
      have strict : 0 < t ∧ t < 1 := by
        constructor
        · exact lt_of_le_of_ne t.property.1 (Ne.symm zero)
        · exact lt_of_le_of_ne t.property.2 one
      exact K.compatibleContourSourceOnlyCollapse_fiber_of_strict_address compact nonempty R
        no_boundary level higher M positive inner_disk beta acute contour starts W models geometry
        f image roof boundary_gap marked (.inl e) t strict
        (K.compatibleContourPhysicalAttachmentPoint_eq_of_finite_interior compact nonempty R
          no_boundary level higher M positive inner_disk beta acute contour starts W e t strict)
        p hp pos
    · obtain ⟨e, flag, t, at_x⟩ := K.compatibleContourTailMark_exists_of_mem_cut_above compact
        nonempty R no_boundary level higher M positive inner_disk beta acute contour starts W
        x (projected.symm ▸ on_cut) (projected.symm ▸ le_of_not_gt below)
      have pos := named (.inr e) flag t at_x
      by_cases zero : t = 0
      · subst t
        exact K.compatibleContourSourceOnlyCollapse_fiber_of_terminal_join compact nonempty R
          no_boundary level higher M positive inner_disk beta acute contour starts W models
          geometry f image roof boundary_gap marked e p hp pos
      have strict : 0 < t := lt_of_le_of_ne zero_le (Ne.symm zero)
      exact K.compatibleContourSourceOnlyCollapse_fiber_of_strict_address compact nonempty R
        no_boundary level higher M positive inner_disk beta acute contour starts W models geometry
        f image roof boundary_gap marked (.inr e) t strict
        (K.compatibleContourPhysicalAttachmentPoint_eq_of_positive_tail compact nonempty R
          no_boundary level higher M positive inner_disk beta acute contour starts W e t strict)
        p hp pos
  · exact K.compatibleContourSourceOnlyCollapse_fiber_off_cut compact nonempty R no_boundary
      level higher M positive inner_disk beta acute contour starts W models f roof marked p hp on_cut

local notation "Visit[" j "]" => TriangleComplex.contourOriginalVertex D Selection contour j
local notation "RawGraft" => MetricGluing.Realization Raw
  (MetricGluing.ClosedSeams.relation Seams)

set_option maxHeartbeats 3000000 in
-- Transfer the proper spatial collapse and the metric balls through the exact cell presentation.
/-- The actual source-only gap graft develops isometrically onto the entire plane. -/
theorem compatibleContourSourceOnlyGraft_exists_surjective_isometry
    (convex : Convex ℝ slopes) (ends : Visit[Fin.last contour.length] ∈ (Fcut).parents.roots)
    (strict : ∀ (e : Event) (k : Fin LengthAt[e]), let B := BankAt[e]
      0 < inner ℝ (B.chain.vertex k.succ.castSucc - B.start) (B.chain.edge k.succ)) :
    ∃ develop : Graft → Plane, Isometry develop ∧ Function.Surjective develop := by
  obtain ⟨f, proper, range_eq, roof, gap, _, marked⟩ :=
    K.compatibleContourSourceOnlyGraft_exists_proper_collapse_with_marked_fibers compact nonempty R
      no_boundary level higher M positive inner_disk beta acute contour starts W models geometry
      (fun _ => rfl)
  have image : Set.range f ⊆ Surface := range_eq.le
  have every (p : Surface) : ContractibleSpace {x : Graft | f x = p.val} :=
    K.compatibleContourSourceOnlyCollapse_contractibleFiber compact nonempty R no_boundary level
      higher M positive inner_disk beta acute contour starts W geometry f image roof gap marked
      p.val p.property
  let E := K.compatibleContourSourceOnlyClosedSeamsIsometry compact nonempty R no_boundary
    level higher M positive inner_disk beta acute contour starts W models
  let spatial (z : Graft) : Surface := ⟨f z, image (Set.mem_range_self z)⟩
  have spatial_proper : IsProperMap spatial :=
    isProperMap_of_comp_of_inj (proper.continuous.subtype_mk _)
      continuous_subtype_val proper Subtype.val_injective
  have spatial_onto : Function.Surjective spatial := by
    intro p
    obtain ⟨z, at_p⟩ : p.val ∈ Set.range f := range_eq.symm ▸ p.property
    exact ⟨z, Subtype.ext at_p⟩
  let collapse : RawGraft → Surface := spatial ∘ E
  let : ContractibleSpace Surface := (SpatialEnvelope.wholeSurfaceHomeomorph M.plane).contractibleSpace
  have all_fibers (p : Surface) : ContractibleSpace (collapse ⁻¹' {p}) := by
    let s : Set Graft := {z | f z = p.val}
    have preimage : collapse ⁻¹' {p} = E ⁻¹' s := by
      ext z
      change spatial (E z) = p ↔ f (E z) = p.val
      exact ⟨congrArg Subtype.val, fun h => Subtype.ext h⟩
    rw [preimage]
    let : ContractibleSpace s := every p
    let H := E.toHomeomorph
    exact ((H.image (H ⁻¹' s)).trans (Homeomorph.setCongr (H.image_preimage s))).contractibleSpace
  have cell (ij : Σ i, Index i) :=
    K.compatibleContourSourceOnlyCells_geometry compact nonempty R no_boundary level higher
      M positive inner_disk beta acute contour starts W models ij.1 ij.2
  have boundary_only := K.compatibleContourSourceOnlyClosedSeams_boundary compact nonempty R
    no_boundary level higher M positive inner_disk beta acute contour starts W models
  have flat (z : RawGraft) : HasMetricBallChart Plane z :=
    (hasMetricBallChart_isometryEquiv_iff E z).mp
      (K.compatibleContourSourceOnlyGraft_hasMetricBallChart compact nonempty R no_boundary level
        higher M positive inner_disk beta acute contour starts W geometry convex ends strict (E z))
  obtain ⟨develop, preserves, onto⟩ :=
    MetricGluing.exists_global_planar_isometry_of_proper_contractible_fibers
      (fun ij : Σ i, Index i => Cells ij.1 ij.2) (Seams).relation collapse
      (spatial_proper.comp E.toHomeomorph.isProperMap) (spatial_onto.comp E.surjective) all_fibers
      (fun ij => (cell ij).1) (fun ij => (cell ij).2.1) (fun ij => (cell ij).2.2) boundary_only flat
  exact ⟨develop ∘ E.symm, preserves.comp E.symm.isometry, onto.comp E.symm.surjective⟩

end Unfoldings.ConvexRoof
