module

public import Unfoldings.Roof.CompatibleContourSourceOnlyLabels
public import Unfoldings.Roof.CompatibleMeshInteriorFiber
public import Unfoldings.Roof.ConstructedFiniteTerminalBoundary
public import Unfoldings.Roof.CompatibleContourTerminalSideLabels
public import Unfoldings.Complex.DirectedBoundaryPathReversal

/-! Every actual cut-roof copy on the physical forest has a named bank address. -/

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

local instance sourceOnlyRoofAddressCoverageIndexFintype : Fintype (T).Index :=
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

local instance sourceOnlyRoofAddressCoverageWholeFintype : Fintype W.Index := W.finiteIndex

local notation "Edge" => {v : TriangleComplex.Vertex D Set.univ //
  v ∉ AscendingParents.roots (PotentialCutForest.parents Fcut)}
local notation "Interval[" v "," h "]" => TriangleComplex.contourParentInterval
  D Selection contour (PotentialCutForest.boundary_roots Fcut) starts v h
local notation "Map" => K.compatibleMeshWholeMap compact nonempty R no_boundary level higher M
  positive inner_disk beta acute W
local notation "Retain" => PotentialCutForest.retain Fcut
local notation "Height" => SlopeEnvelope.height (K.clippedExtension slopes compact nonempty)
local notation "Conforming" => K.compatibleCutMesh_conforming compact nonempty R no_boundary
  level higher M positive inner_disk
local notation "Inside" => K.compatible_section_interior compact nonempty R level higher M

set_option maxHeartbeats 1700000 in
-- The finite cut mesh and the extended roof use the same dependent retained-bank labels.
/-- Below the truncation level, every roof copy of a physical cut point is a
named mark on an actual selected finite parent edge. -/
theorem compatibleContourParentMark_exists_of_mem_cut_below
    (x : W.Cut) (on_cut : Cap.horizontal (W.partition.restoreCut R.carrier x).val ∈ R.carrier)
    (below : Height (Cap.horizontal (W.partition.restoreCut R.carrier x).val) < level) :
    ∃ (p : Edge) (side : Bool) (t : unitInterval),
      K.compatibleContourParentMark compact nonempty R no_boundary level higher M positive
        inner_disk beta acute contour starts W p.val p.property side t = x := by
  let restored (x : W.Cut) := Cap.horizontal (W.partition.restoreCut R.carrier x).val
  let folding := (T).pairedFolding
  change restored x ∈ R.carrier at on_cut
  change Height (restored x) < level at below
  obtain ⟨y, mapped, _⟩ := K.existsUnique_compatibleMesh_preimage compact nonempty R no_boundary
    level higher M positive inner_disk beta acute W x below
  have position : Cap.horizontal (folding.toSpace Retain y) = restored x :=
    (congrArg Cap.horizontal (K.restore_compatibleMeshWholeMap compact nonempty R no_boundary
      level higher M positive inner_disk beta acute W y)).symm.trans (congrArg restored mapped)
  have in_cut : restored x ∈ R.truncatedCarrier level higher :=
    (R.mem_truncatedCarrier_iff level higher below.le).mpr on_cut
  have inside : restored x ∈ interior (SpatialEnvelope.clip M.plane (-level)) := by
    rw [M.clip_eq_sublevel, neg_neg]
    exact (K.clippedExtension slopes compact nonempty).mem_interior_sublevel below
  obtain ⟨s, not_kept, on_edge⟩ := K.compatibleCutMesh_cut_seam compact nonempty R no_boundary
    level higher M positive inner_disk in_cut inside
  have removed : s ∉ Retain := by
    rwa [K.compatibleMesh_retain_eq_prescribed compact nonempty R no_boundary level higher
      M positive inner_disk beta acute]
  let q := ((T).edgeProjection ((D).left s).face ((D).left s).edge).symm ⟨restored x, on_edge⟩
  have projected : Cap.horizontal (folding.place ((D).left s).face q.val) = restored x :=
    ((M.plane ((T).support ((D).left s).face)).horizontal_place q.val).trans
      ((M.plane ((T).support ((D).left s).face)).project.apply_symm_apply _)
  have on_boundary := (T).toTriangulation.mem_bankBoundary_of_projected_cut_edge Conforming
    Retain s removed q y (position.trans projected.symm)
  obtain ⟨bank, z, rfl⟩ := Set.mem_iUnion.mp on_boundary
  rcases (D).relativeBank_cases Retain Set.univ bank with old | ⟨cut, bit, cut_bank⟩
  · have at_rim := (T).toTriangulation.bank_height Conforming Inside ⟨bank.val, old⟩ z
    have roof : (T).placement bank.val.face z.val 2 =
        SpatialEnvelope.height M.plane (Cap.horizontal ((T).placement bank.val.face z.val)) := by
      rw [(T).toTriangulation.placement_eq_point bank.val.face
        (((T).triangle bank.val.face).edge_subset bank.val.edge z.property),
        SpatialEnvelope.height_point, SpatialEnvelope.horizontal_point]
    have physic : Cap.horizontal ((T).placement bank.val.face z.val) = restored x := position
    have height_eq : Height (restored x) = level :=
      (congrArg Height physic).symm.trans (neg_injective
        ((roof.trans (M.height_eq _)).symm.trans at_rim))
    exact (below.ne height_eq).elim
  · have selected : cut.val ∈ Set.range (Selection).edge := Classical.not_not.mp cut.property.2
    obtain ⟨p, named⟩ := selected
    have tag : (D).selectedParentCut Selection p.val p.property = cut := Subtype.ext named
    let data := Interval[p.val,p.property]
    let parent_bank (side : Bool) :=
      (D).contourParentBank Selection contour (Fcut).boundary_roots starts p.val p.property side
    have names : ∃ side, ((D).boundaryEndEquiv Retain (parent_bank side)).1 = bank := by
      by_cases h : bit = data.side
      · have turn := ((D).boundaryEnd_bank_eq_iff Retain (parent_bank true)
          (contour.cycle.point data.enter)).mpr (Or.inr rfl)
        exact ⟨true, turn.trans (data.entry_named.trans
          ((congrArg (fun k => (D).relativeCutBank Retain Set.univ k data.side) tag).trans
            ((congrArg ((D).relativeCutBank Retain Set.univ cut) h.symm).trans cut_bank.symm)))⟩
      · have h' : bit = !data.side := by cases bit <;> cases hd : data.side <;> simp_all
        refine ⟨false, data.exit_named.trans ?_⟩
        exact (congrArg (fun k => (D).relativeCutBank Retain Set.univ k (!data.side)) tag).trans
          ((congrArg ((D).relativeCutBank Retain Set.univ cut) h'.symm).trans cut_bank.symm)
    obtain ⟨side, name⟩ := names
    have on_path : (D).bankMap Retain bank z ∈ Set.range ((D).directedBoundaryPath (parent_bank side)) := by
      rw [(D).directedBoundaryPath_range]
      change _ ∈ Set.range ((D).bankMap Retain ((D).boundaryEndEquiv Retain (parent_bank side)).1)
      rw [name]
      exact ⟨z, rfl⟩
    obtain ⟨t, at_point⟩ := on_path
    exact ⟨p, side, t, (congrArg Map at_point).trans mapped⟩

end Unfoldings.ConvexRoof
