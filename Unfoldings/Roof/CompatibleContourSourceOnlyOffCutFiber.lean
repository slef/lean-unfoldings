module

public import Unfoldings.Roof.CompatibleContourSourceOnlyCollapseNames
public import Unfoldings.Roof.CompatibleContourPhysicalTails

/-! The original roof supplies the singleton fibers away from the cut forest. -/

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

local instance sourceOnlyOffCutFiberIndexFintype : Fintype (T).Index :=
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
  (models : ∀ event : (K.compatibleCutMesh compact nonempty R no_boundary level higher M
      positive inner_disk).pairedComplex.PositiveContourSource
      (K.compatibleMeshForest compact nonempty R no_boundary level higher M positive
        inner_disk beta acute).selection contour,
    BankGapModel
      (K.compatibleContourSourceBank compact nonempty R no_boundary level higher M positive
        inner_disk beta acute contour starts event)
      (K.compatibleContourSourceOnlyBank compact nonempty R no_boundary level higher M positive
        inner_disk beta acute contour starts event))

local instance sourceOnlyOffCutFiberWholeFintype : Fintype W.Index := W.finiteIndex

local notation "Event" => TriangleComplex.PositiveContourSource D Selection contour
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
local notation "SpatialAt[" e "]" => K.compatibleContourPhysicalBank compact nonempty R no_boundary
  level higher M positive inner_disk beta acute contour starts e
local notation "Index" => K.compatibleContourSourceOnlyCellIndex compact nonempty R no_boundary
  level higher M positive inner_disk beta acute contour starts W models

local notation "Graft" => K.compatibleContourSourceOnlyGraft compact nonempty R no_boundary
  level higher M positive inner_disk beta acute contour starts W models
local notation "L" => MetricGluing.bankStackLeft Pieces Stack Base Gap
local notation "Rgt" => MetricGluing.bankStackRight Pieces Stack Base Gap
local notation "Banks" => MetricGluing.bankSeams L Rgt

local notation "Surface" => SpatialEnvelope.wholeSurface M.plane

local notation "Point" => MetricGluing.point Pieces Banks
local notation "AddressAt[" b "," e "," h "," t "]" => K.compatibleContourGapAddress compact
  nonempty R no_boundary level higher M positive inner_disk beta acute contour b e h t

include W in
/-- An address of a spatial gap path is literally the restored point of its named roof bank. -/
theorem compatibleContourPhysicalBank_addressPoint_eq_restore
    (e : Event) (b : Attachment) (mem : e ∈ Stack b) (t : ParamAt b) :
    (SpatialAt[e]).addressPoint AddressAt[b,e,mem,t] =
      (W.partition.restoreCut R.carrier (Base b false t)).val := by
  cases b with
  | inl v =>
    exact (K.compatibleContourPhysicalBank_parent_point compact nonempty R no_boundary level higher
      M positive inner_disk beta acute contour starts v.val v.property e mem t).trans
      (K.restore_compatibleContourParentMark_position compact nonempty R no_boundary level higher
        M positive inner_disk beta acute contour starts W v.val v.property false t).symm
  | inr edge =>
    exact (K.compatibleContourPhysicalBank_tail_parent compact nonempty R no_boundary level higher
      M positive inner_disk beta acute contour starts W edge e mem t).trans
      (K.restore_compatibleContourTerminalMark_affine compact nonempty R no_boundary level higher
        M positive inner_disk beta acute contour starts W edge false t).symm

include W in
/-- Every point of an actual spatial gap path projects to the original cut forest. -/
theorem compatibleContourPhysicalBank_horizontal_mem_carrier
    (e : Event) {p : Space} (on_path : p ∈ (SpatialAt[e]).carrier) :
    Cap.horizontal p ∈ R.carrier := by
  obtain ⟨a, point⟩ := (SpatialAt[e]).exists_address on_path
  obtain ⟨b, mem, t, address⟩ := K.exists_compatibleContourGapAddress_eq compact nonempty R
    no_boundary level higher M positive inner_disk beta acute contour e a
  have named := K.compatibleContourPhysicalBank_addressPoint_eq_restore compact nonempty R
    no_boundary level higher M positive inner_disk beta acute contour starts W e b mem t
  have loc := point.symm.trans ((congrArg ((SpatialAt[e]).addressPoint) address.symm).trans named)
  rw [loc]
  cases b with
  | inl v =>
    exact K.compatibleContourParentMark_carrier compact nonempty R no_boundary level higher M
      positive inner_disk beta acute contour starts W v.val v.property false t
  | inr edge =>
    exact K.compatibleContourTerminalMark_carrier compact nonempty R no_boundary level higher M
      positive inner_disk beta acute contour starts W edge false t

set_option maxHeartbeats 1100000 in
-- The unique actual roof copy transports through the original cut partition isometry.
/-- An off-cut fiber of the marked collapse is exactly one original roof point. -/
theorem compatibleContourSourceOnlyCollapse_fiber_off_cut
    (f : Graft → Space)
    (roof : ∀ x : W.Cut, f (Point ⟨none, x⟩) = (W.partition.restoreCut R.carrier x).val)
    (marked : ∀ e : Event, (models e).HasMarkedCollapseFibers (SpatialAt[e])
      (fun y => f (Point ⟨some e, y⟩)))
    (p : Space) (inside : p ∈ Surface) (off_cut : Cap.horizontal p ∉ R.carrier) :
    ContractibleSpace {x : Graft | f x = p} := by
  obtain ⟨x, hx⟩ := W.partition.restoreCut_surjective R.carrier ⟨p, inside⟩
  have p_x : f (Point ⟨none, x⟩) = p := (roof x).trans (congrArg PolygonalPoint.val hx)
  have unique (z : Graft) (hz : f z = p) : z = Point ⟨none, x⟩ := by
    obtain ⟨⟨i, y⟩, rfl⟩ := MetricGluing.point_surjective Pieces Banks z
    cases i with
    | some e =>
      have on_path : p ∈ (SpatialAt[e]).carrier := (marked e).1 ⟨y, hz⟩
      exact (off_cut (K.compatibleContourPhysicalBank_horizontal_mem_carrier compact nonempty R
        no_boundary level higher M positive inner_disk beta acute contour starts W e on_path)).elim
    | none =>
      have equal : W.partition.restoreCut R.carrier y = W.partition.restoreCut R.carrier x :=
        PolygonalPoint.ext ((roof y).symm.trans (hz.trans p_x.symm) |>.trans (roof x))
      have outside : Cap.horizontal (W.partition.restoreCut R.carrier y).val ∉ R.carrier :=
        fun h => off_cut ((congrArg Cap.horizontal ((roof y).symm.trans hz)) ▸ h)
      let E := W.partition.cutIsometryEquiv R.carrier
      have same : y = x := E.injective
        (MetricGluing.cutToPolygonal_injective_off_cuts W.partition.spatialCell
          W.partition.isClosed_spatialCell (Cap.horizontal ⁻¹' R.carrier)
          W.partition.convex_spatialCell W.partition.wholeSurface_eq_iUnion_spatialCell equal outside)
      exact congrArg (fun y => Point ⟨none, y⟩) same
  let : Nonempty {x : Graft | f x = p} := ⟨⟨Point ⟨none, x⟩, p_x⟩⟩
  let : Subsingleton {x : Graft | f x = p} :=
    ⟨fun q r => Subtype.ext ((unique q.val q.property).trans (unique r.val r.property).symm)⟩
  infer_instance

end Unfoldings.ConvexRoof
