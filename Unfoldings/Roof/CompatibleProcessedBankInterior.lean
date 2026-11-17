module

public import Unfoldings.Roof.CompatibleProcessedBankMetric
public import Unfoldings.Polyhedron.CutBankParameters
public import Unfoldings.Metric.ClosedUnitIntervalLineMap

/-! Every regular point of a processed original seam lies strictly below the original rim. -/

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
local notation "conforming" => K.compatibleCutMesh_conforming compact nonempty R no_boundary
  level higher M positive inner_disk
local notation "inside" => K.compatible_section_interior compact nonempty R level higher M
local notation "Q" => SpatialEnvelope.Triangulation.roof
  (SpatialEnvelope.ConstrainedTriangulation.toTriangulation T) conforming inside
local notation "Fcut" => K.compatibleMeshForest compact nonempty R no_boundary level higher
  M positive inner_disk beta acute

local instance processedBankInteriorIndexFintype : Fintype (T).Index :=
  @Fintype.ofFinite _ (T).finite

local notation "B" => SlopeEnvelope.boundaryEnvelope
  (K.clippedExtension slopes compact nonempty) boundary
local notation "Gcut" => K.truncatedCutEmbedding compact nonempty R no_boundary level higher


local notation "V" => R.levelWindowModel M level higher
local notation "proper" => R.levelWindow_proper M level higher
local notation "full" => R.levelWindow_full M level higher
local notation "domain" => SpatialEnvelope.levelEquation_domain M.plane (-level)
local notation "heights" => (Set.eqOn_refl (SpatialEnvelope.height M.plane) _)
local notation "outside" => K.compatibleMesh_cut_disjoint_interior compact nonempty R
  no_boundary level higher M positive inner_disk
/-- A regular point of a removed original seam stays strictly below the old rim.
The original open seam avoids the outer cut tails, independently of later subdivisions. -/
theorem compatibleMeshProcessed_removed_edge_height_lt
    (S : (Fcut).parents.ParentFrontier) (s : (T).pairedComplex.Seam) (removed : s ∉
      (T).pairedComplex.processedParentRetain (Fcut).selection S)
    (q : ((T).pairedComplex.triangle ((T).pairedComplex.left s).face).Edge
      ((T).pairedComplex.left s).edge)
    (regular : ¬ ((T).pairedComplex.triangle ((T).pairedComplex.left s).face).IsVertex q.val) :
    (K.clippedExtension slopes compact nonempty).height
      (Cap.horizontal ((T).pairedFolding.place ((T).pairedComplex.left s).face q.val)) < level := by
  by_contra missing
  have above := le_of_not_gt missing
  have on_cut := K.compatibleMeshProcessed_removed_edge compact nonempty R no_boundary level
    higher M
    positive inner_disk beta acute S s removed q
  have carrier := K.compatibleMeshProcessedCarrier_subset compact nonempty R no_boundary level
    higher
    M positive inner_disk beta acute S on_cut
  have raw_open : q.val ∈ openSegment ℝ
      (((T).pairedComplex.triangle ((T).pairedComplex.left s).face).vertex
        ((T).pairedComplex.left s).edge)
      (((T).pairedComplex.triangle ((T).pairedComplex.left s).face).vertex
        (Triangle.next ((T).pairedComplex.left s).edge)) :=
    mem_openSegment_of_ne_left_right (fun equal => regular ⟨_, equal⟩)
      (fun equal => regular ⟨_, equal⟩) q.property
  have on_open : (T).pairedFolding.place ((T).pairedComplex.left s).face q.val ∈
      (T).pairedFolding.openSeamImage s :=
    (image_openSegment ℝ ((T).pairedFolding.place ((T).pairedComplex.left s).face).toAffineMap
      _ _).subset ⟨q.val, raw_open, rfl⟩
  exact Set.disjoint_left.mp
    (K.compatibleMesh_openSeam_disjoint_outer compact nonempty R no_boundary level higher M positive
      inner_disk s) on_open ⟨carrier, above⟩

variable (W : R.WholeCutModel M)

local instance processedBankInteriorWholeFintype : Fintype W.Index := W.finiteIndex

local notation "RetainAt[" S "]" => TriangleComplex.processedParentRetain
  (SpatialEnvelope.Triangulation.pairedComplex
    (SpatialEnvelope.ConstrainedTriangulation.toTriangulation T))
  (PotentialCutForest.selection Fcut) S
local notation "CutsAt[" S "]" => K.compatibleMeshProcessedCarrier compact nonempty R no_boundary
  level higher M positive inner_disk beta acute S
local notation "SeamBankAt[" S "," s "," h "," b "]" =>
  K.compatibleMeshProcessedSeamBank compact nonempty R no_boundary level higher M positive
    inner_disk beta acute W S s h b

/-- Original cut geometry supplies the strict interior bound needed for side matching.
Matching on a connected dense regular portion fixes the complete bank, including endpoints. -/
theorem compatibleMeshProcessedSeamBank_side_of_dense_original_cut
    {A : Type*} [TopologicalSpace A]
    (S : (Fcut).parents.ParentFrontier) (s : (T).pairedComplex.Seam) (removed : s ∉ RetainAt[S])
    (curve : A → W.partition.Cut CutsAt[S]) (continuous_curve : Continuous curve)
    (point : A → ((T).pairedComplex.triangle ((T).pairedComplex.left s).face).Edge
      ((T).pairedComplex.left s).edge) (continuous_point : Continuous point)
    (portion : Set A) (connected : IsPreconnected portion) (dense : Dense portion)
    (regular : ∀ a ∈ portion,
      ¬ ((T).pairedComplex.triangle ((T).pairedComplex.left s).face).IsVertex (point a).val)
    (position : ∀ a, (W.partition.restoreCut CutsAt[S] (curve a)).val =
      (T).pairedFolding.place ((T).pairedComplex.left s).face (point a).val) :
    ∃ side : Bool, ∀ a, curve a = SeamBankAt[S,s,removed,side] (point a) :=
  K.compatibleMeshProcessedSeamBank_side_of_dense_regular compact nonempty R no_boundary level
    higher M positive inner_disk beta acute W S s removed curve continuous_curve point
    continuous_point portion connected dense regular
    (fun a member => K.compatibleMeshProcessed_removed_edge_height_lt compact nonempty R no_boundary
      level higher M positive inner_disk beta acute S s removed (point a)
        (regular a member)) position

/-- One named regular contact determines the original side of the entire continuous
bank, including its endpoint copies. No separate interior-height premise is needed. -/
theorem compatibleMeshProcessedSeamBank_eq_of_dense_original_cut_contact
    {A : Type*} [TopologicalSpace A]
    (S : (Fcut).parents.ParentFrontier) (s : (T).pairedComplex.Seam) (removed : s ∉ RetainAt[S])
    (curve : A → W.partition.Cut CutsAt[S]) (continuous_curve : Continuous curve)
    (point : A → ((T).pairedComplex.triangle ((T).pairedComplex.left s).face).Edge
      ((T).pairedComplex.left s).edge) (continuous_point : Continuous point)
    (portion : Set A) (connected : IsPreconnected portion) (dense : Dense portion)
    (regular : ∀ a ∈ portion,
      ¬ ((T).pairedComplex.triangle ((T).pairedComplex.left s).face).IsVertex (point a).val)
    (position : ∀ a, (W.partition.restoreCut CutsAt[S] (curve a)).val =
      (T).pairedFolding.place ((T).pairedComplex.left s).face (point a).val)
    (side : Bool) (a : A) (interior_contact : a ∈ portion)
    (contact : curve a = SeamBankAt[S,s,removed,side] (point a)) :
    ∀ t, curve t = SeamBankAt[S,s,removed,side] (point t) := by
  obtain ⟨chosen, matched_paths⟩ :=
    K.compatibleMeshProcessedSeamBank_side_of_dense_original_cut compact nonempty R no_boundary
      level higher M positive inner_disk beta acute W S s removed curve continuous_curve point
      continuous_point portion connected dense regular position
  by_cases same : chosen = side
  · exact same ▸ matched_paths
  · have separated := K.compatibleMeshProcessedSeamBank_ne compact nonempty R no_boundary level
      higher M positive inner_disk beta acute W S s removed chosen side same (point a) (point a)
      (regular a interior_contact)
      (K.compatibleMeshProcessed_removed_edge_height_lt compact nonempty R no_boundary level
        higher M
        positive inner_disk beta acute S s removed (point a) (regular a interior_contact))
    exact (separated ((matched_paths a).symm.trans contact)).elim

local notation "MapAt[" S "]" => K.compatibleMeshProcessedWholeMap compact nonempty R no_boundary
  level higher M positive inner_disk beta acute W S

/-- The labeled original finite bank and the common left-edge bank coordinates
identify exactly the same whole-cut copy. -/
theorem compatibleMeshProcessedWholeMap_cutBank_left_parameter
    (S : (Fcut).parents.ParentFrontier) (s : (T).pairedComplex.CutSeam RetainAt[S]) (side : Bool)
    (q : ((T).pairedComplex.triangle ((T).pairedComplex.cutBank RetainAt[S] s side).val.face).Edge
      ((T).pairedComplex.cutBank RetainAt[S] s side).val.edge) :
    MapAt[S] ((T).pairedComplex.bankMap RetainAt[S]
      ((T).pairedComplex.cutBank RetainAt[S] s side) q) =
      SeamBankAt[S,s.val,s.property,side]
        ((T).pairedComplex.cutBankLeftParameterEquiv RetainAt[S] s side q) := by
  cases side
  · rfl
  · exact congrArg (fun z => MapAt[S] ((T).pairedComplex.bankMap RetainAt[S]
      ((T).pairedComplex.rightBank RetainAt[S] s.val s.property) z))
      ((T).pairedComplex.identify s.val |>.apply_symm_apply q).symm

/-- A whole-cut curve over a forward subinterval of an original removed bank is
that same original bank everywhere once one regular contact fixes its side. -/
theorem compatibleMeshProcessedCutBank_eq_of_subinterval_contact
    (S : (Fcut).parents.ParentFrontier) (s : (T).pairedComplex.CutSeam RetainAt[S])
    (side flag : Bool) (first last : unitInterval) (forward : first.val < last.val)
    (curve : unitInterval → W.partition.Cut CutsAt[S]) (continuous_curve : Continuous curve)
    (position : ∀ u, (W.partition.restoreCut CutsAt[S] (curve u)).val =
      (T).pairedFolding.toSpace RetainAt[S]
        ((T).pairedComplex.directedBoundaryPath
          (((T).pairedComplex.boundaryEndEquiv RetainAt[S]).symm
            ((T).pairedComplex.cutBank RetainAt[S] s side, flag))
          (closedUnitIntervalLineMap first last forward.le u)))
    (t : unitInterval) (interior_contact : t ∈ Set.Ioo (0 : unitInterval) 1)
    (contact : curve t = MapAt[S] ((T).pairedComplex.directedBoundaryPath
      (((T).pairedComplex.boundaryEndEquiv RetainAt[S]).symm
        ((T).pairedComplex.cutBank RetainAt[S] s side, flag))
      (closedUnitIntervalLineMap first last forward.le t))) :
    ∀ u, curve u = MapAt[S] ((T).pairedComplex.directedBoundaryPath
      (((T).pairedComplex.boundaryEndEquiv RetainAt[S]).symm
        ((T).pairedComplex.cutBank RetainAt[S] s side, flag))
      (closedUnitIntervalLineMap first last forward.le u)) := by
  let bank := (T).pairedComplex.cutBank RetainAt[S] s side
  let clock := closedUnitIntervalLineMap first last forward.le
  let point (u : unitInterval) := (T).pairedComplex.cutBankLeftParameterEquiv RetainAt[S] s side
    ((T).pairedComplex.bankParameterFromEnd bank flag (clock u))
  have continuous_parameter : Continuous ((T).pairedComplex.bankParameterFromEnd bank flag) := by
    unfold TriangleComplex.bankParameterFromEnd
    fun_prop
  have continuous_point : Continuous point :=
    ((T).pairedComplex.cutBankLeftParameterEquiv RetainAt[S] s side).continuous.comp
      (continuous_parameter.comp (continuous_closedUnitIntervalLineMap first last forward.le))
  have target (u : unitInterval) :=
    (congrArg MapAt[S] ((T).pairedComplex.directedBoundaryPath_from_bank bank flag (clock u))).trans
      (K.compatibleMeshProcessedWholeMap_cutBank_left_parameter compact nonempty R no_boundary level
        higher M positive inner_disk beta acute W S s side
        ((T).pairedComplex.bankParameterFromEnd bank flag (clock u)))
  have regular (u : unitInterval) (member : u ∈ Set.Ioo (0 : unitInterval) 1) :
      ¬ ((T).pairedComplex.triangle ((T).pairedComplex.left s.val).face).IsVertex
        (point u).val := by
    have interior_time := closedUnitIntervalLineMap_strict first last forward u member
    intro vertex
    exact (T).pairedComplex.bankParameterFromEnd_nonvertex bank flag (clock u)
      interior_time.1 interior_time.2
      (((T).pairedComplex.cutBankLeftParameter_isVertex_iff RetainAt[S] s side _).mp vertex)
  have physical (u : unitInterval) := (position u).trans
    ((congrArg ((T).pairedFolding.toSpace RetainAt[S])
      ((T).pairedComplex.directedBoundaryPath_from_bank bank flag (clock u))).trans
      ((T).pairedFolding.toSpace_cutBank_left_parameter RetainAt[S] s side
        ((T).pairedComplex.bankParameterFromEnd bank flag (clock u))))
  have matched_paths :=
    K.compatibleMeshProcessedSeamBank_eq_of_dense_original_cut_contact compact nonempty R
      no_boundary
      level higher M positive inner_disk beta acute W S s.val s.property curve continuous_curve
      point continuous_point (Set.Ioo (0 : unitInterval) 1) isPreconnected_Ioo
      dense_unitInterval_interior regular physical side t interior_contact
      (contact.trans (target t))
  exact fun u => (matched_paths u).trans (target u).symm

end Unfoldings.ConvexRoof
