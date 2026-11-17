module

public import Unfoldings.Roof.CompatibleProcessedBankInterior
public import Unfoldings.Roof.SpatialEnvelopeVertexFibers

/-! Regular points on either original cut-bank side lie strictly below the original rim. -/

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

local instance processedCutBankInteriorIndexFintype : Fintype (T).Index :=
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
local notation "RetainAt[" S "]" => TriangleComplex.processedParentRetain
  (SpatialEnvelope.Triangulation.pairedComplex
    (SpatialEnvelope.ConstrainedTriangulation.toTriangulation T))
  (PotentialCutForest.selection Fcut) S

/-- Either labeled original cut-bank side has the same strict interior height bound. -/
theorem compatibleMeshProcessed_cutBank_height_lt
    (S : (Fcut).parents.ParentFrontier) (s : (T).pairedComplex.CutSeam RetainAt[S]) (side : Bool)
    (q : ((T).pairedComplex.triangle ((T).pairedComplex.cutBank RetainAt[S] s side).val.face).Edge
      ((T).pairedComplex.cutBank RetainAt[S] s side).val.edge)
    (regular : ¬ ((T).pairedComplex.triangle
      ((T).pairedComplex.cutBank RetainAt[S] s side).val.face).IsVertex q.val) :
    (K.clippedExtension slopes compact nonempty).height
      (Cap.horizontal ((T).pairedFolding.toSpace RetainAt[S]
        ((T).pairedComplex.bankMap RetainAt[S]
          ((T).pairedComplex.cutBank RetainAt[S] s side) q))) < level := by
  have original := K.compatibleMeshProcessed_removed_edge_height_lt compact nonempty R no_boundary
    level higher M positive inner_disk beta acute S s.val s.property
    ((T).pairedComplex.cutBankLeftParameterEquiv RetainAt[S] s side q)
    (fun vertex => regular
      (((T).pairedComplex.cutBankLeftParameter_isVertex_iff RetainAt[S] s side q).mp vertex))
  exact (congrArg (fun z : Space =>
    (K.clippedExtension slopes compact nonempty).height (Cap.horizontal z))
    ((T).pairedFolding.toSpace_cutBank_left_parameter RetainAt[S] s side q)).trans_lt original

/-- Every strict original interval time on either directed cut bank lies below the old rim. -/
theorem compatibleMeshProcessed_directedCutBank_height_lt
    (S : (Fcut).parents.ParentFrontier) (s : (T).pairedComplex.CutSeam RetainAt[S])
    (side flag : Bool)
    (u : unitInterval) (interior_time : 0 < u.val ∧ u.val < 1) :
    (K.clippedExtension slopes compact nonempty).height
      (Cap.horizontal ((T).pairedFolding.toSpace RetainAt[S]
        ((T).pairedComplex.directedBoundaryPath
          (((T).pairedComplex.boundaryEndEquiv RetainAt[S]).symm
            ((T).pairedComplex.cutBank RetainAt[S] s side, flag)) u))) < level := by
  let bank := (T).pairedComplex.cutBank RetainAt[S] s side
  have original := K.compatibleMeshProcessed_cutBank_height_lt compact nonempty R no_boundary
    level higher M positive inner_disk beta acute S s side
    ((T).pairedComplex.bankParameterFromEnd bank flag u)
    ((T).pairedComplex.bankParameterFromEnd_nonvertex bank flag u interior_time.1 interior_time.2)
  exact (congrArg (fun z => (K.clippedExtension slopes compact nonempty).height
    (Cap.horizontal ((T).pairedFolding.toSpace RetainAt[S] z)))
    ((T).pairedComplex.directedBoundaryPath_from_bank bank flag u)).trans_lt original

/-- A boundary bank starting strictly below the old rim was created by an actual
original cut. It cannot be an unpaired edge of the original finite roof. -/
theorem compatibleMeshProcessed_boundaryEnd_is_cut_of_height_lt
    (S : (Fcut).parents.ParentFrontier) (p : (T).pairedComplex.BoundaryEnd RetainAt[S])
    (below : (K.clippedExtension slopes compact nonempty).height
      (Cap.horizontal ((T).pairedFolding.boundaryPosition p)) < level) :
    ¬ (T).pairedComplex.IsBoundaryEdge Set.univ ((T).pairedComplex.germEdge p.val) := by
  let vertex := (T).pairedComplex.vertexForgetCuts (Set.subset_univ RetainAt[S])
    ((T).pairedComplex.boundaryEndVertex RetainAt[S] p)
  have internal : ¬ (T).pairedComplex.IsBoundaryVertex Set.univ vertex := by
    apply ((Q).projectedVertex_mem_interior_iff vertex).mp
    rw [(T).toTriangulation.roof_footprint conforming inside, M.clip_eq_sublevel, neg_neg]
    apply (K.clippedExtension slopes compact nonempty).mem_interior_sublevel
    exact (congrArg (K.clippedExtension slopes compact nonempty).height
      ((T).toTriangulation.roof_projectedVertex_vertexForgetCuts conforming inside RetainAt[S]
        ((T).pairedComplex.boundaryEndVertex RetainAt[S] p))).trans_lt below
  intro boundary
  apply internal
  have original := (T).pairedComplex.isBoundaryVertex_of_boundary_germ Set.univ p.val boundary
  simpa only [vertex, TriangleComplex.boundaryEndVertex,
    TriangleComplex.vertexForgetCuts_vertexOfCorner] using original

end Unfoldings.ConvexRoof
