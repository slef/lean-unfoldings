module

public import Unfoldings.Roof.ConstructedFiniteTerminalBankChains
public import Unfoldings.Roof.PotentialContourHistory
public import Unfoldings.Complex.BoundaryContourAnchor

/-! Construct original rim-started compatible-cut histories, including flat unused roots. -/

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

local instance compatibleContourHistoryIndexFintype : Fintype (T).Index :=
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
local notation "removed" => K.compatibleMesh_removed_edge compact nonempty R no_boundary
  level higher M positive inner_disk beta acute
local notation "retained" => K.compatibleMesh_retained_open_edge compact nonempty R no_boundary
  level higher M positive inner_disk beta acute

variable (W : R.WholeCutModel M)

local instance compatibleContourHistoryWholeFintype : Fintype W.Index := W.finiteIndex

variable (r : {v // v ∈ R.parents.roots}) (side : Bool)

local notation "τ" => R.terminalTime level r
local notation "bank" => K.wholeTerminalBank compact nonempty R no_boundary W r side

/-- The named terminal endpoint is an actual boundary vertex copy of the finite cut. -/
theorem compatibleMeshTerminalFinishVertex_boundary :
    (T).pairedComplex.IsBoundaryVertex (Fcut).retain
      (K.compatibleMeshTerminalFinishVertex compact nonempty R no_boundary level higher M positive
        inner_disk beta acute W r side) := by
  apply ((T).pairedComplex.vertexPoint_mem_bankBoundary_iff (Fcut).retain _).mp
  rw [K.vertexPoint_compatibleMeshTerminalFinishVertex]
  exact K.compatibleMeshTerminalBank_mem_boundary compact nonempty R no_boundary level higher M
    positive inner_disk beta acute W r side ⟨τ, (R.terminalTime_pos level higher r).le, le_rfl⟩

/-- Anchor the actual constructed cut contour at the specified original terminal rim copy. -/
def compatibleMeshRimContour : (T).pairedComplex.BoundaryContour (Fcut).retain :=
  (K.compatibleMeshBoundaryContour compact nonempty R no_boundary level higher M positive
    inner_disk beta acute).anchor (T).pairedComplex
    (K.compatibleMeshTerminalFinishVertex compact nonempty R no_boundary level higher M positive
      inner_disk beta acute W r side)
    (K.compatibleMeshTerminalFinishVertex_boundary compact nonempty R no_boundary level higher M
      positive inner_disk beta acute W r side)

/-- The actual anchored contour starts at the same named original rim copy. -/
theorem compatibleMeshRimContour_first :
    (T).pairedComplex.boundaryEndVertex (Fcut).retain
      (K.compatibleMeshRimContour compact nonempty R no_boundary level higher M positive inner_disk
        beta acute W r side).cycle.first =
      K.compatibleMeshTerminalFinishVertex compact nonempty R no_boundary level higher M positive
        inner_disk beta acute W r side :=
  TriangleComplex.BoundaryContour.anchor_first _ _ _ _

/-- The starting root follows from the constructed rim endpoint, rather than a contour premise. -/
theorem compatibleMeshRimContour_starts_root :
    (T).pairedComplex.contourOriginalVertex (Fcut).selection
      (K.compatibleMeshRimContour compact nonempty R no_boundary level higher M positive inner_disk
        beta acute W r side) 0 ∈ (Fcut).parents.roots := by
  have same := congrArg ((T).pairedComplex.vertexForgetCuts (Set.subset_univ (Fcut).retain))
    (K.compatibleMeshRimContour_first compact nonempty R no_boundary level higher M positive
      inner_disk beta acute W r side)
  exact Eq.mpr (congrArg (fun v => v ∈ (Fcut).parents.roots) same)
    (K.compatibleMeshTerminalFinishVertex_root compact nonempty R no_boundary level higher M
      positive inner_disk beta acute W r side)

local notation "contour" => K.compatibleMeshRimContour compact nonempty R no_boundary level higher M
  positive inner_disk beta acute W r side

/-- The constructed original contour processes every original fine vertex. -/
theorem compatibleMeshRimContour_history_complete :
    (((Fcut).parents.initialFrontier).run
      ((T).pairedComplex.selectedContourSeeds (Fcut).selection contour)).processed = Set.univ :=
  (Fcut).contour_history_complete contour

/-- Exact curvature charges follow for the actual compatible mesh, including unused flat roots. -/
theorem compatibleMeshRimContour_history_curvature (convex : Convex ℝ slopes) :
    ((((Fcut).parents.initialFrontier).history
      ((T).pairedComplex.selectedContourSeeds (Fcut).selection contour)).map
        (fun v => (T).pairedComplex.interiorAngularDefect Set.univ v.val)).sum =
      (T).pairedComplex.totalInteriorAngularDefect Set.univ :=
  (Fcut).contour_history_curvature contour
    (K.compatibleMeshForest_curvature_covered compact nonempty R no_boundary level higher M positive
      inner_disk convex)

/-- Every actual contour step has at most one fresh selected seam. No extra cuts through
unused flat vertices, padding branches or supplied schedule are needed. -/
theorem compatibleMeshRimContour_contactTime_le_one (i : Fin ((contour).length + 1)) :
    ((T).pairedComplex.contourFrontier (Fcut).selection contour i).contactTime
      ((T).pairedComplex.contourOriginalVertex (Fcut).selection contour i) ≤ 1 :=
  (Fcut).contour_contactTime_le_one contour
    (K.compatibleMeshRimContour_starts_root compact nonempty R no_boundary level higher M positive
      inner_disk beta acute W r side) i

end Unfoldings.ConvexRoof
