module

public import Unfoldings.Roof.CompatibleMeshContourHistory
public import Unfoldings.Complex.SupportedRootwardReference

/-! Actual surviving rootward chains in the constructed compatible finite cut. -/

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

local instance compatibleRootwardChainIndexFintype : Fintype (T).Index :=
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

local instance compatibleRootwardChainWholeFintype : Fintype W.Index := W.finiteIndex

variable (r : {v // v ∈ R.parents.roots}) (side : Bool)

local notation "τ" => R.terminalTime level r
local notation "bank" => K.wholeTerminalBank compact nonempty R no_boundary W r side

local notation "contour" => K.compatibleMeshRimContour compact nonempty R no_boundary level higher M
  positive inner_disk beta acute W r side

/-- Every fresh source of the constructed actual contour has exactly one fresh parent seam. -/
theorem compatibleMeshRimContour_fresh_contactTime (i : Fin ((contour).length + 1))
    (fresh : (T).pairedComplex.contourOriginalVertex (Fcut).selection contour i ∉
      ((T).pairedComplex.contourFrontier (Fcut).selection contour i).processed) :
    ((T).pairedComplex.contourFrontier (Fcut).selection contour i).contactTime
      ((T).pairedComplex.contourOriginalVertex (Fcut).selection contour i) = 1 := by
  have bound := K.compatibleMeshRimContour_contactTime_le_one compact nonempty R no_boundary level
    higher M positive inner_disk beta acute W r side i
  have nonzero : ((T).pairedComplex.contourFrontier (Fcut).selection contour i).contactTime
      ((T).pairedComplex.contourOriginalVertex (Fcut).selection contour i) ≠ 0 := by
    intro zero
    exact fresh (((T).pairedComplex.contourFrontier (Fcut).selection contour
      i).contactTime_eq_zero_iff
      ((T).pairedComplex.contourOriginalVertex (Fcut).selection contour i) |>.mp zero)
  omega

/-- Construct the entire nonempty surviving rootward stem in the actual intermediate cut.
Every original fine parent bank and actual boundary successor is derived, with no padding cuts. -/
def compatibleMeshCurrentRootwardChain (i : Fin ((contour).length + 1))
    (fresh : (T).pairedComplex.contourOriginalVertex (Fcut).selection contour i ∉
      ((T).pairedComplex.contourFrontier (Fcut).selection contour i).processed)
    (m : ℕ) (length : (Fcut).parents.distanceToRoot
      ((T).pairedComplex.contourOriginalVertex (Fcut).selection contour i) = m + 2) :
    ((T).pairedComplex.boundarySystem ((T).pairedComplex.processedParentRetain (Fcut).selection
      ((T).pairedComplex.contourFrontier (Fcut).selection contour i))).Chain m :=
  (T).pairedFolding.rootwardParentBankChain_of_boundary_roots (Fcut).selection (Fcut).boundary_roots
    contour (K.compatibleMeshRimContour_starts_root compact nonempty R no_boundary level higher M
      positive inner_disk beta acute W r side) i
    (K.compatibleMeshRimContour_fresh_contactTime compact nonempty R no_boundary level higher M
      positive inner_disk beta acute W r side i fresh) m length

/-- The constructed current stem follows every original parent iterate in its exact order. -/
theorem compatibleMeshCurrentRootwardChain_original (i : Fin ((contour).length + 1))
    (fresh : (T).pairedComplex.contourOriginalVertex (Fcut).selection contour i ∉
      ((T).pairedComplex.contourFrontier (Fcut).selection contour i).processed)
    (m : ℕ) (length : (Fcut).parents.distanceToRoot
      ((T).pairedComplex.contourOriginalVertex (Fcut).selection contour i) = m + 2)
    (k : Fin (m + 1)) :
    (T).pairedComplex.vertexForgetCuts (Set.subset_univ _)
      ((T).pairedComplex.boundaryEndVertex _
        ((K.compatibleMeshCurrentRootwardChain compact nonempty R no_boundary level higher M
          positive
          inner_disk beta acute W r side i fresh m length).point k)) =
      (Fcut).parents.parent^[k.val + 1]
        ((T).pairedComplex.contourOriginalVertex (Fcut).selection contour i) :=
  SpatialFolding.rootwardParentBank_original_of_boundary_roots (Fcut).selection
    (Fcut).boundary_roots
    contour (K.compatibleMeshRimContour_starts_root compact nonempty R no_boundary level higher M
      positive inner_disk beta acute W r side) i
    (K.compatibleMeshRimContour_fresh_contactTime compact nonempty R no_boundary level higher M
      positive inner_disk beta acute W r side i fresh) m length k

/-- The same actual original banks, restored only to their original ancestor-path cut. -/
def compatibleMeshReferenceRootwardChain (i : Fin ((contour).length + 1))
    (fresh : (T).pairedComplex.contourOriginalVertex (Fcut).selection contour i ∉
      ((T).pairedComplex.contourFrontier (Fcut).selection contour i).processed)
    (m : ℕ) (length : (Fcut).parents.distanceToRoot
      ((T).pairedComplex.contourOriginalVertex (Fcut).selection contour i) = m + 2) :
    ((T).pairedComplex.boundarySystem ((T).pairedComplex.ancestorPathRetain (Fcut).selection
      ((Fcut).parents.parent
        ((T).pairedComplex.contourOriginalVertex (Fcut).selection contour i)))).Chain m :=
  (T).pairedFolding.rootwardReferenceBankChain_of_boundary_roots (Fcut).selection
    (Fcut).boundary_roots
    contour (K.compatibleMeshRimContour_starts_root compact nonempty R no_boundary level higher M
      positive inner_disk beta acute W r side) i fresh
    (K.compatibleMeshRimContour_fresh_contactTime compact nonempty R no_boundary level higher M
      positive inner_disk beta acute W r side i fresh) m length

/-- The complete actual current roll agrees point for point with the original path reference,
including every unreduced heading and every original bank length. -/
theorem compatibleMeshReferenceRootwardChain_roll (i : Fin ((contour).length + 1))
    (fresh : (T).pairedComplex.contourOriginalVertex (Fcut).selection contour i ∉
      ((T).pairedComplex.contourFrontier (Fcut).selection contour i).processed)
    (m : ℕ) (length : (Fcut).parents.distanceToRoot
      ((T).pairedComplex.contourOriginalVertex (Fcut).selection contour i) = m + 2) :
    (T).pairedComplex.boundaryChainRoll
      (K.compatibleMeshReferenceRootwardChain compact nonempty R no_boundary level higher M positive
        inner_disk beta acute W r side i fresh m length) =
      (T).pairedComplex.boundaryChainRoll
        (K.compatibleMeshCurrentRootwardChain compact nonempty R no_boundary level higher M positive
          inner_disk beta acute W r side i fresh m length) :=
  (T).pairedFolding.rootwardReferenceBankChain_roll_of_boundary_roots (Fcut).selection
    (Fcut).boundary_roots contour
    (K.compatibleMeshRimContour_starts_root compact nonempty R no_boundary level higher M positive
      inner_disk beta acute W r side) i fresh
    (K.compatibleMeshRimContour_fresh_contactTime compact nonempty R no_boundary level higher M
      positive inner_disk beta acute W r side i fresh) m length

end Unfoldings.ConvexRoof
