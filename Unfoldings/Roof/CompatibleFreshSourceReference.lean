module

public import Unfoldings.Roof.CompatibleFreshSourceBank
public import Unfoldings.Complex.CompleteSourceReference

/-! Actual source-bank references preserve all original banks and their real rolling data. -/

@[expose] public section

noncomputable section

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

local instance compatibleFreshSourceReferenceIndexFintype : Fintype (T).Index :=
  @Fintype.ofFinite _ (T).finite

include beta acute

local notation "SourceAt[" q "," i "]" => TriangleComplex.contourOriginalVertex
  (SpatialEnvelope.Triangulation.pairedComplex
    (SpatialEnvelope.ConstrainedTriangulation.toTriangulation T))
  (PotentialCutForest.selection Fcut) q i
local notation "RetainAt[" q "," i "]" => TriangleComplex.processedParentRetain
  (SpatialEnvelope.Triangulation.pairedComplex
    (SpatialEnvelope.ConstrainedTriangulation.toTriangulation T))
  (PotentialCutForest.selection Fcut)
  (TriangleComplex.contourFrontier
    (SpatialEnvelope.Triangulation.pairedComplex
      (SpatialEnvelope.ConstrainedTriangulation.toTriangulation T))
    (PotentialCutForest.selection Fcut) q i)

local notation "ChainAt[" q "," h "," i "," hf "," n "," hn "]" =>
  K.compatibleMeshFreshSourceBankChain compact nonempty R no_boundary level higher M positive
    inner_disk beta acute q h i hf n hn

/-- Restore exactly the side branches outside the actual source's full parent path. -/
def compatibleMeshFreshSourceReferenceChain
    (contour : (T).pairedComplex.BoundaryContour
      ((T).pairedComplex.selectedRetain (Fcut).selection))
    (starts : (T).pairedComplex.contourOriginalVertex (Fcut).selection contour 0 ∈
      (Fcut).parents.roots)
    (j : Fin contour.length)
    (fresh : (T).pairedComplex.contourOriginalVertex (Fcut).selection contour j.castSucc ∉
      ((T).pairedComplex.contourFrontier (Fcut).selection contour j.castSucc).processed)
    (m : ℕ)
    (span : (Fcut).parents.distanceToRoot
      ((T).pairedComplex.contourOriginalVertex (Fcut).selection contour j.castSucc) = m + 1) :
    ((T).pairedComplex.boundarySystem
      ((T).pairedComplex.ancestorPathRetain (Fcut).selection
        SourceAt[contour,j.castSucc])).Chain m :=
  (T).pairedComplex.completeSourceReference (Fcut).selection (Fcut).boundary_roots
    ((T).pairedComplex.contourFrontier (Fcut).selection contour j.succ)
    ChainAt[contour,starts,j,fresh,m,span] SourceAt[contour,j.castSucc] span
    (K.compatibleMeshFreshSourceBankChain_original compact nonempty R no_boundary level higher M
      positive inner_disk beta acute contour starts j fresh m span)
    (K.compatibleMeshFreshSourceBankChain_terminal_original compact nonempty R no_boundary level
      higher M positive inner_disk beta acute contour starts j fresh m span)
    ((T).pairedComplex.previous_contour_vertex_processed (Fcut).selection contour j)

local notation "ReferenceAt[" q "," h "," i "," hf "," n "," hn "]" =>
  K.compatibleMeshFreshSourceReferenceChain compact nonempty R no_boundary level higher M positive
    inner_disk beta acute q h i hf n hn

/-- The source-inclusive reference keeps the entire actual normalized roll, edge for edge. -/
theorem compatibleMeshFreshSourceReferenceChain_roll
    (contour : (T).pairedComplex.BoundaryContour
      ((T).pairedComplex.selectedRetain (Fcut).selection))
    (starts : (T).pairedComplex.contourOriginalVertex (Fcut).selection contour 0 ∈
      (Fcut).parents.roots)
    (j : Fin contour.length)
    (fresh : (T).pairedComplex.contourOriginalVertex (Fcut).selection contour j.castSucc ∉
      ((T).pairedComplex.contourFrontier (Fcut).selection contour j.castSucc).processed)
    (m : ℕ)
    (span : (Fcut).parents.distanceToRoot
      ((T).pairedComplex.contourOriginalVertex (Fcut).selection contour j.castSucc) = m + 1) :
    (T).pairedComplex.boundaryChainRoll ReferenceAt[contour,starts,j,fresh,m,span] =
      (T).pairedComplex.boundaryChainRoll ChainAt[contour,starts,j,fresh,m,span] :=
  (T).pairedComplex.completeSourceReference_roll _ _ _ _ _ _ _ _ _

/-- The exact original real heading prefixes survive, without reducing modulo a full turn. -/
theorem compatibleMeshFreshSourceReferenceChain_heading
    (contour : (T).pairedComplex.BoundaryContour
      ((T).pairedComplex.selectedRetain (Fcut).selection))
    (starts : (T).pairedComplex.contourOriginalVertex (Fcut).selection contour 0 ∈
      (Fcut).parents.roots)
    (j : Fin contour.length)
    (fresh : (T).pairedComplex.contourOriginalVertex (Fcut).selection contour j.castSucc ∉
      ((T).pairedComplex.contourFrontier (Fcut).selection contour j.castSucc).processed)
    (m : ℕ)
    (span : (Fcut).parents.distanceToRoot
      ((T).pairedComplex.contourOriginalVertex (Fcut).selection contour j.castSucc) = m + 1)
    (k : Fin (m + 1)) :
    (T).pairedComplex.boundaryChainRollHeading ReferenceAt[contour,starts,j,fresh,m,span] k =
      (T).pairedComplex.boundaryChainRollHeading ChainAt[contour,starts,j,fresh,m,span] k :=
  (T).pairedComplex.completeSourceReference_heading _ _ _ _ _ _ _ _ _ k

end Unfoldings.ConvexRoof
