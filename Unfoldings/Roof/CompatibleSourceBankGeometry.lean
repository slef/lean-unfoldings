module

public import Unfoldings.Roof.CompatibleMeshPaths
public import Unfoldings.Roof.PotentialContourHistory
public import Unfoldings.Roof.SpatialEnvelopeBoundaryChains
public import Unfoldings.Polyhedron.ProjectedBoundaryChain
public import Unfoldings.Complex.FreshSourceBankChain

/-! Complete source-inclusive banks have their actual compatible histories and interior starts. -/

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

local instance compatibleSourceBankIndexFintype : Fintype (T).Index :=
  @Fintype.ofFinite _ (T).finite

include beta acute

/-- All actual physical vertices, including both true endpoints, are the complete parent history. -/
theorem compatibleSourceBankChain_eq_history
    {retain : Set (T).pairedComplex.Seam} {m : ℕ}
  (chain : ((T).pairedComplex.boundarySystem retain).Chain m)
  (source : (T).pairedComplex.Vertex Set.univ)
  (span : (Fcut).parents.distanceToRoot source = m + 1)
  (labels : ∀ k : Fin (m + 1), (T).pairedComplex.vertexForgetCuts (Set.subset_univ _)
    ((T).pairedComplex.boundaryEndVertex _ (chain.point k)) =
      (Fcut).parents.parent^[k.val] source)
  (terminal : (T).pairedComplex.vertexForgetCuts (Set.subset_univ _)
    ((T).pairedComplex.boundaryEndVertex _ ((T).pairedComplex.boundaryTurn _ chain.last)) =
      (Fcut).parents.root source) :
    (T).pairedFolding.projectedBoundaryChain chain =
      K.compatibleMeshHistory compact nonempty R no_boundary level higher M positive
        inner_disk beta acute source (m + 1) := by
  apply congrArg PolygonalChain.mk
  funext j
  refine Fin.lastCases ?_ (fun k => ?_) j
  · have far := ((T).toTriangulation.projectedBoundaryChain_vertex_succ chain conforming inside
      (Fin.last m)).trans (congrArg (Q).projectedVertex terminal)
    have reaches := (Fcut).parents.iterate_distanceToRoot_eq_root source
    rw [span] at reaches
    simpa only [Fin.succ_last, compatibleMeshHistory, Fin.val_last, reaches,
      SpatialEnvelope.Triangulation.projectedBoundaryChain, PolygonalChain.affineMap] using far
  · exact ((T).toTriangulation.projectedBoundaryChain_vertex_castSucc
      chain conforming inside k).trans (congrArg (Q).projectedVertex (labels k))

/-- The complete actual source bank follows the original routing, with no step witness supplied. -/
theorem compatibleSourceBankChain_follows
    {retain : Set (T).pairedComplex.Seam} {m : ℕ}
  (chain : ((T).pairedComplex.boundarySystem retain).Chain m)
  (source : (T).pairedComplex.Vertex Set.univ)
  (span : (Fcut).parents.distanceToRoot source = m + 1)
  (labels : ∀ k : Fin (m + 1), (T).pairedComplex.vertexForgetCuts (Set.subset_univ _)
    ((T).pairedComplex.boundaryEndVertex _ (chain.point k)) =
      (Fcut).parents.parent^[k.val] source)
  (terminal : (T).pairedComplex.vertexForgetCuts (Set.subset_univ _)
    ((T).pairedComplex.boundaryEndVertex _ ((T).pairedComplex.boundaryTurn _ chain.last)) =
      (Fcut).parents.root source) :
    R.Follows ((T).pairedFolding.projectedBoundaryChain chain) := by
  rw [K.compatibleSourceBankChain_eq_history compact nonempty R no_boundary level higher M
    positive inner_disk beta acute chain source span labels terminal]
  exact K.compatibleMeshHistory_follows compact nonempty R no_boundary level higher M positive
    inner_disk beta acute source (m + 1) span.ge

/-- Every actual parent-bank start lies strictly inside the roof; only its final endpoint is rim. -/
theorem compatibleSourceBankChain_starts_interior
    {retain : Set (T).pairedComplex.Seam} {m : ℕ}
  (chain : ((T).pairedComplex.boundarySystem retain).Chain m)
  (source : (T).pairedComplex.Vertex Set.univ)
  (span : (Fcut).parents.distanceToRoot source = m + 1)
  (labels : ∀ k : Fin (m + 1), (T).pairedComplex.vertexForgetCuts (Set.subset_univ _)
    ((T).pairedComplex.boundaryEndVertex _ (chain.point k)) =
      (Fcut).parents.parent^[k.val] source)
    (k : Fin (m + 1)) :
    Cap.horizontal ((T).pairedFolding.boundaryPosition (chain.point k)) ∈
      interior (SpatialEnvelope.clip M.plane (-level)) := by
  have nonroot := (Fcut).parents.iterate_lt_distanceToRoot_not_mem source
    (show k.val < (Fcut).parents.distanceToRoot source by rw [span]; exact k.isLt)
  have not_boundary : ¬ (T).pairedComplex.IsBoundaryVertex Set.univ
      ((Fcut).parents.parent^[k.val] source) := fun boundary =>
    nonroot ((Fcut).boundary_roots boundary)
  have member := ((Q).projectedVertex_mem_interior_iff _).mpr not_boundary
  rw [(T).toTriangulation.roof_footprint conforming inside] at member
  have position := ((T).toTriangulation.projectedBoundaryChain_vertex_castSucc chain conforming
    inside k).trans (congrArg (Q).projectedVertex (labels k))
  change ((T).pairedFolding.projectedBoundaryChain chain).vertex k.castSucc = _ at position
  rw [(T).pairedFolding.projectedBoundaryChain_vertex_castSucc] at position
  exact position.symm ▸ member

end Unfoldings.ConvexRoof
