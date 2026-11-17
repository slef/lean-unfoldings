module

public import Unfoldings.Roof.CompletionChainSpatialParameters
public import Unfoldings.Roof.CompletionChainRadial
public import Unfoldings.Polyhedron.DirectedBankSubinterval
public import Unfoldings.Cap.ProjectedBoundaryChainFolding

/-! Physical cap bank subdivisions preserve exact projected parameters and radial geometry. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof.CompletionMesh.OriginalChainRefinement

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexRoof C} {φ : ℝ} {region : Set Plane}
  {E : K.CompletionMesh φ region K.originalEdgeEquations}

local instance completionProjectedParametersIndexFintype : Fintype E.partition.Index :=
  @Fintype.ofFinite _ E.partition.finite

variable {retain : Set C.Seam} {n : ℕ} {coarse : (C.boundarySystem retain).Chain n}
  (R : E.OriginalChainRefinement retain coarse)

local notation "F" => E.partition.pairedFolding.restrictFaces E.originalPieceSet

open Classical in
/-- Each entire spatial fine bank is its exact forward original-bank restriction. -/
theorem block_spatial_point (i : Fin (n + 1)) (k : Fin ((R.block i).length + 1))
    (t : unitInterval) :
    (R.blockSpatialChain i).point k t = K.folding.toSpace retain
      (C.directedBoundaryPath (coarse.point i) (R.pieceParameter i k t)) := by
  rw [PolygonalChain.point, R.block_spatial_vertex_parameter, R.block_spatial_vertex_parameter,
    K.folding.directedBoundaryPath_lineMap, K.folding.directedBoundaryPath_lineMap,
    K.folding.directedBoundaryPath_lineMap]
  exact ((AffineMap.lineMap (K.folding.boundaryPosition (coarse.point i))
    (K.folding.boundaryPosition (C.boundaryTurn retain (coarse.point i)))).apply_lineMap
      _ _ _).symm

open Classical in
/-- Every complete fine projected bank uses the same ordered original arclength parameter. -/
theorem block_projected_point (i : Fin (n + 1)) (k : Fin ((R.block i).length + 1))
    (t : unitInterval) :
    ((F).projectedBoundaryChain R.chain).point (R.blockIndex i k) t =
      (K.folding.projectedBoundaryChain coarse).point i (R.pieceParameter i k t) := by
  calc
    _ = Cap.horizontal ((F).toSpace (E.originalRetain retain)
        (E.originalComplex.directedBoundaryPath (R.chain.point (R.blockIndex i k)) t)) :=
      (F).projectedBoundaryChain_point R.chain (R.blockIndex i k) t
    _ = Cap.horizontal ((F).toSpace (E.originalRetain retain)
        (E.originalComplex.directedBoundaryPath ((R.block i).chain.point k) t)) :=
      congrArg (fun p => Cap.horizontal ((F).toSpace (E.originalRetain retain)
        (E.originalComplex.directedBoundaryPath p t))) (R.blockIndex_point i k)
    _ = Cap.horizontal ((R.blockSpatialChain i).point k t) :=
      congrArg Cap.horizontal ((F).boundarySpatialChain_point (R.block i).chain k t).symm
    _ = Cap.horizontal (K.folding.toSpace retain
        (C.directedBoundaryPath (coarse.point i) (R.pieceParameter i k t))) :=
      congrArg Cap.horizontal (R.block_spatial_point i k t)
    _ = _ := (K.folding.projectedBoundaryChain_point coarse i (R.pieceParameter i k t)).symm

open Classical in
/-- Actual physical refinement preserves radial order in the original horizontal plane. -/
theorem projected_radialFrom (source : Plane)
    (radial : (K.folding.projectedBoundaryChain coarse).RadialFrom source 0) :
    ((F).projectedBoundaryChain R.chain).RadialFrom source 0 := by
  intro j _ t s ordered
  obtain ⟨i, k, at_j⟩ := R.blockIndex_coverage j
  dsimp only
  rw [← at_j, R.block_projected_point, R.block_projected_point]
  exact radial i (Nat.zero_le _) (R.pieceParameter_monotone i k ordered)

open Classical in
/-- The comparison cap's own projected bank is this very physical chain. -/
theorem cap_projectedBoundaryChain_eq :
    E.cap.projectedBoundaryChain E.originalPieceSet R.chain =
      (F).projectedBoundaryChain R.chain := by
  have positions (p : E.originalComplex.BoundaryEnd (E.originalRetain retain)) :
      Cap.horizontal ((E.cap.folding.restrictFaces E.originalPieceSet).boundaryPosition p) =
        Cap.horizontal ((F).boundaryPosition p) := by
    change Cap.horizontal (E.partition.placement p.val.1.1.val
        ((E.originalComplex.triangle p.val.1.1).vertex p.val.1.2) +
          Cap.horizontalAtHeight 0 (-E.level)) = _
    exact ConvexRoof.horizontal_add_level _ _
  apply congrArg PolygonalChain.mk
  funext j
  refine Fin.lastCases ?_ (fun i => ?_) j
  · exact (E.cap.projectedBoundaryChain_vertex_last E.originalPieceSet R.chain).trans
      ((positions _).trans ((F).projectedBoundaryChain_vertex_last R.chain).symm)
  · exact (E.cap.projectedBoundaryChain_vertex_castSucc E.originalPieceSet R.chain i).trans
      ((positions _).trans ((F).projectedBoundaryChain_vertex_castSucc R.chain i).symm)

open Classical in
/-- The actual cap chain used by the rolling estimate inherits original radial geometry. -/
theorem cap_projected_radialFrom (source : Plane)
    (radial : (K.folding.projectedBoundaryChain coarse).RadialFrom source 0) :
    (E.cap.projectedBoundaryChain E.originalPieceSet R.chain).RadialFrom source 0 := by
  rw [R.cap_projectedBoundaryChain_eq]
  exact R.projected_radialFrom source radial

end Unfoldings.ConvexRoof.CompletionMesh.OriginalChainRefinement
