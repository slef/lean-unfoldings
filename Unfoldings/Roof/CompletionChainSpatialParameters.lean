module

public import Unfoldings.Roof.CompletionChainRollTrace
public import Unfoldings.Roof.CompletionOriginalSpatial
public import Unfoldings.Polyhedron.BoundaryChainGeometry
public import Unfoldings.Polyhedron.BankLengths
public import Unfoldings.Geometry.ShortestPolygonalChain

/-! Exact original arclength parameters of every spatial physical bank refinement. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof.CompletionMesh.OriginalChainRefinement

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexRoof C} {φ : ℝ} {region : Set Plane}
  {E : K.CompletionMesh φ region K.originalEdgeEquations}

local instance completionSpatialParametersIndexFintype : Fintype E.partition.Index :=
  @Fintype.ofFinite _ E.partition.finite

variable {retain : Set C.Seam} {n : ℕ} {coarse : (C.boundarySystem retain).Chain n}
  (R : E.OriginalChainRefinement retain coarse)

local notation "F" => E.partition.pairedFolding.restrictFaces E.originalPieceSet
open Classical in
/-- The actual folded spatial chain of one complete original bank block. -/
def blockSpatialChain (i : Fin (n + 1)) : PolygonalChain Space ((R.block i).length + 1) :=
  (F).boundarySpatialChain (R.block i).chain

open Classical in
/-- The actual physical block starts at the full original spatial bank endpoint. -/
theorem block_spatial_first (i : Fin (n + 1)) :
    (R.blockSpatialChain i).vertex 0 = K.folding.boundaryPosition (coarse.point i) := by
  have first := (R.block i).first_image
  change _ = C.vertexPoint retain (C.boundaryEndVertex retain (R.label i).start) at first
  rw [R.named] at first
  exact ((F).boundarySpatialChain_vertex_castSucc (R.block i).chain 0).trans
    ((E.originalMetricEquiv_toSpace retain _).trans
      (congrArg (K.folding.toSpace retain) first))

open Classical in
/-- The true final physical block endpoint is the original bank's full spatial endpoint. -/
theorem block_spatial_last (i : Fin (n + 1)) :
    (R.blockSpatialChain i).vertex (Fin.last ((R.block i).length + 1)) =
      K.folding.boundaryPosition (C.boundaryTurn retain (coarse.point i)) := by
  have last := (R.block i).last_image
  change _ = C.vertexPoint retain (C.vertexOfCorner retain (R.label i).finishCorner) at last
  rw [← (R.label i).finish_vertex, R.named] at last
  exact ((F).boundarySpatialChain_vertex_last (R.block i).chain).trans
    ((E.originalMetricEquiv_toSpace retain _).trans
      (congrArg (K.folding.toSpace retain) last))

open Classical in
/-- A physical spatial edge has exactly its actual intrinsic fine-bank length. -/
theorem block_spatial_edge_length (i : Fin (n + 1)) (k : Fin ((R.block i).length + 1)) :
    ‖(R.blockSpatialChain i).edge k‖ = R.blockLengths i k :=
  (congrArg norm ((F).boundarySpatialChain_edge (R.block i).chain k)).trans
    ((F).boundaryBankLength_eq_germDirection_norm ((R.block i).chain.point k)).symm

open Classical in
/-- A physical original bank attains its straight spatial chord length exactly. -/
theorem block_spatial_length (i : Fin (n + 1)) :
    (R.blockSpatialChain i).projectedLength = C.boundaryBankLength (coarse.point i) := by
  simp only [PolygonalChain.projectedLength, R.block_spatial_edge_length]
  exact R.block_sum_lengths i

open Classical in
/-- The actual whole physical block is Euclidean shortest, retaining its direction. -/
theorem block_spatial_shortest (i : Fin (n + 1)) :
    (R.blockSpatialChain i).projectedLength =
      ‖(R.blockSpatialChain i).vertex (Fin.last ((R.block i).length + 1)) -
        (R.blockSpatialChain i).vertex 0‖ := by
  rw [R.block_spatial_length, R.block_spatial_first, R.block_spatial_last,
    ← K.folding.germDirection_boundary_positions,
    ← K.folding.boundaryBankLength_eq_germDirection_norm]

open Classical in
/-- Every original or inserted physical vertex keeps its exact old arclength parameter. -/
theorem block_spatial_vertex_parameter (i : Fin (n + 1)) (k : Fin ((R.block i).length + 2)) :
    (R.blockSpatialChain i).vertex k = K.folding.toSpace retain
      (C.directedBoundaryPath (coarse.point i) (R.blockParameter i k)) := by
  have chord : (R.blockSpatialChain i).vertex (Fin.last ((R.block i).length + 1)) ≠
      (R.blockSpatialChain i).vertex 0 := by
    intro same
    have length := R.block_spatial_shortest i
    rw [same, sub_self, norm_zero, R.block_spatial_length] at length
    exact (C.boundaryBankLength_pos _).ne' length
  have vertex := (R.blockSpatialChain i).vertex_eq_chord_arclength_of_length_eq chord
    (R.block_spatial_shortest i) k
  have norm_chord := (R.block_spatial_shortest i).symm.trans (R.block_spatial_length i)
  rw [norm_chord, R.block_spatial_first, R.block_spatial_last,
    ← K.folding.germDirection_boundary_positions] at vertex
  rw [K.folding.directedBoundaryPath_position]
  convert vertex using 1
  simp only [blockParameter, R.block_spatial_edge_length]

end Unfoldings.ConvexRoof.CompletionMesh.OriginalChainRefinement
