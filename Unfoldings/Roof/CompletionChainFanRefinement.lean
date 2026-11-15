module

public import Unfoldings.Roof.CompletionOriginalChainRefinement
public import Unfoldings.Roof.CompletionSubdivisionAngles
public import Unfoldings.Complex.BoundaryChainVertices
public import Unfoldings.Complex.ReversedBoundaryChain

/-! Complete actual chain refinements preserve old fans and insert only straight hinges. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof.CompletionMesh

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexRoof C} {φ : ℝ} {region : Set Plane}
  (E : K.CompletionMesh φ region K.originalEdgeEquations)

local instance completionChainFanIndexFintype : Fintype E.partition.Index :=
  @Fintype.ofFinite _ E.partition.finite

open Classical in
/-- Data constructed from the physical completion by `originalChainRefinement`. -/
structure OriginalChainRefinement (retain : Set C.Seam) {n : ℕ}
    (coarse : (C.boundarySystem retain).Chain n) where
  label : Fin (n + 1) → C.DirectedCutBank retain
  named : ∀ i, (label i).start = coarse.point i
  length : ℕ
  chain : (E.originalComplex.boundarySystem (E.originalRetain retain)).Chain length
  first_image : E.originalMetricEquiv retain
    (E.originalComplex.vertexPoint (E.originalRetain retain)
      (E.originalComplex.boundaryEndVertex (E.originalRetain retain) chain.first)) =
        C.vertexPoint retain (C.boundaryEndVertex retain coarse.first)
  last_image : E.originalMetricEquiv retain
    (E.originalComplex.vertexPoint (E.originalRetain retain)
      (E.originalComplex.boundaryEndVertex (E.originalRetain retain)
        (E.originalComplex.boundaryTurn (E.originalRetain retain) chain.last))) =
          C.vertexPoint retain (C.boundaryEndVertex retain (C.boundaryTurn retain coarse.last))
  covered : ∀ p : E.originalComplex.BoundaryEnd (E.originalRetain retain),
    (∃ j, chain.point j = p) ↔ ∃ i : Fin (n + 1), ∃ j,
      (E.originalBankBlock retain (label i).seam
        (label i).side (label i).flag).chain.point j = p

open Classical in
/-- Construct a complete fine chain from an actual original cut-bank chain. -/
def originalChainRefinement (retain : Set C.Seam) {n : ℕ}
    (coarse : (C.boundarySystem retain).Chain n)
    (cut : ∀ i, ¬ C.IsBoundaryEdge Set.univ (C.germEdge (coarse.point i).val)) :
    E.OriginalChainRefinement retain coarse :=
  Classical.choice (by
    obtain ⟨label, named, m, fine, first, last, covered⟩ :=
      E.exists_original_chain_refinement retain coarse cut
    exact ⟨⟨label, named, m, fine, first, last, covered⟩⟩)

namespace OriginalChainRefinement

variable {E} {retain : Set C.Seam} {n : ℕ} {coarse : (C.boundarySystem retain).Chain n}
  (R : E.OriginalChainRefinement retain coarse)

open Classical in
/-- The canonical directed physical block belonging to an old bank. -/
def block (i : Fin (n + 1)) :=
  E.originalBankBlock retain (R.label i).seam (R.label i).side (R.label i).flag

open Classical in
/-- Every old starting vertex is present in the fine path with its exact intrinsic copy. -/
theorem exists_vertex_index (i : Fin (n + 1)) :
    ∃ j : Fin (R.length + 1),
      E.originalMetricEquiv retain
        (E.originalComplex.vertexPoint (E.originalRetain retain)
          (E.originalComplex.boundaryEndVertex (E.originalRetain retain) (R.chain.point j))) =
            C.vertexPoint retain (C.boundaryEndVertex retain (coarse.point i)) := by
  obtain ⟨j, same⟩ := (R.covered (R.block i).chain.first).mpr ⟨i, 0, rfl⟩
  refine ⟨j, ?_⟩
  rw [same, (R.block i).first_image]
  change C.vertexPoint retain (C.boundaryEndVertex retain (R.label i).start) = _
  rw [R.named]

open Classical in
/-- Locate each old starting cut-vertex copy in the actual fine chain. -/
def coarseIndex (i : Fin (n + 1)) : Fin (R.length + 1) :=
  (R.exists_vertex_index i).choose

open Classical in
/-- The fine index is characterized by its metric image, including the cut-side copy. -/
theorem coarseIndex_image (i : Fin (n + 1)) :
    E.originalMetricEquiv retain
      (E.originalComplex.vertexPoint (E.originalRetain retain)
        (E.originalComplex.boundaryEndVertex (E.originalRetain retain)
          (R.chain.point (R.coarseIndex i)))) =
            C.vertexPoint retain (C.boundaryEndVertex retain (coarse.point i)) :=
  (R.exists_vertex_index i).choose_spec

open Classical in
/-- Metric images determine unique indices along this actual path. -/
theorem index_eq_of_image {i j : Fin (R.length + 1)}
    (same : E.originalMetricEquiv retain
      (E.originalComplex.vertexPoint (E.originalRetain retain)
        (E.originalComplex.boundaryEndVertex (E.originalRetain retain) (R.chain.point i))) =
      E.originalMetricEquiv retain
        (E.originalComplex.vertexPoint (E.originalRetain retain)
          (E.originalComplex.boundaryEndVertex (E.originalRetain retain) (R.chain.point j)))) :
    i = j :=
  E.originalComplex.boundaryChain_vertices_injective (E.originalRetain retain) R.chain
    (E.originalComplex.vertexPoint_injective _ ((E.originalMetricEquiv retain).injective same))

open Classical in
/-- Old hinges have different fine indices, even for overlapping planar developments. -/
theorem coarseIndex_injective : Function.Injective R.coarseIndex := by
  intro i j equal
  apply C.boundaryChain_vertices_injective retain coarse
  apply C.vertexPoint_injective retain
  rw [← R.coarseIndex_image i, ← R.coarseIndex_image j, equal]

open Classical in
@[simp] theorem coarseIndex_zero : R.coarseIndex 0 = 0 := by
  apply R.index_eq_of_image
  exact (R.coarseIndex_image 0).trans R.first_image.symm

open Classical in
/-- The fine copy has the full actual old one-sided intrinsic fan angle. -/
theorem coarseIndex_totalAngle (i : Fin (n + 1)) :
    E.originalComplex.totalAngle (E.originalRetain retain)
      (E.originalComplex.boundaryEndVertex (E.originalRetain retain)
        (R.chain.point (R.coarseIndex i))) =
      C.totalAngle retain (C.boundaryEndVertex retain (coarse.point i)) :=
  E.original_totalAngle_eq retain _ _ (R.coarseIndex_image i)

open Classical in
/-- Every inserted hinge is straight; only actual old hinges can turn the fine roll. -/
theorem totalAngle_eq_pi_of_new (j : Fin (R.length + 1))
    (new : ∀ i, R.coarseIndex i ≠ j) :
    E.originalComplex.totalAngle (E.originalRetain retain)
      (E.originalComplex.boundaryEndVertex (E.originalRetain retain) (R.chain.point j)) =
        Real.pi := by
  obtain ⟨i, k, same⟩ := (R.covered (R.chain.point j)).mp ⟨j, rfl⟩
  revert same
  refine Fin.cases ?_ (fun k same => ?_) k
  · intro same
    have image := (R.block i).first_image
    change _ = C.vertexPoint retain (C.boundaryEndVertex retain (R.label i).start) at image
    rw [R.named] at image
    have at_i : R.coarseIndex i = j := by
      apply R.index_eq_of_image
      rw [R.coarseIndex_image, ← same]
      exact image.symm
    exact (new i at_i).elim
  · rw [← same]
    exact E.originalComplex.boundaryChain_internal_angle_of_zero_heading
      (R.block i).chain (R.block i).zero_heading k

end OriginalChainRefinement
end Unfoldings.ConvexRoof.CompletionMesh
