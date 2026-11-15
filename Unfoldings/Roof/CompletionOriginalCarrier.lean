module

public import Unfoldings.Roof.CompletionOriginalSubdivision
public import Unfoldings.Roof.SpatialEnvelopeProjection
public import Unfoldings.Roof.ConvexRestriction

/-! The original physical completion patch has its exact footprint and spatial positions. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof.CompletionMesh

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexRoof C} {φ : ℝ} {region : Set Plane}
  (E : K.CompletionMesh φ region K.originalEdgeEquations)

local instance originalMetricIndexFintype : Fintype E.partition.Index :=
  @Fintype.ofFinite _ E.partition.finite

open Classical in
/-- The original auxiliary pieces cover exactly the original physical footprint. -/
theorem original_restrictedCarrier :
    (E.partition.roof E.conforming E.interior_nonempty).restrictedCarrier E.originalPieceSet =
      K.footprint := by
  ext p
  constructor
  · rintro member
    obtain ⟨i, member⟩ := Set.mem_iUnion.mp member
    rw [E.partition.roof_projectedTriangle] at member
    exact K.projectedTriangle_subset_footprint (E.originalParent i)
      (E.originalParent_contains i member)
  · intro member
    rw [K.footprint_eq_union_projectedTriangles] at member
    obtain ⟨f, member⟩ := Set.mem_iUnion.mp member
    obtain ⟨i, _, fine⟩ := E.original_piece_cover f p member
    apply Set.mem_iUnion.mpr
    refine ⟨i, ?_⟩
    rwa [E.partition.roof_projectedTriangle]

open Classical in
/-- The actual original-piece restriction has no collapsed intrinsic copies. -/
theorem original_projection_injective :
    Function.Injective ((E.partition.roof E.conforming E.interior_nonempty).restrictProjection
      E.originalPieceSet) := by
  have selected : E.originalPieceSet.Nonempty := by
    obtain ⟨f⟩ := K.nonempty_face
    obtain ⟨i, _, _⟩ := E.original_piece_cover f ((K.projectedTriangle f).vertex 0)
      ((K.projectedTriangle f).vertex_mem 0)
    exact ⟨i.val, i.property⟩
  apply ConvexRoof.restrictProjection_injective_of_convex _ E.originalPieceSet selected
  rw [E.original_restrictedCarrier]
  exact K.convex_projection

open Classical in
/-- Fine and original tagged points have precisely the same spatial placements. -/
theorem original_parentPoint_spatial (a : E.originalComplex.Total) :
    K.folding.toSpace Set.univ (MetricGluing.point C.Cell (C.glue Set.univ)
      (E.originalSubdivision.parentPoint a)) =
    ((E.partition.pairedFolding.restrictFaces E.originalPieceSet).toSpace Set.univ)
      (MetricGluing.point E.originalComplex.Cell (E.originalComplex.glue Set.univ) a) := by
  rcases a with ⟨i, x⟩
  change K.folding.place (E.originalParent i)
    (E.originalPlace i.val (E.originalParent i) (E.originalParent_contains i) x.val) =
      E.partition.placement i.val x.val
  rw [E.originalPlace_apply]
  exact E.originalCoordinates_spatial i.val (E.originalParent i) (E.originalParent_contains i) _

end Unfoldings.ConvexRoof.CompletionMesh
