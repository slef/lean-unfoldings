module

public import Unfoldings.Roof.CompletionOriginalCopies
public import Unfoldings.Roof.SpatialEnvelopeRetainedClasses
public import Unfoldings.Complex.FaceRestrictionClasses

/-! Regular fine copies agree across original parents away from original cuts. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof.CompletionMesh

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexRoof C} {φ : ℝ} {region : Set Plane}
  (L : K.CompletionMesh φ region K.originalEdgeEquations)

local instance originalRegularIndexFintype : Fintype L.partition.Index :=
  @Fintype.ofFinite _ L.partition.finite

open Classical in
theorem originalPointCopy_eq_away_cuts_of_regular (retain : Set C.Seam)
    {i j : L.originalPieceSet} (p : Plane)
    (first : p ∈ (L.partition.projectedTriangle i.val).carrier)
    (last : p ∈ (L.partition.projectedTriangle j.val).carrier)
    (regular : ¬ (L.partition.projectedTriangle i.val).IsVertex p)
    (outside : p ∉ K.projectedCutSet retain) :
    L.originalPointCopy retain i p first = L.originalPointCopy retain j p last := by
  let x : L.originalComplex.Cell i :=
    ⟨(L.pieceProjection (i.val)).symm p,
      (L.partition.triangle_carrier i.val).symm.subset ⟨p, first, rfl⟩⟩
  let y : L.originalComplex.Cell j :=
    ⟨(L.pieceProjection (j.val)).symm p,
      (L.partition.triangle_carrier j.val).symm.subset ⟨p, last, rfl⟩⟩
  let a : L.originalComplex.Total := ⟨i, x⟩
  let b : L.originalComplex.Total := ⟨j, y⟩
  have first_projection : L.pieceProjection (i.val) x.val = p :=
    (L.pieceProjection (i.val)).apply_symm_apply p
  have last_projection : L.pieceProjection (j.val) y.val = p :=
    (L.pieceProjection (j.val)).apply_symm_apply p
  have raw_regular : ¬ L.originalComplex.IsVertex a := by
    rintro ⟨k, equal⟩
    apply regular
    refine ⟨k, ?_⟩
    apply (L.pieceProjection (i.val)).symm.injective
    exact equal
  have related := L.partition.paired_related_of_projection_eq L.conforming
    (a := L.partition.pairedComplex.includedTotal L.originalPieceSet a)
    (b := L.partition.pairedComplex.includedTotal L.originalPieceSet b)
    (first_projection.trans last_projection.symm)
  have retained := L.partition.related_away_cuts (K.projectedCutSet retain) related
    (first_projection.symm ▸ outside)
  exact (L.originalComplex.faceMap_eq_iff (L.originalRetain retain) i j x y).mpr
    (L.partition.pairedComplex.restrict_eqvGen_of_regular L.originalPieceSet
      (L.partition.retainOutside (K.projectedCutSet retain)) raw_regular retained)

end Unfoldings.ConvexRoof.CompletionMesh
