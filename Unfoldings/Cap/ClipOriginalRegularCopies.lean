module

public import Unfoldings.Cap.ClipOriginalCopies
public import Unfoldings.Cap.ClipRetainedClasses
public import Unfoldings.Complex.FaceRestrictionClasses

/-! Regular fine copies agree across original parents away from original cuts. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap.LineAlignedClip

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexCap C} {Z : ℝ} (L : K.LineAlignedClip Z K.originalEdgeEquations)

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
    ⟨(K.projectFaceEquiv (L.partition.face i.val)).symm p,
      (L.partition.triangle_carrier i.val).symm.subset ⟨p, first, rfl⟩⟩
  let y : L.originalComplex.Cell j :=
    ⟨(K.projectFaceEquiv (L.partition.face j.val)).symm p,
      (L.partition.triangle_carrier j.val).symm.subset ⟨p, last, rfl⟩⟩
  let a : L.originalComplex.Total := ⟨i, x⟩
  let b : L.originalComplex.Total := ⟨j, y⟩
  have first_projection : K.projectFace (L.partition.face i.val) x.val = p :=
    (K.projectFaceEquiv (L.partition.face i.val)).apply_symm_apply p
  have last_projection : K.projectFace (L.partition.face j.val) y.val = p :=
    (K.projectFaceEquiv (L.partition.face j.val)).apply_symm_apply p
  have raw_regular : ¬ L.originalComplex.IsVertex a := by
    rintro ⟨k, equal⟩
    apply regular
    refine ⟨k, ?_⟩
    apply (K.projectFaceEquiv (L.partition.face i.val)).symm.injective
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

end Unfoldings.ConvexCap.LineAlignedClip
