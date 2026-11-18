module

public import Unfoldings.Roof.CompletionProjectedChainHeading
public import Unfoldings.Cap.OriginalBankHeadingComparison

/-! The comparison cap and original physical projected metric have the same real bank headings. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof.CompletionMesh

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexRoof C} {φ : ℝ} {region : Set Plane}
  (E : K.CompletionMesh φ region K.originalEdgeEquations)

local instance completionProjectedCapHeadingIndexFintype : Fintype E.partition.Index :=
  @Fintype.ofFinite _ E.partition.finite

open Classical in
theorem cap_originalProjectedTriangle (g : E.originalPieceSet) :
    E.cap.projectedTriangle g.val =
      E.originalComplex.affineProjectedTriangle E.originalProjection g := by
  apply Triangle.eq_of_vertex_eq
  intro i
  change Cap.horizontal (E.partition.placement g.val
      ((E.originalComplex.triangle g).vertex i) + Cap.horizontalAtHeight 0 (-E.level)) =
    E.originalProjection g ((E.originalComplex.triangle g).vertex i)
  exact (ConvexRoof.horizontal_add_level _ _).trans
    (((K.completionPlanes E.tentHeight (Real.sin φ / 2))
      (E.partition.support g.val)).horizontal_place _)

open Classical in
/-- Vertical cap normalization leaves every actual unreduced projected heading unchanged. -/
theorem cap_projectedFanRollHeading_eq {retain : Set C.Seam} {n : ℕ}
    (chain : (E.originalComplex.boundarySystem (E.originalRetain retain)).Chain n)
    (i : Fin (n + 1)) :
    E.cap.projectedFanRollHeading E.originalPieceSet chain i =
      E.originalProjectedComplex.boundaryChainRollHeading
        (E.originalComplex.affineProjectionChain E.originalProjection
          E.originalProjection_joined chain) i := by
  refine Eq.trans ?_ (E.originalComplex.affineProjectionChain_heading
    E.originalProjection E.originalProjection_joined chain i).symm
  apply congrArg (fun turn : Fin n → ℝ => Fin.partialSum turn i)
  funext j
  apply congrArg (fun a : ℝ => Real.pi - a)
  unfold ConvexCap.projectedCutFanAngle
  apply Finset.sum_congr rfl
  intro d _
  rw [E.cap_originalProjectedTriangle d.1]
  rfl

end Unfoldings.ConvexRoof.CompletionMesh
