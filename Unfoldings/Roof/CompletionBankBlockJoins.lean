module

public import Unfoldings.Roof.CompletionBankDistinctness
public import Unfoldings.Roof.CompletionBankRolling

/-! Derive actual fine-bank separation and joins from the original cut labels and corners. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof.CompletionMesh

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexRoof C} {φ : ℝ} {region : Set Plane}
  (E : K.CompletionMesh φ region K.originalEdgeEquations)

local instance completionBlockJoinIndexFintype : Fintype E.partition.Index :=
  @Fintype.ofFinite _ E.partition.finite

open Classical in
/-- Distinct original cut banks give disjoint actual fine block labels in both orientations. -/
theorem original_bank_blocks_separated (retain : Set C.Seam)
    (s t : C.CutSeam retain) (side other : Bool)
    (different : C.cutBank retain s side ≠ C.cutBank retain t other)
    (a : E.faceSidePieces (C.seamSide s.val side).face (C.seamSide s.val side).edge)
    (b : E.faceSidePieces (C.seamSide t.val other).face (C.seamSide t.val other).edge)
    (p q : E.originalComplex.BoundaryEnd (E.originalRetain retain))
    (first : (E.originalComplex.boundaryEndEquiv (E.originalRetain retain) p).1 =
      E.subdividedCutBank retain s side a)
    (last : (E.originalComplex.boundaryEndEquiv (E.originalRetain retain) q).1 =
      E.subdividedCutBank retain t other b) :
    p ≠ q ∧ p ≠ E.originalComplex.boundaryTurn (E.originalRetain retain) q := by
  let D := E.originalComplex
  let kept := E.originalRetain retain
  have banks : (D.boundaryEndEquiv kept p).1 ≠ (D.boundaryEndEquiv kept q).1 := by
    rw [first, last]
    exact fun same => different (E.original_cutBank_eq_of_subdivided_eq retain s t side other
      a b same)
  constructor
  · intro same
    exact banks (congrArg (fun p : D.BoundaryEnd kept => (D.boundaryEndEquiv kept p).1) same)
  · intro same
    have equal := congrArg (fun p : D.BoundaryEnd kept => (D.boundaryEndEquiv kept p).1) same
    exact banks (by
      simpa only [D, kept, TriangleComplex.boundaryTurn, Equiv.apply_symm_apply] using! equal)

open Classical in
/-- Matching old cut-corner classes derive the actual fine boundary successor. Parent
faces and endpoint coordinates determine the metric copies internally; no fine vertex
or fan correspondence is supplied. -/
theorem original_boundaryMate_eq_of_matching_corners (retain : Set C.Seam)
    (p q : E.originalComplex.BoundaryEnd (E.originalRetain retain)) (f g : Face) (i j : Fin 3)
    (parent_p : E.originalParent p.val.1.1 = f)
    (position_p : E.originalBankEndProjection p = (K.projectedTriangle f).vertex i)
    (parent_q : E.originalParent q.val.1.1 = g)
    (position_q : E.originalBankEndProjection q = (K.projectedTriangle g).vertex j)
    (same : C.vertexOfCorner retain (f, i) = C.vertexOfCorner retain (g, j))
    (different : p ≠ q) : E.originalComplex.boundaryMate (E.originalRetain retain) p = q := by
  let D := E.originalComplex
  let kept := E.originalRetain retain
  have vertices : D.boundaryEndVertex kept q = D.boundaryEndVertex kept p := by
    apply D.vertexPoint_injective kept
    apply (E.originalMetricEquiv retain).injective
    rw [E.originalMetricEquiv_boundaryEnd_at_corner retain q g j parent_q position_q,
      E.originalMetricEquiv_boundaryEnd_at_corner retain p f i parent_p position_p, same]
  exact ((D.exists_unique_other_boundaryEnd kept p).unique ⟨different.symm, vertices⟩
    (D.boundaryMate_spec kept p)).symm

end Unfoldings.ConvexRoof.CompletionMesh
