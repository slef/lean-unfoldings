module

public import Unfoldings.Roof.CompletionBankBlocks
public import Unfoldings.Geometry.OrderedSegmentLength
public import Unfoldings.Complex.BoundaryBankLength

/-! Every physical bank subdivision preserves its entire original intrinsic length. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof.CompletionMesh

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexRoof C} {φ : ℝ} {region : Set Plane}
  (E : K.CompletionMesh φ region K.originalEdgeEquations)

local instance completionBankLengthIndexFintype : Fintype E.partition.Index :=
  @Fintype.ofFinite _ E.partition.finite

open Classical in
/-- Count every genuine physical fine edge in an old side exactly once, using intrinsic lengths. -/
theorem sum_faceSidePieces_lengths (f : Face) (e : Fin 3) :
    (∑ a : E.faceSidePieces f e,
      dist ((E.partition.triangle a.val.1.val).vertex a.val.2)
        ((E.partition.triangle a.val.1.val).vertex (Triangle.next a.val.2))) =
      dist ((C.triangle f).vertex e) ((C.triangle f).vertex (Triangle.next e)) := by
  obtain ⟨G⟩ := E.exists_ordered_faceSidePieces f e
  let F := (K.projectFaceEquiv f).symm.toAffineMap
  have first (a : E.faceSidePieces f e) := a.property (left_mem_segment ℝ _ _)
  have last (a : E.faceSidePieces f e) := a.property (right_mem_segment ℝ _ _)
  have sum := G.sum_dist_affine_eq ((K.projectedTriangle f).edge_endpoints_ne e) first last F
  have coordinates (a : E.faceSidePieces f e) (j : Fin 3) :
      F ((E.partition.projectedTriangle a.val.1.val).vertex j) =
        E.originalPlace a.val.1.val f a.val.1.property
          ((E.partition.triangle a.val.1.val).vertex j) := by
    change (K.projectFaceEquiv f).symm _ = (K.projectFaceEquiv f).symm
      (E.pieceProjection a.val.1.val ((E.pieceProjection a.val.1.val).symm _))
    rw [(E.pieceProjection a.val.1.val).apply_symm_apply]
  have lengths (a : E.faceSidePieces f e) :
      dist (F ((E.partition.projectedTriangle a.val.1.val).vertex a.val.2))
        (F ((E.partition.projectedTriangle a.val.1.val).vertex (Triangle.next a.val.2))) =
      dist ((E.partition.triangle a.val.1.val).vertex a.val.2)
        ((E.partition.triangle a.val.1.val).vertex (Triangle.next a.val.2)) := by
    rw [coordinates, coordinates]
    exact (E.originalPlace a.val.1.val f a.val.1.property).isometry.dist_eq _ _
  have endpoints (j : Fin 3) : F ((K.projectedTriangle f).vertex j) =
      (C.triangle f).vertex j := (K.projectFaceEquiv f).symm_apply_apply _
  simpa only [lengths, endpoints] using sum

namespace OriginalBankBlock

variable {E} {retain : Set C.Seam} {s : C.CutSeam retain} {side flag : Bool}
  (A : E.OriginalBankBlock retain s side flag)

open Classical in
/-- Every complete directed block has exactly the full original edge length. -/
theorem sum_bank_lengths :
    (∑ i, E.originalComplex.boundaryBankLength (A.chain.point i)) =
      dist ((C.triangle (C.seamSide s.val side).face).vertex (C.seamSide s.val side).edge)
        ((C.triangle (C.seamSide s.val side).face).vertex
          (Triangle.next (C.seamSide s.val side).edge)) := by
  have length (i) : E.originalComplex.boundaryBankLength (A.chain.point i) =
      dist ((E.partition.triangle (A.index i).val.1.val).vertex (A.index i).val.2)
        ((E.partition.triangle (A.index i).val.1.val).vertex
          (Triangle.next (A.index i).val.2)) := by
    rw [E.originalComplex.boundaryBankLength_eq_edge]
    have edge := congrArg (fun bank : E.originalComplex.BoundaryBank (E.originalRetain retain) =>
      bank.val) (A.named i)
    change E.originalComplex.germEdge (A.chain.point i).val =
      (E.subdividedCutBank retain s side (A.index i)).val at edge
    rw [edge]
    rfl
  rw [show (∑ i, E.originalComplex.boundaryBankLength (A.chain.point i)) =
    ∑ i, dist ((E.partition.triangle (A.index i).val.1.val).vertex (A.index i).val.2)
      ((E.partition.triangle (A.index i).val.1.val).vertex (Triangle.next (A.index i).val.2))
      from Finset.sum_congr rfl (fun i _ => length i)]
  exact (Equiv.sum_comp A.index (fun a =>
    dist ((E.partition.triangle a.val.1.val).vertex a.val.2)
      ((E.partition.triangle a.val.1.val).vertex (Triangle.next a.val.2)))).trans
        (E.sum_faceSidePieces_lengths _ _)

end OriginalBankBlock
end Unfoldings.ConvexRoof.CompletionMesh
