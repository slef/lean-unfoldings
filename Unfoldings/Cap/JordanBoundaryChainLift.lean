module

public import Unfoldings.Cap.JordanOriginalBanks
public import Unfoldings.Cap.RestrictedBoundaryChainLift

/-! Construct the actual Jordan boundary traversal of original banks, preserving their full roll. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexCap C)
  {J : Set Plane} (jordan : Schoenflies.IsJordanCurve J) (contains : J ⊆ K.footprint)
  (avoids : ∀ f, Disjoint (interior (K.projectedTriangle f).carrier) J)

include jordan contains avoids in
open Classical in
/-- Original banks on the curve with their incident faces inside the selected Jordan
filling construct its actual intrinsic bank chain. Successors, lengths, one-sided fans
and every unreduced heading are derived; no contour correspondence is supplied. -/
theorem exists_jordan_boundary_chain (U : Set Face)
    {retain : Set (C.restrictFaces U).Seam} {n : ℕ}
    (c : ((C.restrictFaces U).boundarySystem retain).Chain n)
    (selected : ∀ i, (c.point i).val.1.1.val ∈ K.jordanFaces J)
    (on_curve : ∀ i, (K.projectedTriangle (c.point i).val.1.1.val).edge
      (C.germEdge (C.includeRestrictedGerm U (c.point i).val)).edge ⊆ J) :
    ∃ d : ((C.restrictFaces (K.jordanFaces J)).boundarySystem Set.univ).Chain n,
      (∀ i, C.includeRestrictedGerm (K.jordanFaces J) (d.point i).val =
        C.includeRestrictedGerm U (c.point i).val) ∧
      (∀ i, (C.restrictFaces (K.jordanFaces J)).boundaryChainRollHeading d i =
        (C.restrictFaces U).boundaryChainRollHeading c i) ∧
      (C.restrictFaces (K.jordanFaces J)).boundaryChainRoll d =
        (C.restrictFaces U).boundaryChainRoll c := by
  let V := K.jordanFaces J
  let T := C.restrictFaces V
  have embedded : Function.Injective (fun w : T.Vertex Set.univ =>
      Cap.horizontal ((K.folding.restrictFaces V).toSpace Set.univ
        (T.vertexPoint Set.univ w))) := by
    intro w z same
    apply T.vertexPoint_injective Set.univ
    apply (K.jordanIntrinsicHomeomorph jordan contains avoids).injective
    exact Subtype.ext same
  have available (i) : ∃ q : T.BoundaryEnd Set.univ,
      C.includeRestrictedGerm V q.val = C.includeRestrictedGerm U (c.point i).val :=
    K.exists_jordan_bank_of_original_germ jordan contains avoids
      (C.includeRestrictedGerm U (c.point i).val) (selected i) (on_curve i)
  obtain ⟨d, banks⟩ := K.exists_restricted_boundary_chain_of_original_banks U V embedded c available
  refine ⟨d, banks, ?_, ?_⟩
  · intro i
    exact C.restricted_boundary_chain_rollHeading V U d c banks i
  · exact C.restricted_boundary_chain_roll V U d c banks

end Unfoldings.ConvexCap
