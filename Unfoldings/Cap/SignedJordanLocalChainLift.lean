module

public import Unfoldings.Cap.SignedJordanBankPropagation
public import Unfoldings.Cap.JordanBoundaryChainLift

/-! One initial bank side constructs the full actual Jordan comparison in either orientation. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap

open Filter Topology

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexCap C)
  {J : Set Plane} (jordan : Schoenflies.IsJordanCurve J) (contains : J ⊆ K.footprint)
  (avoids : ∀ f, Disjoint (interior (K.projectedTriangle f).carrier) J)

include jordan contains avoids in
open Classical in
/-- Local two-ray geometry propagates the original incident side through the entire
actual Jordan traversal. Only the initial selected face is specified. All later banks,
corner fans, lengths, real heading prefixes and the full roll are derived
in either orientation. -/
theorem exists_jordan_boundary_chain_of_local_rays_signed (U : Set Face)
    {retain : Set (C.restrictFaces U).Seam} {n : ℕ}
    (c : ((C.restrictFaces U).boundarySystem retain).Chain n)
    (selected : c.first.val.1.1.val ∈ K.jordanFaces J)
    (on_curve : (K.projectedTriangle c.first.val.1.1.val).edge
      (C.germEdge (C.includeRestrictedGerm U c.first.val)).edge ⊆ J)
    (locally : ∀ i : Fin n, ∀ᶠ x in 𝓝
      (Cap.horizontal ((K.folding.restrictFaces U).boundaryPosition (c.point i.succ))),
      x ∈ J → x - Cap.horizontal
        ((K.folding.restrictFaces U).boundaryPosition (c.point i.succ)) ∈
      nonnegativeRay (Cap.horizontal
        ((K.folding.restrictFaces U).germDirection (c.point i.succ).val)) ∪
      nonnegativeRay (Cap.horizontal ((K.folding.restrictFaces U).germDirection
        ((C.restrictFaces U).boundaryMate retain (c.point i.succ)).val))) :
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
  have available (i : Fin (n + 1)) : ∃ q : T.BoundaryEnd Set.univ,
      C.includeRestrictedGerm V q.val = C.includeRestrictedGerm U (c.point i).val := by
    induction i using Fin.induction with
    | zero =>
      exact K.exists_jordan_bank_of_original_germ jordan contains avoids
        (C.includeRestrictedGerm U c.first.val) selected on_curve
    | succ k previous =>
      obtain ⟨p, named⟩ := previous
      exact K.exists_next_jordan_bank_of_local_rays_signed jordan contains avoids U
        (c.point k.castSucc) (c.point k.succ) (c.next k) p named
        (locally k)
  obtain ⟨d, banks⟩ := K.exists_restricted_boundary_chain_of_original_banks U V embedded c available
  exact ⟨d, banks, C.restricted_boundary_chain_rollHeading V U d c banks,
    C.restricted_boundary_chain_roll V U d c banks⟩

end Unfoldings.ConvexCap
