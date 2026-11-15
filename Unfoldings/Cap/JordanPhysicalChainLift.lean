module

public import Unfoldings.Cap.JordanPhysicalInitialBank
public import Unfoldings.Cap.JordanPhysicalBankPropagation
public import Unfoldings.Cap.PhysicalBoundaryChainLift

/-! Construct the complete actual Jordan bank traversal without an initial incident side. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap

open Filter Topology

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexCap C)
  {J : Set Plane} (jordan : Schoenflies.IsJordanCurve J) (contains : J ⊆ K.footprint)
  (avoids : ∀ f, Disjoint (interior (K.projectedTriangle f).carrier) J)

local instance jordanPhysicalChainMembership (U : Set Face) : DecidablePred (· ∈ U) :=
  Classical.decPred _

include jordan contains avoids in
/-- All physical original bank points and full edge vectors construct their actual Jordan
traversal. The initial selected side, later faces and actual successor order are derived.
The resulting one-sided fan may be the original bank's complementary side. -/
theorem exists_jordan_physical_chain_of_local_rays (U : Set Face)
    {retain : Set (C.restrictFaces U).Seam} {n : ℕ}
    (c : ((C.restrictFaces U).boundarySystem retain).Chain n)
    (simple : Function.Injective (K.projectedBoundaryChain U c).vertex)
    (internal : ∀ i, ¬ C.IsBoundaryVertex Set.univ
      (C.vertexOfCorner Set.univ (C.includeRestrictedGerm U (c.point i).val).1))
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
      (∀ i, (K.folding.restrictFaces (K.jordanFaces J)).boundaryPosition (d.point i) =
        (K.folding.restrictFaces U).boundaryPosition (c.point i)) ∧
      ∀ i, (K.folding.restrictFaces (K.jordanFaces J)).germDirection (d.point i).val =
        (K.folding.restrictFaces U).germDirection (c.point i).val := by
  let V := K.jordanFaces J
  let T := C.restrictFaces V
  let F := K.folding.restrictFaces U
  have paired : ¬ C.IsBoundaryEdge Set.univ
      (C.germEdge (C.includeRestrictedGerm U c.first.val)) := by
    intro boundary
    let raw := C.includeRestrictedGerm U c.first.val
    let g : C.LinkGerm Set.univ (C.vertexOfCorner Set.univ raw.1) := ⟨raw, rfl⟩
    have fixed : C.linkMate Set.univ _ g = g :=
      Subtype.ext ((C.mateGerm_eq_self_iff Set.univ raw).mpr boundary)
    exact internal 0 ((C.isBoundaryVertex_iff_linkMate_fixed Set.univ _).mpr ⟨g, fixed⟩)
  obtain ⟨first, first_position, first_vector⟩ := K.exists_jordan_initial_physical_bank
    jordan contains avoids (C.includeRestrictedGerm U c.first.val) paired on_curve
  have original_position : F.boundaryPosition c.first = K.folding.toSpace Set.univ
      (C.vertexPoint Set.univ (C.vertexOfCorner Set.univ
        (C.includeRestrictedGerm U c.first.val).1)) := by
    rw [F.boundaryPosition_raw]
    rfl
  have available (i : Fin (n + 1)) : ∃ q : T.BoundaryEnd Set.univ,
      (K.folding.restrictFaces V).boundaryPosition q = F.boundaryPosition (c.point i) ∧
      (K.folding.restrictFaces V).germDirection q.val = F.germDirection (c.point i).val := by
    induction i using Fin.induction with
    | zero => exact ⟨first, first_position.trans original_position.symm, first_vector⟩
    | succ k previous =>
      obtain ⟨p, position, direction⟩ := previous
      have next := K.jordan_next_bank_preserves_physical_edge jordan contains avoids U
        (c.point k.castSucc) (c.point k.succ) (c.next k) p position direction
        (internal k.succ) (locally k)
      exact ⟨_, next⟩
  have embedded : Function.Injective (fun w : T.Vertex Set.univ =>
      Cap.horizontal ((K.folding.restrictFaces V).toSpace Set.univ
        (T.vertexPoint Set.univ w))) := by
    intro w z same
    apply T.vertexPoint_injective Set.univ
    apply (K.jordanIntrinsicHomeomorph jordan contains avoids).injective
    exact Subtype.ext same
  exact K.exists_restricted_boundary_chain_of_physical_banks U V c embedded simple available

end Unfoldings.ConvexCap
