module

public import Unfoldings.Cone.Tangent

/-!
# Radial seams along actual ordered vertex links

Every consecutive pair in the constructed link order crosses a retained
original seam. The seam includes its actual direction and endpoint permutation,
so later fan placements can be built from genuine full-edge isometries.
-/

@[expose] public section

noncomputable section

namespace Unfoldings.TriangleComplex

universe u v

variable {Face : Type u} [Fintype Face] (C : TriangleComplex.{u, v} Face)
  (retain : Set C.Seam)

theorem germCrosses_mate_of_ne (p : C.Germ) (different : C.mateGerm retain p ≠ p) :
    C.GermCrosses retain p (C.mateGerm retain p) := by
  classical
  by_cases paired : ∃ q, C.GermCrosses retain p q
  · obtain ⟨q, crossing⟩ := paired
    rw [C.mateGerm_of_crossing crossing]
    exact crossing
  · exact (different (by simp only [mateGerm, dite_eq_right paired])).elim

/-- A consecutive pair in a link chain has an actual radial seam between its corners. -/
theorem exists_tangentSeam_of_link_next (v : C.Vertex retain)
    (p q : C.LinkGerm retain v)
    (next : C.linkMate retain v (C.linkTurn retain v p) = q)
    (different : q ≠ C.linkTurn retain v p) :
    ∃ s : C.TangentSeam retain v,
      C.tangentLeft retain v s = ⟨p.val.1, p.property⟩ ∧
      C.tangentRight retain v s = ⟨q.val.1, q.property⟩ := by
  have moved : C.mateGerm retain (C.turnGerm p.val) ≠ C.turnGerm p.val := by
    intro fixed
    apply different
    exact next.symm.trans (Subtype.ext fixed)
  have crossing := C.germCrosses_mate_of_ne retain (C.turnGerm p.val) moved
  have target : C.mateGerm retain (C.turnGerm p.val) = q.val :=
    congrArg Subtype.val next
  rw [target] at crossing
  obtain ⟨s, kept, side, b, source, target⟩ := crossing
  have vertex : C.vertexOfCorner retain
      (C.germOfEndpoint (C.seamSide s side) b).1 = v := by
    rw [← source]
    exact p.property
  let seam : C.TangentSeam retain v := ⟨(s, side, b), kept, vertex⟩
  refine ⟨seam, ?_, ?_⟩
  · apply Subtype.ext
    exact (congrArg Prod.fst source).symm
  · apply Subtype.ext
    exact (congrArg Prod.fst target).symm

/-- Each step in the nonrepeating corner order supplies the seam needed for a hinge placement. -/
theorem exists_tangentSeam_of_chain (v : C.Vertex retain) {n : ℕ}
    (chain : (C.linkSystem retain v).Chain n) (i : Fin n) :
    ∃ s : C.TangentSeam retain v,
      C.tangentLeft retain v s =
        ⟨(chain.point i.castSucc).val.1, (chain.point i.castSucc).property⟩ ∧
      C.tangentRight retain v s =
        ⟨(chain.point i.succ).val.1, (chain.point i.succ).property⟩ :=
  C.exists_tangentSeam_of_link_next retain v _ _ (chain.next i)
    (chain.disjoint i.succ i.castSucc)

end Unfoldings.TriangleComplex
