module

public import Unfoldings.Cone.LinkComparison
public import Unfoldings.Topology.ChainPairings

/-!
# Every actual seam of an interval link is consecutive

The fixed two terminal germs rule out a hidden closing seam. This classifies
every directed original radial seam by a consecutive pair in either direction.
-/

@[expose] public section

noncomputable section

namespace Unfoldings.TriangleComplex

universe u v

variable {Face : Type u} [Fintype Face] (C : TriangleComplex.{u, v} Face)
  (retain : Set C.Seam) (v : C.Vertex retain)

theorem tangentSeam_interval_cases {n : ℕ} (chain : (C.linkSystem retain v).Chain n)
    (covers : ∀ p, chain.Visited p)
    (start : C.linkMate retain v chain.first = chain.first)
    (finish : C.linkMate retain v (C.linkTurn retain v chain.last) =
      C.linkTurn retain v chain.last) (s : C.TangentSeam retain v) :
    (∃ k : Fin n, C.tangentSourceGerm retain v s = C.turnGerm (chain.point k.castSucc).val ∧
      C.tangentTargetGerm retain v s = (chain.point k.succ).val) ∨
    (∃ k : Fin n, C.tangentSourceGerm retain v s = (chain.point k.succ).val ∧
      C.tangentTargetGerm retain v s = C.turnGerm (chain.point k.castSucc).val) := by
  let p : C.LinkGerm retain v := ⟨C.tangentSourceGerm retain v s, s.property.2⟩
  let q : C.LinkGerm retain v :=
    ⟨C.tangentTargetGerm retain v s, (C.tangentRight retain v s).property⟩
  have paired : C.linkMate retain v p = q := by
    apply Subtype.ext
    exact C.mateGerm_of_crossing (C.tangentSeam_crosses retain v s)
  have different : p ≠ q := by
    intro equal
    exact GermCrosses.ne C (C.tangentSeam_crosses retain v s) (congrArg Subtype.val equal)
  rcases chain.interval_pairing_cases start finish (covers p) paired different with
    ⟨k, source, target⟩ | ⟨k, source, target⟩
  · exact Or.inl ⟨k, congrArg Subtype.val source, congrArg Subtype.val target⟩
  · exact Or.inr ⟨k, congrArg Subtype.val source, congrArg Subtype.val target⟩

end Unfoldings.TriangleComplex
