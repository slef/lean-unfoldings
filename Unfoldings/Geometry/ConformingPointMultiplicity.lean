module

public import Unfoldings.Geometry.ConformingTriangles
public import Unfoldings.Complex.GeometricPairings

/-! A nonvertex point of a conforming planar partition belongs to at most two faces. -/

@[expose] public section

namespace Unfoldings.TriangleFamily

variable {I : Type*} (triangle : I → Triangle)

theorem atMostTwo_faces_of_nonvertex (conforming : Conforming triangle)
    (separated : Pairwise (fun i j =>
      Disjoint (interior (triangle i).carrier) (interior (triangle j).carrier)))
    (i : I) {p : Plane} (member : p ∈ (triangle i).carrier) (regular : ¬ (triangle i).IsVertex p) :
    ∃ j, ∀ k, p ∈ (triangle k).carrier → k = i ∨ k = j := by
  classical
  by_cases other : ∃ j, j ≠ i ∧ p ∈ (triangle j).carrier
  · obtain ⟨j, different_j, member_j⟩ := other
    obtain ⟨e, f, shared_j, on_edge⟩ :=
      (conforming i j (Ne.symm different_j) p ⟨member, member_j⟩).resolve_left
        (fun vertices => regular vertices.1)
    refine ⟨j, fun k member_k => ?_⟩
    by_cases same : k = i
    · exact Or.inl same
    · obtain ⟨a, b, shared_k, on_other⟩ :=
        (conforming i k (Ne.symm same) p ⟨member, member_k⟩).resolve_left
          (fun vertices => regular vertices.1)
      have edges_equal : e = a := by
        by_contra different
        exact regular ((triangle i).isVertex_of_mem_edges different on_edge on_other)
      subst a
      have partners : (⟨j, f⟩ : EdgeRef I) = ⟨k, b⟩ :=
        edge_partner_unique triangle separated (a := ⟨i, e⟩)
          (Ne.symm different_j) (Ne.symm same) shared_j shared_k
      exact Or.inr (congrArg EdgeRef.face partners).symm
  · exact ⟨i, fun k member_k => Or.inl (by
      by_contra different
      exact other ⟨k, different, member_k⟩)⟩

end Unfoldings.TriangleFamily
