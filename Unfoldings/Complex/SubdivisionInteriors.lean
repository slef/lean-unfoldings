module

public import Unfoldings.Complex.SubdivisionMetric
public import Unfoldings.Geometry.Interior
public import Unfoldings.Geometry.EdgePerfect

/-! Interior disjointness and original-face adjacency derived from seam conformity. -/

@[expose] public section

noncomputable section

namespace Unfoldings.TriangleComplex

universe u v w z

variable {Face : Type u} [Fintype Face] {Child : Type w} [Fintype Child]
  {C : TriangleComplex.{u, v} Face} {D : TriangleComplex.{w, z} Child}

theorem eq_of_related_interior {retain : Set C.Seam} {a b : C.Total}
    (inside : a.2.val ∈ interior (C.triangle a.1).carrier)
    (related : Relation.EqvGen (C.glue retain) a b) : a = b := by
  have regular : ¬ C.IsVertex a := by
    rintro ⟨i, hi⟩
    exact (C.triangle a.1).not_mem_interior_of_mem_edge i
      (hi ▸ left_mem_segment ℝ _ _) inside
  rcases (C.eqvGen_iff_of_regular retain regular).mp related with equal | crossing
  · exact equal
  · obtain ⟨s, kept, side, x, equal, _⟩ := crossing
    subst a
    exact ((C.triangle (C.seamSide s side).face).not_mem_interior_of_mem_edge
      (C.seamSide s side).edge x.property inside).elim

namespace Subdivision

variable (S : C.Subdivision D)

theorem interior_inside (g : Child) :
    S.place g '' interior (D.triangle g).carrier ⊆ interior (C.triangle (S.parent g)).carrier := by
  rw [rigid_image_interior (S.place g)]
  exact interior_mono (by rintro _ ⟨x, hx, rfl⟩; exact S.inside g x hx)

namespace Conforming

variable {S} {retain : Set C.Seam} {fineRetain : Set D.Seam}
  (H : S.Conforming retain fineRetain)

include H in
theorem same_parent_disjoint {g h : Child} (different : g ≠ h) (same : S.parent g = S.parent h) :
    Disjoint (interior (S.place g '' (D.triangle g).carrier))
      (interior (S.place h '' (D.triangle h).carrier)) := by
  rw [← rigid_image_interior (S.place g), ← rigid_image_interior (S.place h)]
  apply Set.disjoint_left.mpr
  rintro p ⟨x, hx, first⟩ ⟨y, hy, last⟩
  let a : D.Total := ⟨g, ⟨x, interior_subset hx⟩⟩
  let b : D.Total := ⟨h, ⟨y, interior_subset hy⟩⟩
  have equal : S.parentPoint a = S.parentPoint b :=
    S.parentPoint_eq same (first.trans last.symm)
  have oldRelated : Relation.EqvGen (C.glue retain) (S.parentPoint a) (S.parentPoint b) := by
    rw [equal]
    exact Relation.EqvGen.refl _
  have related := H.lifts a b oldRelated
  have tagged : a = b := D.eq_of_related_interior hx related
  exact different (congrArg Sigma.fst tagged)

include H in
/-- A fine seam lies within one old face or joins the two banks of a retained old seam. -/
theorem parent_adjacent (s : D.Seam) (kept : s ∈ fineRetain) :
    S.parent (D.left s).face = S.parent (D.right s).face ∨
      ∃ t ∈ retain,
        (S.parent (D.left s).face = (C.left t).face ∧
          S.parent (D.right s).face = (C.right t).face) ∨
        (S.parent (D.left s).face = (C.right t).face ∧
          S.parent (D.right s).face = (C.left t).face) := by
  let T := D.triangle (D.left s).face
  let E := T.Edge (D.left s).edge
  let p : E → C.Total := fun x => S.parentPoint (D.edgePoint (D.left s) x)
  have injective : Function.Injective p := by
    intro x y equal
    apply Subtype.ext
    apply (S.place (D.left s).face).injective
    exact congrArg (fun a : C.Total => a.2.val) equal
  have finite : {x : E | C.IsVertex (p x)}.Finite :=
    C.finite_vertices.preimage (f := p) injective.injOn
  let := T.edgePerfectSpace (D.left s).edge
  have infinite : (Set.univ : Set E).Infinite :=
    infinite_of_mem_nhds ⟨T.vertex (D.left s).edge, left_mem_segment ℝ _ _⟩ (by simp)
  obtain ⟨x, nonvertex⟩ : ∃ x : E, ¬ C.IsVertex (p x) := by
    by_contra none
    push Not at none
    exact infinite (finite.subset (fun x _ => none x))
  have related := H.respects _ _ ⟨s, kept, x, rfl, rfl⟩
  rcases (C.eqvGen_iff_of_regular retain nonvertex).mp related with equal | crossing
  · exact Or.inl (congrArg Sigma.fst equal)
  · obtain ⟨t, ht, side, y, first, last⟩ := crossing
    refine Or.inr ⟨t, ht, ?_⟩
    cases side
    · exact Or.inl ⟨congrArg Sigma.fst first, congrArg Sigma.fst last⟩
    · exact Or.inr ⟨congrArg Sigma.fst first, congrArg Sigma.fst last⟩

end Conforming
end Subdivision
end Unfoldings.TriangleComplex
