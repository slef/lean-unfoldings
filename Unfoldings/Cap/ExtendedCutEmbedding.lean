module

public import Unfoldings.Cap.ExtendedCutParents

/-! The finite geometric cut forest has distinct actual projected vertex positions. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap.SkirtTailFamily

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexCap C} {Z : ℝ} {q : Plane} (F : K.SkirtTailFamily Z q)

theorem component_eq_of_common_mem (lower : Z < 0) (c d : F.Component) {x : Plane}
    (first : x ∈ (F.componentTail c).carrier) (last : x ∈ (F.componentTail d).carrier) : c = d := by
  by_contra different
  exact Set.disjoint_left.mp (F.components_disjoint lower different) first last

theorem independent_seed_ne_original (c : F.IndependentComponent) (w : C.Vertex Set.univ) :
    F.componentSeed c.val ≠ K.projectedVertex w := by
  intro same
  have boundary : C.IsBoundaryVertex Set.univ w := by
    by_contra internal
    have inside := (K.projectedVertex_mem_interior_iff w).mpr internal
    rw [← same] at inside
    exact F.component_outside c.val (F.componentTail c.val).seed_mem inside
  exact c.property.2 ⟨w, boundary, same.symm⟩

theorem independent_seed_ne_tip (lower : Z < 0) (c : F.IndependentComponent) (d : F.Component) :
    F.componentSeed c.val ≠ (F.componentTail d).tip := by
  intro same
  have at_last : F.componentSeed c.val ∈ (F.componentTail d).carrier :=
    same.symm ▸ (F.componentTail d).tip_mem
  have component := F.component_eq_of_common_mem lower c.val d
    (F.componentTail c.val).seed_mem at_last
  subst d
  exact c.property.1 same

/-- Auxiliary independent leaves, original vertices, and outer tips are all distinct.
The result concerns the complete geometric network, before choosing a fine triangulation. -/
theorem geometricPosition_injective (lower : Z < 0) : Function.Injective F.geometricPosition := by
  intro a b same
  cases a with
  | inl a =>
    cases b with
    | inl b => exact congrArg Sum.inl (K.projectedVertex_injective same)
    | inr b =>
      cases b with
      | inl b => exact (F.independent_seed_ne_original b a same.symm).elim
      | inr b => exact (F.rim_vertex_ne_tip lower b a same).elim
  | inr a =>
    cases a with
    | inl a =>
      cases b with
      | inl b => exact (F.independent_seed_ne_original a b same).elim
      | inr b =>
        cases b with
        | inl b =>
          change F.componentSeed a.val = F.componentSeed b.val at same
          have at_last : F.componentSeed a.val ∈ (F.componentTail b.val).carrier :=
            same.symm ▸ (F.componentTail b.val).seed_mem
          have component := F.component_eq_of_common_mem lower a.val b.val
            (F.componentTail a.val).seed_mem at_last
          exact congrArg (fun c : F.IndependentComponent => Sum.inr (Sum.inl c))
            (Subtype.ext component)
        | inr b => exact (F.independent_seed_ne_tip lower a b same).elim
    | inr a =>
      cases b with
      | inl b => exact (F.rim_vertex_ne_tip lower a b same.symm).elim
      | inr b =>
        cases b with
        | inl b => exact (F.independent_seed_ne_tip lower b a same.symm).elim
        | inr b =>
          change (F.componentTail a).tip = (F.componentTail b).tip at same
          have at_last : (F.componentTail a).tip ∈ (F.componentTail b).carrier :=
            same.symm ▸ (F.componentTail b).tip_mem
          have component := F.component_eq_of_common_mem lower a b
            (F.componentTail a).tip_mem at_last
          exact congrArg (fun c : F.Component => Sum.inr (Sum.inr c)) component

end Unfoldings.ConvexCap.SkirtTailFamily
