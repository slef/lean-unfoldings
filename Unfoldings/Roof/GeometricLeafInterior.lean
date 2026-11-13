module

public import Unfoldings.Roof.GeometricCutLabels

/-! Every nonterminal node of the actual geometric forest lies strictly inside the roof clip. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof.SectorForest

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexRoof C} {t : ℝ} {origin : Plane} (M : K.SectorForest t origin)
  {outer : Set Plane} (F : K.SkirtTailFamily outer (origin))
  (covered : ∀ w : C.Vertex Set.univ, C.IsBoundaryVertex Set.univ w →
    K.projectedVertex w ∈ ⋃ c : F.Component, (F.componentTail c).carrier)
  (positive : 0 < t) (small : t < 1)

theorem geometric_nonroot_mem_clip_interior (w : F.GeometricVertex)
    (nonroot : w ∉ (M.geometricParents F covered positive small).roots) :
    F.geometricPosition w ∈ interior outer := by
  cases w with
  | inl w => exact F.encloses (K.projectedVertex_mem_footprint w)
  | inr w =>
    cases w with
    | inr c => exact (nonroot ⟨c, rfl⟩).elim
    | inl c =>
      let T := F.componentTail c.val
      have strict : T.start < 1 := lt_of_le_of_ne T.start_le (by
        intro same
        have seed := T.seed_eq
        rw [same, one_smul, add_sub_cancel] at seed
        exact c.property.1 seed)
      have source_inside : origin ∈ interior outer :=
        F.encloses (interior_subset F.origin)
      have inside := F.convex.combo_interior_closure_mem_interior source_inside
        T.boundary.1 (sub_pos.mpr strict) T.start_pos.le (show (1 - T.start) + T.start = 1 by ring)
      have equal : (1 - T.start) • origin + T.start • T.tip =
          F.componentSeed c.val := by
        calc
          _ = origin + T.start • (T.tip - origin) := by module
          _ = F.componentSeed c.val := T.seed_eq.symm
      change F.componentSeed c.val ∈ interior outer
      rw [← equal]
      exact inside

end Unfoldings.ConvexRoof.SectorForest
