module

public import Unfoldings.Cap.GeometricCutLabels

/-! Every nonterminal node of the actual geometric forest lies strictly inside the roof clip. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap.SectorForest

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexCap C} {t : ℝ} {origin : C.Vertex Set.univ} (M : K.SectorForest t origin)
  {Z : ℝ} (F : K.SkirtTailFamily Z (K.projectedVertex origin))
  (covered : ∀ w : C.Vertex Set.univ, C.IsBoundaryVertex Set.univ w →
    K.projectedVertex w ∈ ⋃ c : F.Component, (F.componentTail c).carrier)
  (positive : 0 < t) (small : t < 1) (lower : Z < 0)

theorem geometric_nonroot_mem_clip_interior (w : F.GeometricVertex)
    (nonroot : w ∉ (M.geometricParents F covered positive small lower).roots) :
    F.geometricPosition w ∈ interior (K.clipFootprint Z) := by
  cases w with
  | inl w => exact K.original_footprint_in_clip_interior lower (K.projectedVertex_mem_footprint w)
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
      have source_inside : K.projectedVertex origin ∈ interior (K.clipFootprint Z) :=
        K.original_footprint_in_clip_interior lower (interior_subset F.origin)
      have inside := (K.convex_clipFootprint Z).combo_interior_closure_mem_interior source_inside
        T.boundary.1 (sub_pos.mpr strict) T.start_pos.le (show (1 - T.start) + T.start = 1 by ring)
      have equal : (1 - T.start) • K.projectedVertex origin + T.start • T.tip =
          F.componentSeed c.val := by
        calc
          _ = K.projectedVertex origin + T.start • (T.tip - K.projectedVertex origin) := by module
          _ = F.componentSeed c.val := T.seed_eq.symm
      change F.componentSeed c.val ∈ interior (K.clipFootprint Z)
      rw [← equal]
      exact inside

end Unfoldings.ConvexCap.SectorForest
