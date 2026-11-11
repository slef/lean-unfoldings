module

public import Unfoldings.Geometry.RadialTailLabels

/-! A skirt tail that meets the inner convex rim starts exactly at that meeting point. -/

@[expose] public section

namespace Unfoldings.RadialClipTail

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {S B : Set E} {q p x : E} (T : RadialClipTail S q p)

theorem inner_frontier_eq_seed_of_member (convex : Convex ℝ B) (origin : q ∈ interior B)
    (outside : p ∉ interior B) (boundary : x ∈ frontier B) (member : x ∈ T.carrier) :
    x = p := by
  obtain ⟨a, bounds, at_x⟩ := T.carrier_eq_image.subset member
  by_cases same : a = T.start
  · rw [same] at at_x
    exact at_x.symm.trans T.seed_eq.symm
  · have positive : 0 < a := T.start_pos.trans_le bounds.1
    have strict : T.start < a := lt_of_le_of_ne bounds.1 (fun equal => same equal.symm)
    have small : T.start / a < 1 := (div_lt_one positive).mpr strict
    have inside := convex.combo_interior_closure_mem_interior origin boundary.1
      (sub_pos.mpr small) (div_nonneg T.start_pos.le positive.le)
      (show (1 - T.start / a) + T.start / a = 1 by ring)
    have equal : (1 - T.start / a) • q + (T.start / a) • x = p := by
      calc
        _ = q + T.start • (T.tip - q) := by
          rw [← at_x]
          simp only [smul_add, smul_smul, div_mul_cancel₀ _ positive.ne']
          module
        _ = p := T.seed_eq.symm
    exact (outside (equal ▸ inside)).elim

end Unfoldings.RadialClipTail
