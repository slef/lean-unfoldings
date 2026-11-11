module

public import Unfoldings.Geometry.AngleMonotone

/-! Positive-span wedges are convex and commute with linear maps. -/

@[expose] public section

namespace Unfoldings

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] {u v x y : E}

theorem InDirectionWedge.nonneg_smul (inside : InDirectionWedge u v x)
    {r : ℝ} (nonnegative : 0 ≤ r) : InDirectionWedge u v (r • x) := by
  obtain ⟨a, b, first, last, equal⟩ := inside
  exact ⟨r * a, r * b, mul_nonneg nonnegative first, mul_nonneg nonnegative last,
    by rw [equal, smul_add, smul_smul, smul_smul]⟩

theorem InDirectionWedge.add (first : InDirectionWedge u v x)
    (last : InDirectionWedge u v y) : InDirectionWedge u v (x + y) := by
  obtain ⟨a, b, ha, hb, first⟩ := first
  obtain ⟨c, d, hc, hd, last⟩ := last
  refine ⟨a + c, b + d, add_nonneg ha hc, add_nonneg hb hd, ?_⟩
  rw [first, last, add_smul, add_smul]
  abel

theorem InDirectionWedge.map (inside : InDirectionWedge u v x) (L : E →ₗ[ℝ] F) :
    InDirectionWedge (L u) (L v) (L x) := by
  obtain ⟨a, b, first, last, equal⟩ := inside
  exact ⟨a, b, first, last, by rw [equal, map_add, map_smul, map_smul]⟩

theorem convex_inDirectionWedge (u v : E) : Convex ℝ {x | InDirectionWedge u v x} := by
  intro x first y last a b ha hb _
  exact (first.nonneg_smul ha).add (last.nonneg_smul hb)

end Unfoldings
