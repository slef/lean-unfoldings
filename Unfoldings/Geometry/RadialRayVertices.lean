module

public import Unfoldings.Geometry.PolygonalRayEmbedding

/-! Genuine source-radial polygonal banks have strictly ordered vertices and exact incidences. -/

@[expose] public section

open Topology
open scoped NNReal

namespace Unfoldings.PolygonalRay

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}
  (R : PolygonalRay E n) (outward : R.Outward)
  (genuine : ∀ i : Fin n, R.chain.vertex i.castSucc ≠ R.chain.vertex i.succ)

include outward genuine

/-- A genuine edge has strictly increasing source radius throughout its original parameter. -/
theorem edge_radius_strictMono (i : Fin n) :
    StrictMono (fun t : unitInterval => dist R.start (R.chain.point i t)) := by
  have radial := outward.1 i (Nat.zero_le _)
  have initial := (monotone_dist_lineMap_iff R.start (R.chain.vertex i.castSucc)
    (R.chain.vertex i.succ)).mp radial
  exact fun t s ordered => dist_lineMap_lt_of_inner_nonneg _ _ _ initial (genuine i)
    t.property.1 ordered

/-- Original vertex radii retain their strict order; no simplicity certificate is needed. -/
theorem vertex_radius_strictMono : StrictMono (fun i => dist R.start (R.chain.vertex i)) := by
  apply Fin.strictMono_iff_lt_succ.mpr
  intro i
  have strict := R.edge_radius_strictMono outward genuine i
    (show (0 : unitInterval) < 1 by norm_num)
  simpa only [PolygonalChain.point_zero, PolygonalChain.point_one] using strict

theorem vertex_injective_of_outward : Function.Injective R.chain.vertex := by
  intro i j equal
  exact (R.vertex_radius_strictMono outward genuine).injective (congrArg (dist R.start) equal)

/-- A named original vertex cannot lie strictly inside any original edge of the bank. -/
theorem vertex_not_mem_openSegment (k : Fin (n + 1)) (i : Fin n) :
    R.chain.vertex k ∉ openSegment ℝ (R.chain.vertex i.castSucc) (R.chain.vertex i.succ) := by
  intro member
  rw [openSegment_eq_image_lineMap] at member
  obtain ⟨t, bounds, equal⟩ := member
  let u : unitInterval := ⟨t, bounds.1.le, bounds.2.le⟩
  have at_u : R.chain.point i u = R.chain.vertex k := equal
  have first := R.edge_radius_strictMono outward genuine i
    (show (0 : unitInterval) < u from bounds.1)
  have last := R.edge_radius_strictMono outward genuine i
    (show u < (1 : unitInterval) from bounds.2)
  dsimp only at first last
  rw [PolygonalChain.point_zero, at_u] at first
  rw [PolygonalChain.point_one, at_u] at last
  by_cases before : k ≤ i.castSucc
  · exact (not_lt_of_ge ((R.vertex_radius_strictMono outward genuine).monotone before)) first
  · have after : i.succ ≤ k := by
      have ordered := lt_of_not_ge before
      change i.val + 1 ≤ k.val
      change i.val < k.val at ordered
      omega
    exact (not_lt_of_ge ((R.vertex_radius_strictMono outward genuine).monotone after)) last

/-- The whole true tail avoids every earlier original vertex. -/
theorem vertex_not_mem_tail (nonzero : R.direction ≠ 0) (k : Fin (n + 1))
    (before : k < Fin.last n) : R.chain.vertex k ∉ Set.range R.tail := by
  rintro ⟨t, equal⟩
  have earlier := R.vertex_radius_strictMono outward genuine before
  have tail_bound := (R.tail_radius_strictMono outward nonzero).monotone
    (show (0 : ℝ≥0) ≤ t from zero_le)
  rw [R.tail_zero, equal] at tail_bound
  exact (not_lt_of_ge tail_bound) earlier

end Unfoldings.PolygonalRay
