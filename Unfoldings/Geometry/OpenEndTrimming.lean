module

public import Unfoldings.Geometry.ChainEndTrimming
public import Mathlib.Topology.Order.DenselyOrdered

/-! Genuine endpoint trims enter any open set already containing all internal chain vertices. -/

@[expose] public section

namespace Unfoldings

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- An open neighborhood of any point of a segment also contains a strictly interior parameter. -/
theorem exists_open_segment_parameter {U : Set E} (opened : IsOpen U) (a b : E)
    (t : unitInterval) (member : AffineMap.lineMap a b t.val ∈ U) :
    ∃ s : unitInterval, 0 < s.val ∧ s.val < 1 ∧ AffineMap.lineMap a b s.val ∈ U := by
  let V : Set ℝ := AffineMap.lineMap a b ⁻¹' U
  have open_V : IsOpen V := opened.preimage AffineMap.lineMap_continuous
  have approached : t.val ∈ closure (Set.Ioo (0 : ℝ) 1) := by
    rw [closure_Ioo (by norm_num : (0 : ℝ) ≠ 1)]
    exact t.property
  obtain ⟨s, inside, strict⟩ := (mem_closure_iff.mp approached) V open_V member
  exact ⟨⟨s, strict.1.le, strict.2.le⟩, strict.1, strict.2, inside⟩

namespace PolygonalChain

variable {n : ℕ} (P : PolygonalChain E (n + 2))

/-- The genuine trims keep every internal original vertex and place both new endpoints in U. -/
theorem exists_trimEnds_vertices_mem {U : Set E} (opened : IsOpen U)
    (internal : ∀ j : Fin (n + 3), 0 < j.val → j.val < n + 2 → P.vertex j ∈ U) :
    ∃ a b : unitInterval, (0 < a.val ∧ a.val < 1) ∧ (0 < b.val ∧ b.val < 1) ∧
      ∀ j, (P.trimEnds a b).vertex j ∈ U := by
  obtain ⟨a, ap, al, first⟩ := exists_open_segment_parameter opened
    (P.vertex 0) (P.vertex (0 : Fin (n + 2)).succ) 1 (by
      rw [Set.Icc.coe_one, AffineMap.lineMap_apply_one]
      exact internal _ (by simp) (by simp))
  obtain ⟨b, bp, bl, last⟩ := exists_open_segment_parameter opened
    (P.vertex (Fin.last (n + 1)).castSucc) (P.vertex (Fin.last (n + 2))) 0 (by
      rw [Set.Icc.coe_zero, AffineMap.lineMap_apply_zero]
      exact internal _ (by simp) (by simp))
  refine ⟨a, b, ⟨ap, al⟩, ⟨bp, bl⟩, fun j => ?_⟩
  by_cases initial : j.val = 0
  · have equal : j = 0 := Fin.ext initial
    rw [equal, P.trimEnds_start]
    exact first
  · by_cases final : j.val = n + 2
    · have equal : j = Fin.last (n + 2) := Fin.ext final
      rw [equal, P.trimEnds_last]
      exact last
    · rw [P.trimEnds_vertex_internal a b j (by omega) (by omega)]
      exact internal j (by omega) (by omega)

end PolygonalChain
end Unfoldings
