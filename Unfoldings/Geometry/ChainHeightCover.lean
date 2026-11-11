module

public import Unfoldings.Geometry.ChainLinear
public import Unfoldings.Geometry.HeightGraphSplice
public import Mathlib.Tactic.FieldSimp

/-! A represented monotone chain covers every intermediate height by an actual whole-edge point. -/

@[expose] public section

noncomputable section

namespace Unfoldings

theorem exists_adjacent_height {n : ℕ} (height : Fin (n + 1) → ℝ) (h : ℝ)
    (start : height 0 ≤ h) (finish : h < height (Fin.last n)) :
    ∃ i : Fin n, height i.castSucc ≤ h ∧ h < height i.succ := by
  induction n with
  | zero => exact (not_lt_of_ge start finish).elim
  | succ n ih =>
    by_cases first : h < height (0 : Fin (n + 1)).succ
    · exact ⟨0, start, first⟩
    · let tail : Fin (n + 1) → ℝ := fun j => height j.succ
      obtain ⟨i, lower, upper⟩ := ih tail (le_of_not_gt first) finish
      exact ⟨i.succ, lower, upper⟩

namespace PolygonalChain

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}
  (P : PolygonalChain E n)

theorem exists_point_at_linear_height (height : E →ₗ[ℝ] ℝ)
    (positive : ∀ i, 0 < height (P.edge i)) (h : ℝ)
    (start : height (P.vertex 0) ≤ h) (finish : h < height (P.vertex (Fin.last n))) :
    ∃ i : Fin n, ∃ s : unitInterval, height (P.point i s) = h := by
  obtain ⟨i, lower, upper⟩ := exists_adjacent_height (fun j => height (P.vertex j)) h start finish
  have delta : 0 < height (P.vertex i.succ) - height (P.vertex i.castSucc) := by
    simpa only [edge, map_sub] using positive i
  let s : unitInterval := ⟨(h - height (P.vertex i.castSucc)) /
      (height (P.vertex i.succ) - height (P.vertex i.castSucc)),
    div_nonneg (sub_nonneg.mpr lower) delta.le,
    (div_le_one delta).mpr (by linarith)⟩
  refine ⟨i, s, ?_⟩
  rw [P.linear_point height i s]
  change (1 - (h - height (P.vertex i.castSucc)) /
      (height (P.vertex i.succ) - height (P.vertex i.castSucc))) * height (P.vertex i.castSucc) +
    (h - height (P.vertex i.castSucc)) /
      (height (P.vertex i.succ) - height (P.vertex i.castSucc)) * height (P.vertex i.succ) = h
  field_simp [delta.ne']
  ring

end PolygonalChain

namespace PolygonalChain

variable {n : ℕ} (P : PolygonalChain ℂ n)

/-- Exact segment representation prevents a height graph from taking shortcuts between vertices. -/
theorem heightGraph_point_on_chain (G : MonotoneHeightGraph)
    (representation : ∀ i (s : unitInterval),
      G.coordinate ((P.point i s).re + (P.point i s).im) = (P.point i s).re)
    (positive : ∀ i, 0 < (P.edge i).re + (P.edge i).im) (h : ℝ)
    (start : (P.vertex 0).re + (P.vertex 0).im ≤ h)
    (finish : h < (P.vertex (Fin.last n)).re + (P.vertex (Fin.last n)).im) :
    ∃ i : Fin n, ∃ s : unitInterval, G.point h = P.point i s := by
  let height : ℂ →ₗ[ℝ] ℝ := Complex.reCLM.toLinearMap + Complex.imCLM.toLinearMap
  obtain ⟨i, s, equal⟩ := P.exists_point_at_linear_height height positive h start finish
  have point := G.point_eq_of_coordinate (P.point i s) (representation i s)
  change (P.point i s).re + (P.point i s).im = h at equal
  rw [equal] at point
  exact ⟨i, s, point⟩

end PolygonalChain
end Unfoldings
