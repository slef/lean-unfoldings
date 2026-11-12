module

public import Unfoldings.Geometry.RadialChain
public import Mathlib.Topology.Order.IntermediateValue

/-! Truncate an outward polygonal path at a prescribed physical source radius. -/

@[expose] public section

namespace Unfoldings.PolygonalChain

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}
  (P : PolygonalChain E n)

/-- A finite chain starting strictly inside and ending outside a sphere meets it on
an actual closed edge. No radial assumption is needed for existence. -/
theorem exists_point_at_radius (source : E) (radius : ℝ)
    (start : dist source (P.vertex 0) < radius)
    (finish : radius ≤ dist source (P.vertex (Fin.last n))) :
    ∃ i : Fin n, ∃ s : unitInterval, dist source (P.point i s) = radius := by
  induction n with
  | zero => exact (not_lt_of_ge finish start).elim
  | succ n ih =>
    let Q : PolygonalChain E n := ⟨fun j => P.vertex j.castSucc⟩
    by_cases earlier : radius ≤ dist source (Q.vertex (Fin.last n))
    · obtain ⟨i, s, equal⟩ := ih Q start earlier
      exact ⟨i.castSucc, s, equal⟩
    · have continuous : Continuous (fun s : ℝ => dist source
          (AffineMap.lineMap (P.vertex (Fin.last n).castSucc)
            (P.vertex (Fin.last n).succ) s)) :=
        continuous_const.dist AffineMap.lineMap_continuous
      obtain ⟨s, bounds, equal⟩ := intermediate_value_Icc (show (0 : ℝ) ≤ 1 from zero_le_one)
        continuous.continuousOn (show radius ∈ Set.Icc
          (dist source (AffineMap.lineMap (P.vertex (Fin.last n).castSucc)
            (P.vertex (Fin.last n).succ) 0))
          (dist source (AffineMap.lineMap (P.vertex (Fin.last n).castSucc)
            (P.vertex (Fin.last n).succ) 1)) from by
          constructor
          · rw [AffineMap.lineMap_apply_zero]
            exact le_of_not_ge earlier
          · rw [AffineMap.lineMap_apply_one]
            exact finish)
      exact ⟨Fin.last n, ⟨s, bounds⟩, equal⟩

/-- An outward chain reaches every intermediate radius with its entire preceding
path still inside the closed ball. This stops before any uncontrolled far continuation. -/
theorem RadialFrom.exists_radius_prefix {source : E} (radial : P.RadialFrom source 0)
    (radius : ℝ) (start : dist source (P.vertex 0) < radius)
    (finish : radius ≤ dist source (P.vertex (Fin.last n))) :
    ∃ i : Fin n, ∃ s : unitInterval,
      dist source (P.point i s) = radius ∧
      (∀ j : Fin (n + 1), j.val ≤ i.val → dist source (P.vertex j) ≤ radius) ∧
      ∀ j : Fin n, ∀ r : unitInterval, Before j r i s →
        dist source (P.point j r) ≤ radius := by
  obtain ⟨i, s, equal⟩ := P.exists_point_at_radius source radius start finish
  refine ⟨i, s, equal, ?_, ?_⟩
  · intro j before
    have first := radial.dist_vertices_le P j i.castSucc (Nat.zero_le _) before
    have last := radial i (Nat.zero_le _) (show (0 : unitInterval) ≤ s from s.property.1)
    change dist source (P.point i 0) ≤ dist source (P.point i s) at last
    rw [P.point_zero, equal] at last
    exact first.trans last
  · intro j r before
    exact (radial.dist_point_le P j i r s (Nat.zero_le _) before).trans_eq equal

end Unfoldings.PolygonalChain
