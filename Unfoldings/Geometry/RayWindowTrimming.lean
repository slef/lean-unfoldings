module

public import Unfoldings.Geometry.AxisQuadrantFrame
public import Unfoldings.Geometry.OpenEndTrimming
public import Unfoldings.Geometry.RayWindowAngle

/-! Turn a short source-ray window into a genuinely trimmed chain in a pointed quadrant. -/

@[expose] public section

noncomputable section

namespace Unfoldings

/-- One constructed linear frame contains every actual ray of a short angular window. -/
theorem exists_quadrantFrame_of_ray_angle_sum {n : ℕ} (ray : Fin (n + 1) → Plane)
    (genuine : ∀ i, ray i ≠ 0)
    (small : (∑ k : Fin n, InnerProductGeometry.angle (ray k.castSucc) (ray k.succ)) <
      Real.pi / 4) :
    ∃ frame : (ℝ × ℝ) ≃ₗ[ℝ] Plane, ∀ i,
      0 < (frame.symm (ray i)).1 ∧ 0 < (frame.symm (ray i)).2 := by
  classical
  refine ⟨axisQuadrantFrame (ray 0), fun i => ?_⟩
  apply axisQuadrantFrame_positive (genuine 0)
  have bound := angle_le_partialSum_difference ray genuine (Fin.zero_le i)
  rw [Fin.partialSum_zero, sub_zero, Fin.partialSum, List.sum_take_ofFn] at bound
  have sum_bound : (∑ k ∈ Finset.univ.filter (fun k : Fin n => k.val < i.val),
      InnerProductGeometry.angle (ray k.castSucc) (ray k.succ)) ≤
      ∑ k : Fin n, InnerProductGeometry.angle (ray k.castSucc) (ray k.succ) :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun k _ _ => InnerProductGeometry.angle_nonneg _ _)
  exact (bound.trans sum_bound).trans_lt small

namespace PolygonalChain

variable {n : ℕ} (P : PolygonalChain Plane (n + 2)) (source : Plane)

/-- The original source rays at every internal corner, omitting both trimmable endpoint vertices. -/
def internalSourceRay (i : Fin (n + 1)) : Plane := P.vertex i.succ.castSucc - source

/-- Genuine endpoint trimming constructs the pointed wedge required by radial bank closure. -/
theorem exists_trimEnds_quadrant_of_internal_angle_sum
    (genuine : ∀ i, P.internalSourceRay source i ≠ 0)
    (small : (∑ k : Fin n, InnerProductGeometry.angle
      (P.internalSourceRay source k.castSucc) (P.internalSourceRay source k.succ)) < Real.pi / 4) :
    ∃ (frame : (ℝ × ℝ) ≃ₗ[ℝ] Plane) (a b : unitInterval),
      (0 < a.val ∧ a.val < 1) ∧ (0 < b.val ∧ b.val < 1) ∧
      ∀ j, 0 < (frame.symm ((P.trimEnds a b).vertex j - source)).1 ∧
        0 < (frame.symm ((P.trimEnds a b).vertex j - source)).2 := by
  obtain ⟨frame, positive⟩ := exists_quadrantFrame_of_ray_angle_sum
    (P.internalSourceRay source) genuine small
  let U : Set Plane := {z | 0 < (frame.symm (z - source)).1 ∧
    0 < (frame.symm (z - source)).2}
  have continuous : Continuous frame.symm := frame.symm.continuous_of_finiteDimensional
  have opened : IsOpen U :=
    (isOpen_lt continuous_const ((continuous.comp (continuous_id.sub continuous_const)).fst)).inter
      (isOpen_lt continuous_const ((continuous.comp (continuous_id.sub continuous_const)).snd))
  have internal (j : Fin (n + 3)) (first : 0 < j.val) (last : j.val < n + 2) : P.vertex j ∈ U := by
    let i : Fin (n + 1) := ⟨j.val - 1, by omega⟩
    have same : P.internalSourceRay source i = P.vertex j - source := by
      apply congrArg (fun k => P.vertex k - source)
      apply Fin.ext
      change j.val - 1 + 1 = j.val
      omega
    have bound := positive i
    rw [same] at bound
    exact bound
  obtain ⟨a, b, first, last, inside⟩ := P.exists_trimEnds_vertices_mem opened internal
  exact ⟨frame, a, b, first, last, inside⟩

end PolygonalChain
end Unfoldings
