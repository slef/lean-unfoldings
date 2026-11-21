module

public import Unfoldings.Geometry.HalfTurnQuadrant
public import Unfoldings.Geometry.AffineArrangement

/-! Trim each endpoint in an open segment while avoiding a finite set of old vertices. -/

@[expose] public section

noncomputable section

namespace Unfoldings

theorem exists_open_parameter_avoids_points {I : Type*} [Finite I] (point : I → Plane)
    {U : Set Plane} (open_U : IsOpen U) {a b : Plane} (genuine : a ≠ b)
    (t : unitInterval) (member : AffineMap.lineMap a b t.val ∈ U) :
    ∃ s : unitInterval, (0 < s.val ∧ s.val < 1) ∧ AffineMap.lineMap a b s.val ∈ U ∧
      ∀ i, AffineMap.lineMap a b s.val ≠ point i := by
  let V := Set.Ioo (0 : ℝ) 1 ∩ AffineMap.lineMap a b ⁻¹' U
  have open_V : IsOpen V := isOpen_Ioo.inter
    (open_U.preimage AffineMap.lineMap_continuous)
  obtain ⟨anchor, first, last, in_U⟩ := exists_open_segment_parameter open_U a b t member
  have present : V.Nonempty := ⟨anchor.val, ⟨first, last⟩, in_U⟩
  let d := b - a
  let parameter (i) := inner ℝ d (point i - a) / ‖d‖ ^ 2
  let equation (i) : ℝ →ᵃ[ℝ] ℝ := AffineMap.id ℝ ℝ - AffineMap.const ℝ ℝ (parameter i)
  have proper (i) : equation i ≠ 0 := by
    intro zero
    have h := DFunLike.congr_fun zero (parameter i + 1)
    change parameter i + 1 - parameter i = 0 at h
    linarith
  obtain ⟨s, hs, avoids⟩ :=
    (AffineArrangement.dense_regular equation proper).inter_open_nonempty V open_V present
  refine ⟨⟨s, hs.1.1.le, hs.1.2.le⟩, hs.1, hs.2, ?_⟩
  intro i equal
  have position : point i - a = s • d := by
    rw [← equal, AffineMap.lineMap_apply_module', add_sub_cancel_right]
  have d_squared : ‖d‖ ^ 2 ≠ 0 :=
    pow_ne_zero _ (norm_ne_zero_iff.mpr (sub_ne_zero.mpr genuine.symm))
  have at_i : parameter i = s := by
    dsimp only [parameter]
    rw [position, real_inner_smul_right, real_inner_self_eq_norm_sq, mul_div_cancel_right₀ _ d_squared]
  exact avoids i (by change s - parameter i = 0; rw [at_i, sub_self])

namespace PolygonalChain

open InnerProductGeometry

variable {n : ℕ} (P : PolygonalChain Plane (n + 2)) (source : Plane)

/-- The two genuine trims can also avoid every old vertex without narrowing
the class of angular windows. -/
theorem exists_trimEnds_quadrant_of_halfturn_avoids
    (genuine : ∀ i, P.internalSourceRay source i ≠ 0)
    (small : (∑ k : Fin n, angle (P.internalSourceRay source k.castSucc)
      (P.internalSourceRay source k.succ)) < Real.pi)
    (first_nonzero : P.edge 0 ≠ 0) (last_nonzero : P.edge (Fin.last (n + 1)) ≠ 0)
    {I : Type*} [Finite I] (point : I → Plane) :
    ∃ (frame : (ℝ × ℝ) ≃ₗ[ℝ] Plane) (a b : unitInterval),
      (0 < a.val ∧ a.val < 1) ∧ (0 < b.val ∧ b.val < 1) ∧
      (∀ i, (P.trimEnds a b).vertex 0 ≠ point i) ∧
      (∀ i, (P.trimEnds a b).vertex (Fin.last (n + 2)) ≠ point i) ∧
      ∀ j, 0 < (frame.symm ((P.trimEnds a b).vertex j - source)).1 ∧
        0 < (frame.symm ((P.trimEnds a b).vertex j - source)).2 := by
  obtain ⟨frame, a, b, _, _, inside⟩ :=
    P.exists_trimEnds_quadrant_of_halfturn source genuine small
  let U : Set Plane := {z | 0 < (frame.symm (z - source)).1 ∧
    0 < (frame.symm (z - source)).2}
  have continuous : Continuous frame.symm := frame.symm.continuous_of_finiteDimensional
  have open_U : IsOpen U :=
    (isOpen_lt continuous_const ((continuous.comp (continuous_id.sub continuous_const)).fst)).inter
      (isOpen_lt continuous_const ((continuous.comp (continuous_id.sub continuous_const)).snd))
  have first_different : P.vertex 0 ≠ P.vertex (0 : Fin (n + 2)).succ :=
    (sub_ne_zero.mp first_nonzero).symm
  have last_different : P.vertex (Fin.last (n + 1)).castSucc ≠ P.vertex (Fin.last (n + 2)) :=
    (sub_ne_zero.mp last_nonzero).symm
  have first_in : AffineMap.lineMap (P.vertex 0) (P.vertex (0 : Fin (n + 2)).succ) a.val ∈ U := by
    have h : (P.trimEnds a b).vertex 0 ∈ U := inside 0
    rwa [P.trimEnds_start] at h
  have last_in : AffineMap.lineMap (P.vertex (Fin.last (n + 1)).castSucc)
      (P.vertex (Fin.last (n + 2))) b.val ∈ U := by
    have h : (P.trimEnds a b).vertex (Fin.last (n + 2)) ∈ U := inside (Fin.last (n + 2))
    rwa [P.trimEnds_last] at h
  obtain ⟨a', ha, start_in, start_avoids⟩ :=
    exists_open_parameter_avoids_points point open_U first_different a first_in
  obtain ⟨b', hb, end_in, end_avoids⟩ :=
    exists_open_parameter_avoids_points point open_U last_different b last_in
  refine ⟨frame, a', b', ha, hb, ?_, ?_, ?_⟩
  · intro i
    rw [P.trimEnds_start]
    exact start_avoids i
  · intro i
    rw [P.trimEnds_last]
    exact end_avoids i
  · intro j
    change (P.trimEnds a' b').vertex j ∈ U
    by_cases beginning : j.val = 0
    · rw [show j = 0 from Fin.ext beginning, P.trimEnds_start]
      exact start_in
    by_cases finish : j.val = n + 2
    · rw [show j = Fin.last (n + 2) from Fin.ext finish, P.trimEnds_last]
      exact end_in
    have member : (P.trimEnds a b).vertex j ∈ U := inside j
    rw [P.trimEnds_vertex_internal a' b' j (by omega) (by omega)]
    rwa [P.trimEnds_vertex_internal a b j (by omega) (by omega)] at member

end PolygonalChain
end Unfoldings
