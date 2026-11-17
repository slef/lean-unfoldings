module

public import Unfoldings.Roof.CompatibleTerminalExcision
public import Unfoldings.Roof.TerminalTruncation

/-! An actual incoming terminal segment and the fixed outer tail retain the whole cut germ. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexRoof C)
  {slopes : Set Plane} (compact : IsCompact slopes) (nonempty : slopes.Nonempty)
  {boundary : (frontier slopes).Nonempty} {a β : ℝ}
  (R : K.CompatiblePotentialRouting {f | K.normalSlope f ∈ slopes}
    (K.clippedExtension slopes compact nonempty) boundary a β)
  (no_boundary : ∀ f, K.normalSlope f ∉ frontier slopes)
  (level : ℝ)
  (higher : ∀ v, (K.clippedExtension slopes compact nonempty).height (K.projectedVertex v) < level)

include no_boundary higher in
/-- Retaining one genuine incoming original ray segment and every outer cut point
retains the exact whole original cut germ at the truncation junction. -/
theorem exists_terminal_junction_cut_germ (cuts : Set Plane) (included : cuts ⊆ R.carrier)
    (outer : R.carrier ∩ {p | level ≤ (K.clippedExtension slopes compact nonempty).height p} ⊆ cuts)
    (r : {v // v ∈ R.parents.roots}) {s : ℝ} (_nonnegative : 0 ≤ s)
    (before : s < R.terminalTime level r)
    (incoming : segment ℝ (R.exterior.ray (R.terminalIndex r) s) (R.terminalPoint level r) ⊆ cuts) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ z, dist z (R.terminalPoint level r) < ε →
      (z ∈ R.carrier ↔ z ∈ cuts) := by
  obtain ⟨δ, δpos, germ⟩ := K.exists_terminalRayCut_germ compact nonempty R no_boundary r
    (R.terminalTime_pos level higher r)
  refine ⟨min δ (R.terminalTime level r - s), lt_min δpos (sub_pos.mpr before), ?_⟩
  intro z near
  refine ⟨fun on_cut => ?_, fun member => included member⟩
  have ray_member := (germ z (near.trans_le (min_le_left _ _))).mp on_cut
  obtain ⟨u, at_z⟩ := ray_member
  have position : z = R.exterior.ray (R.terminalIndex r) u.val :=
    at_z.symm.trans (R.terminal_lineMap r u.val)
  by_cases after : R.terminalTime level r ≤ u.val
  · apply outer ⟨on_cut, ?_⟩
    change level ≤ (K.clippedExtension slopes compact nonempty).height z
    rw [position, R.exterior.height_ray _ u.property]
    have at_end := R.terminalPoint_level level higher r
    change (K.clippedExtension slopes compact nonempty).height
      (R.exterior.ray (R.terminalIndex r) (R.terminalTime level r)) = level at at_end
    rw [R.exterior.height_ray _ (R.terminalTime_pos level higher r).le] at at_end
    have rate : 0 ≤ R.exterior.rate (R.terminalIndex r) := (R.exterior.positive _).le
    nlinarith
  · have distance : dist z (R.terminalPoint level r) = |u.val - R.terminalTime level r| := by
      rw [position]
      change dist (R.exterior.ray (R.terminalIndex r) u.val)
        (R.exterior.ray (R.terminalIndex r) (R.terminalTime level r)) = _
      rw [dist_eq_norm]
      have difference : R.exterior.ray (R.terminalIndex r) u.val -
          R.exterior.ray (R.terminalIndex r) (R.terminalTime level r) =
          (u.val - R.terminalTime level r) •
            R.exterior.direction (R.exterior.slope (R.terminalIndex r)) := by
        simp only [SlopeEnvelope.ExteriorPlan.ray]
        module
      rw [difference, norm_smul, R.exterior.unit, mul_one, Real.norm_eq_abs]
    have close := near.trans_le (min_le_right δ (R.terminalTime level r - s))
    rw [distance, abs_sub_lt_iff] at close
    have from_start : s ≤ u.val := by linarith [close.2]
    have before_end : u.val ≤ R.terminalTime level r := (lt_of_not_ge after).le
    apply incoming
    rw [position, segment_eq_image_lineMap]
    let t := (u.val - s) / (R.terminalTime level r - s)
    have bounds : t ∈ Set.Icc (0 : ℝ) 1 :=
      ⟨div_nonneg (sub_nonneg.mpr from_start) (sub_pos.mpr before).le,
        (div_le_one (sub_pos.mpr before)).mpr (by linarith)⟩
    refine ⟨t, bounds, ?_⟩
    have parameter : t * (R.terminalTime level r - s) = u.val - s :=
      div_mul_cancel₀ _ (sub_pos.mpr before).ne'
    change AffineMap.lineMap (R.exterior.ray _ s) (R.exterior.ray _ _) t = _
    have index : s + t * (R.terminalTime level r - s) = u.val := by linarith
    calc
      _ = R.exterior.point (R.terminalIndex r) +
          (s + t * (R.terminalTime level r - s)) •
            R.exterior.direction (R.exterior.slope (R.terminalIndex r)) := by
        simp only [SlopeEnvelope.ExteriorPlan.ray, AffineMap.lineMap_apply_module']
        module
      _ = _ := congrArg (fun q : ℝ => R.exterior.point (R.terminalIndex r) +
        q • R.exterior.direction (R.exterior.slope (R.terminalIndex r))) index

end Unfoldings.ConvexRoof
