module

public import Unfoldings.Topology.PathJordanArc
public import Unfoldings.Topology.ClosedJordanDomain

/-! Consecutive intersections of two graphs bound Jordan disks in disjoint horizontal slabs. -/

@[expose] public section

noncomputable section

namespace Unfoldings.PlanarTopology

/-- A graph in literal planar coordinates. -/
def graphPoint (f : ℝ → ℝ) (t : ℝ) : Plane := WithLp.toLp 2 ![t, f t]

theorem continuous_graphPoint {f : ℝ → ℝ} (hf : Continuous f) : Continuous (graphPoint f) := by
  apply (PiLp.continuous_toLp 2 (fun _ : Fin 2 => ℝ)).comp
  apply continuous_pi
  intro j
  fin_cases j
  · exact continuous_id
  · exact hf

/-- A continuous graph restricted to an ordered closed interval is an embedded arc. -/
theorem isArcBetween_graphPoint (f : ℝ → ℝ) (hf : Continuous f)
    {a b : ℝ} (ordered : a < b) :
    Schoenflies.IsArcBetween (graphPoint f '' Set.Icc a b) (graphPoint f a) (graphPoint f b) := by
  let time (s : unitInterval) := a + (b - a) * s.val
  let P : Path (graphPoint f a) (graphPoint f b) :=
    { toFun := fun s => graphPoint f (time s)
      continuous_toFun := (continuous_graphPoint hf).comp (by dsimp [time]; fun_prop)
      source' := by simp [time]
      target' := by simp [time] }
  have injective : Function.Injective P := by
    intro s t same
    have time_eq : time s = time t := congrArg (fun p : Plane => p 0) same
    have coeff : (b - a) * s.val = (b - a) * t.val :=
      add_left_cancel time_eq
    exact Subtype.ext (mul_left_cancel₀ (sub_ne_zero.mpr ordered.ne') coeff)
  have range_eq : Set.range P = graphPoint f '' Set.Icc a b := by
    ext p
    constructor
    · rintro ⟨s, rfl⟩
      refine ⟨time s, ?_, rfl⟩
      have ht := s.property
      change a ≤ a + (b - a) * s.val ∧ a + (b - a) * s.val ≤ b
      exact ⟨by linarith only [mul_nonneg (sub_nonneg.mpr ordered.le) ht.1],
        by linarith only [mul_le_mul_of_nonneg_left ht.2 (sub_nonneg.mpr ordered.le)]⟩
    · rintro ⟨t, ht, rfl⟩
      let s : unitInterval := ⟨(t - a) / (b - a),
        div_nonneg (sub_nonneg.mpr ht.1) (sub_nonneg.mpr ordered.le),
        (div_le_one (sub_pos.mpr ordered)).mpr (sub_le_sub_right ht.2 a)⟩
      refine ⟨s, congrArg (graphPoint f) ?_⟩
      change a + (b - a) * ((t - a) / (b - a)) = t
      rw [← mul_div_assoc, mul_div_cancel_left₀ _ (sub_ne_zero.mpr ordered.ne'), add_sub_cancel]
  rw [← range_eq]
  exact isArcBetween_of_injective_path P injective

/-- Between two consecutive graph intersections, the closed graph segments
form a Jordan boundary even if the same graphs meet at other times. -/
theorem isJordanCurve_two_graphs (f g : ℝ → ℝ) (hf : Continuous f) (hg : Continuous g)
    {a b : ℝ} (ordered : a < b) (start : f a = g a) (finish : f b = g b)
    (separated : ∀ t ∈ Set.Ioo a b, f t ≠ g t) :
    Schoenflies.IsJordanCurve
      (graphPoint f '' Set.Icc a b ∪ graphPoint g '' Set.Icc a b) := by
  have first := isArcBetween_graphPoint f hf ordered
  have last := isArcBetween_graphPoint g hg ordered
  have at_start : graphPoint f a = graphPoint g a := by simp [graphPoint, start]
  have at_finish : graphPoint f b = graphPoint g b := by simp [graphPoint, finish]
  rw [← at_start, ← at_finish] at last
  apply Schoenflies.IsJordanCurve.of_two_arcs first last.reverse
  rintro p ⟨s, hs, rfl⟩ ⟨t, _, same⟩
  have st : t = s := congrArg (fun p : Plane => p 0) same
  subst t
  have agree : g s = f s := congrArg (fun p : Plane => p 1) same
  rcases eq_or_lt_of_le hs.1 with at_a | after
  · exact Or.inl (congrArg (graphPoint f) at_a.symm)
  rcases eq_or_lt_of_le hs.2 with at_b | before
  · exact Or.inr (congrArg (graphPoint f) at_b)
  · exact ((separated s ⟨after, before⟩) agree.symm).elim

end Unfoldings.PlanarTopology
