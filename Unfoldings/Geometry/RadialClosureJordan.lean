module

public import Unfoldings.Geometry.RadialClosureSegments
public import Unfoldings.Topology.PathJordanArc
public import Schoenflies.Polygonal

/-! Construct a genuine Jordan closure from source-radius ordering and one supporting half-plane. -/

@[expose] public section

noncomputable section

namespace Unfoldings.PolygonalChain

variable {n : ℕ} (P : PolygonalChain Plane n) (source : Plane)
  (radial : P.RadialFrom source 0)

include radial in
/-- All three added segments are actual straight connectors with proved intersection control. -/
theorem radial_halfplane_closure_jordan
    (initial : 0 < dist source (P.vertex 0))
    (progress : dist source (P.vertex 0) < dist source (P.vertex (Fin.last n)))
    (height : Plane →ₗ[ℝ] ℝ)
    (supported : ∀ z ∈ Set.range P.path, 0 ≤ height (z - source))
    (c : Plane) (outside : height (c - source) < 0)
    (outward : 0 < inner ℝ (P.vertex (Fin.last n) - source) (c - P.vertex (Fin.last n))) :
    Schoenflies.IsJordanCurve (Set.range P.path ∪
      ((segment ℝ (P.vertex (Fin.last n)) c ∪ segment ℝ c source) ∪
        segment ℝ source (P.vertex 0))) := by
  let a := P.vertex 0
  let b := P.vertex (Fin.last n)
  have a_member : a ∈ Set.range P.path := ⟨0, P.path.source⟩
  have b_member : b ∈ Set.range P.path := ⟨1, P.path.target⟩
  have bounds {z : Plane} (hz : z ∈ Set.range P.path) :
      dist source a ≤ dist source z ∧ dist source z ≤ dist source b :=
    P.path_radius_bounds source radial hz
  have source_ne_a : source ≠ a := by
    intro same
    have zero : dist source a = 0 := by rw [same, dist_self]
    linarith
  have b_ne_c : b ≠ c := by
    intro same
    change 0 < inner ℝ (b - source) (c - b) at outward
    rw [same, sub_self, inner_zero_right] at outward
    exact lt_irrefl 0 outward
  have c_ne_source : c ≠ source := by
    intro same
    rw [same, sub_self, map_zero] at outside
    exact lt_irrefl 0 outside
  have origin_meet {z : Plane} (hc : z ∈ segment ℝ source c)
      (nonnegative : 0 ≤ height (z - source)) : z = source := by
    have same := source_segments_inter height source z c nonnegative outside
    exact Set.mem_singleton_iff.mp ((Set.ext_iff.mp same z).mp
      ⟨right_mem_segment ℝ _ _, hc⟩)
  have end_meet {z : Plane} (hc : z ∈ segment ℝ b c) (hz : z ∈ Set.range P.path) : z = b := by
    have same := terminal_segment_inter_radial_disk source b c outward
    exact Set.mem_singleton_iff.mp ((Set.ext_iff.mp same z).mp ⟨hc, (bounds hz).2⟩)
  have start_meet {z : Plane} (hc : z ∈ segment ℝ source a)
      (hz : z ∈ Set.range P.path) : z = a := by
    have same := initial_segment_inter_radial_exterior source a
    exact Set.mem_singleton_iff.mp ((Set.ext_iff.mp same z).mp ⟨hc, (bounds hz).1⟩)
  have closing_first := (Schoenflies.isArcBetween_segment b_ne_c).concatenate
    (Schoenflies.isArcBetween_segment c_ne_source) (by
      intro z hb hc
      rw [segment_symm ℝ c source] at hc
      have same := source_terminal_segments_inter height source b c
        (supported b b_member) outside outward
      exact Set.mem_singleton_iff.mp ((Set.ext_iff.mp same z).mp ⟨hc, hb⟩))
  have closing := closing_first.concatenate (Schoenflies.isArcBetween_segment source_ne_a) (by
    intro z first last
    rcases first with hb | hc
    · have upper := dist_initial_segment_le source a last
      have same := terminal_segment_inter_radial_disk source b c outward
      have at_b : z = b := Set.mem_singleton_iff.mp
        ((Set.ext_iff.mp same z).mp ⟨hb, upper.trans progress.le⟩)
      rw [at_b] at upper
      exact False.elim (not_le_of_gt progress upper)
    · rw [segment_symm ℝ c source] at hc
      exact origin_meet hc (linear_nonnegative_on_initial_segment height source a
        (supported a a_member) last))
  obtain ⟨Q, injective, range_eq⟩ := P.exists_injective_radial_path source radial progress
  have arc : Schoenflies.IsArcBetween (Set.range P.path) a b := by
    rw [← range_eq]
    exact PlanarTopology.isArcBetween_of_injective_path Q injective
  apply Schoenflies.IsJordanCurve.of_two_arcs arc closing
  intro z hz member
  rcases member with (hb | hc) | ha
  · exact Or.inr (end_meet hb hz)
  · rw [segment_symm ℝ c source] at hc
    have same := origin_meet hc (supported z hz)
    have lower := (bounds hz).1
    rw [same, dist_self] at lower
    exact False.elim (not_le_of_gt initial lower)
  · exact Or.inl (start_meet ha hz)

end Unfoldings.PolygonalChain
