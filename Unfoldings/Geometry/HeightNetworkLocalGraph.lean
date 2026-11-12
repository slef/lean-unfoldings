module

public import Unfoldings.Geometry.HeightSegmentNetwork
public import Unfoldings.Geometry.HeightGraphSplice

/-! Away from network vertices, an actual covered tail agrees locally with its edge graph. -/

@[expose] public section

noncomputable section

namespace Unfoldings

open Filter Topology

namespace MonotoneHeightGraph

theorem through_coordinate_of_mem_segment (p q : ℂ) (horizontal : p.re ≤ q.re)
    (vertical : p.im ≤ q.im) (genuine : 0 < q.re + q.im - (p.re + p.im))
    {z : ℂ} (member : z ∈ segment ℝ p q) :
    (through p q horizontal vertical genuine).coordinate (z.re + z.im) = z.re := by
  rw [segment_eq_image_lineMap] at member
  obtain ⟨s, _, rfl⟩ := member
  exact congrArg Complex.re (through_lineMap p q horizontal vertical genuine s)

end MonotoneHeightGraph

namespace HeightSegmentNetwork

variable {ι : Type*} [Finite ι] (N : HeightSegmentNetwork ι)

theorem graph_locally_on_segment (G : MonotoneHeightGraph) {a b h : ℝ}
    (cover : ∀ k ∈ Set.Icc a b, G.point k ∈ N.carrier) (inside : h ∈ Set.Ioo a b)
    (i : ι) (on_piece : G.point h ∈ segment ℝ (N.first i) (N.last i))
    (not_vertex : ∀ j, G.point h ≠ N.last j) :
    ∀ᶠ k in 𝓝 h, G.point k ∈ segment ℝ (N.first i) (N.last i) := by
  have closed (j : ι) : IsClosed (segment ℝ (N.first j) (N.last j)) := by
    rw [segment_eq_image_lineMap]
    exact (isCompact_Icc.image AffineMap.lineMap_continuous).isClosed
  have active := finite_closed_cover_eventually_active
    (fun j => segment ℝ (N.first j) (N.last j)) closed G.point G.point_continuous h
  have near : ∀ᶠ k in 𝓝 h, k ∈ Set.Ioo a b := isOpen_Ioo.mem_nhds inside
  filter_upwards [active, near] with k at_base in_range
  obtain ⟨j, member⟩ := Set.mem_iUnion.mp (cover k ⟨in_range.1.le, in_range.2.le⟩)
  have same := N.forward_unique i j (G.point h) on_piece (not_vertex i)
    (at_base j member) (not_vertex j)
  exact same.symm ▸ member

theorem graph_locally_eq_through (G : MonotoneHeightGraph) {a b h : ℝ}
    (cover : ∀ k ∈ Set.Icc a b, G.point k ∈ N.carrier) (inside : h ∈ Set.Ioo a b)
    (i : ι) (on_piece : G.point h ∈ segment ℝ (N.first i) (N.last i))
    (not_vertex : ∀ j, G.point h ≠ N.last j)
    (horizontal : (N.first i).re ≤ (N.last i).re)
    (vertical : (N.first i).im ≤ (N.last i).im) :
    let H := MonotoneHeightGraph.through (N.first i) (N.last i) horizontal vertical
      (sub_pos.mpr (N.ascending i))
    ∃ c d, h ∈ Set.Ioo c d ∧ Set.EqOn G.coordinate H.coordinate (Set.Ioo c d) := by
  have on_edge := N.graph_locally_on_segment G cover inside i on_piece not_vertex
  have equal : ∀ᶠ k in 𝓝 h, G.coordinate k =
      (MonotoneHeightGraph.through (N.first i) (N.last i) horizontal vertical
        (sub_pos.mpr (N.ascending i))).coordinate k := by
    filter_upwards [on_edge] with k member
    have coordinate := MonotoneHeightGraph.through_coordinate_of_mem_segment (N.first i)
      (N.last i) horizontal vertical (sub_pos.mpr (N.ascending i)) member
    rw [G.point_height] at coordinate
    exact coordinate.symm
  obtain ⟨r, positive, near⟩ := Metric.eventually_nhds_iff.mp equal
  refine ⟨h - r, h + r, ⟨by linarith, by linarith⟩, fun k member => near ?_⟩
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith [member.1, member.2]

end HeightSegmentNetwork
end Unfoldings
