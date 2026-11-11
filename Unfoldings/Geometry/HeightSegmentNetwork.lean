module

public import Unfoldings.Geometry.CoalescingHeightGraphs
public import Unfoldings.Geometry.SegmentHeightUnique
public import Unfoldings.Topology.FiniteClosedActive
public import Mathlib.Analysis.Convex.Topology

/-! Height-parametrized paths on a finite forward-deterministic segment network coalesce. -/

@[expose] public section

noncomputable section

namespace Unfoldings

open Filter Topology

def complexDiagonalHeight : ℂ →ₗ[ℝ] ℝ := Complex.reCLM.toLinearMap + Complex.imCLM.toLinearMap

structure HeightSegmentNetwork (ι : Type*) where
  first : ι → ℂ
  last : ι → ℂ
  ascending : ∀ i, complexDiagonalHeight (first i) < complexDiagonalHeight (last i)
  forward_unique : ∀ i j (x : ℂ),
    x ∈ segment ℝ (first i) (last i) → x ≠ last i →
    x ∈ segment ℝ (first j) (last j) → x ≠ last j → i = j

namespace HeightSegmentNetwork

variable {ι : Type*} [Finite ι] (N : HeightSegmentNetwork ι)

def carrier : Set ℂ := ⋃ i, segment ℝ (N.first i) (N.last i)

theorem local_right_graph_unique (G H : MonotoneHeightGraph) {a b t : ℝ}
    (first_cover : ∀ h ∈ Set.Icc a b, G.point h ∈ N.carrier)
    (last_cover : ∀ h ∈ Set.Icc a b, H.point h ∈ N.carrier)
    (member : t ∈ Set.Ico a b) (same : G.coordinate t = H.coordinate t) :
    ∀ᶠ h in nhdsWithin t (Set.Ioi t), G.coordinate h = H.coordinate h := by
  have closed (i : ι) : IsClosed (segment ℝ (N.first i) (N.last i)) := by
    rw [segment_eq_image_lineMap]
    exact (isCompact_Icc.image AffineMap.lineMap_continuous).isClosed
  have active_first := finite_closed_cover_eventually_active
    (fun i => segment ℝ (N.first i) (N.last i)) closed G.point G.point_continuous t
  have active_last := finite_closed_cover_eventually_active
    (fun i => segment ℝ (N.first i) (N.last i)) closed H.point H.point_continuous t
  have same_point : G.point t = H.point t := by
    apply Complex.ext
    · exact same
    · change t - G.coordinate t = t - H.coordinate t
      rw [same]
  have near : ∀ᶠ h in 𝓝 t, h < b := Iio_mem_nhds member.2
  have before : ∀ᶠ h in nhdsWithin t (Set.Ioi t), h < b :=
    near.filter_mono nhdsWithin_le_nhds
  filter_upwards [active_first.filter_mono nhdsWithin_le_nhds,
    active_last.filter_mono nhdsWithin_le_nhds, before,
    self_mem_nhdsWithin (s := Set.Ioi t)] with h first_active last_active before after
  have in_range : h ∈ Set.Icc a b := ⟨member.1.trans after.le, before.le⟩
  obtain ⟨i, first⟩ := Set.mem_iUnion.mp (first_cover h in_range)
  obtain ⟨j, last⟩ := Set.mem_iUnion.mp (last_cover h in_range)
  have first_base := first_active i first
  have last_base : G.point t ∈ segment ℝ (N.first j) (N.last j) :=
    same_point.symm ▸ last_active j last
  have not_end (k : ι) (z : ℂ) (inside : z ∈ segment ℝ (N.first k) (N.last k))
      (later : t < complexDiagonalHeight z) : G.point t ≠ N.last k := by
    intro equal
    have upper := (linear_segment_bounds complexDiagonalHeight (N.ascending k).le inside).2
    have height : t = complexDiagonalHeight (N.last k) :=
      (G.point_height t).symm.trans (congrArg complexDiagonalHeight equal)
    linarith
  have first_later : t < complexDiagonalHeight (G.point h) := by
    change t < (G.point h).re + (G.point h).im
    rw [G.point_height]
    exact after
  have last_later : t < complexDiagonalHeight (H.point h) := by
    change t < (H.point h).re + (H.point h).im
    rw [H.point_height]
    exact after
  have equal_edges := N.forward_unique i j (G.point t) first_base
    (not_end i (G.point h) first first_later) last_base
    (not_end j (H.point h) last last_later)
  subst j
  have heights : complexDiagonalHeight (G.point h) = complexDiagonalHeight (H.point h) :=
    (G.point_height h).trans (H.point_height h).symm
  have points := point_eq_of_mem_segment_of_linear_eq complexDiagonalHeight (N.ascending i)
    first last heights
  exact congrArg Complex.re points

/-- Finite closed-edge activity and unique forward continuation imply equality of entire
later tails. This proves the path-coalescence condition rather than assuming it. -/
theorem graphs_coalesce (G H : MonotoneHeightGraph) {a b : ℝ}
    (first_cover : ∀ h ∈ Set.Icc a b, G.point h ∈ N.carrier)
    (last_cover : ∀ h ∈ Set.Icc a b, H.point h ∈ N.carrier) : G.CoalescesOn H a b := by
  let equal : Set ℝ := {h | G.coordinate h = H.coordinate h}
  have closed : IsClosed equal := isClosed_eq G.continuous H.continuous
  intro x member same y later
  have all : Set.Icc x b ⊆ equal := by
    apply (closed.inter isClosed_Icc).Icc_subset_of_forall_mem_nhdsWithin same
    intro t at_t
    exact N.local_right_graph_unique G H first_cover last_cover
      ⟨member.1.trans at_t.2.1, at_t.2.2⟩ at_t.1
  exact all later

end HeightSegmentNetwork
end Unfoldings
