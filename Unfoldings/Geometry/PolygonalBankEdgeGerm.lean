module

public import Unfoldings.Geometry.RadialRayEdgePoints
public import Unfoldings.Geometry.PolygonalBankTailGerm
public import Unfoldings.Geometry.SegmentInteriorDirections

/-! The actual bank germ at each strict finite edge point is its original direction line. -/

@[expose] public section

noncomputable section

open Filter Topology

namespace Unfoldings.PolygonalRay

variable {n : ℕ} (R : PolygonalRay ℂ n)

/-- No other original bank piece contributes to the germ at a strict finite edge point. -/
theorem eventually_mem_carrier_iff_segment (outward : R.Outward) (nonzero : R.direction ≠ 0)
    (genuine : ∀ i : Fin n, R.chain.vertex i.castSucc ≠ R.chain.vertex i.succ)
    (i : Fin n) (t : unitInterval) (bounds : 0 < t ∧ t < 1) :
    ∀ᶠ z in 𝓝 (R.chain.point i t), z ∈ R.carrier ↔
      z ∈ segment ℝ (R.chain.vertex i.castSucc) (R.chain.vertex i.succ) := by
  have no_source : ∀ᶠ z in 𝓝 (R.chain.point i t), z ∉ ({R.start} : Set ℂ) :=
    isClosed_singleton.isOpen_compl.mem_nhds (R.point_ne_start outward genuine i t bounds.1)
  have no_tail : ∀ᶠ z in 𝓝 (R.chain.point i t), z ∉ Set.range R.tail :=
    (R.isClosed_range_tail nonzero).isOpen_compl.mem_nhds
      (R.point_not_mem_tail outward genuine nonzero i t bounds.2)
  have no_other (j : Fin n) : ∀ᶠ z in 𝓝 (R.chain.point i t), j ≠ i →
      z ∉ segment ℝ (R.chain.vertex j.castSucc) (R.chain.vertex j.succ) := by
    by_cases different : j ≠ i
    · have closed : IsClosed (segment ℝ (R.chain.vertex j.castSucc)
          (R.chain.vertex j.succ)) := by
        rw [segment_eq_image_lineMap]
        exact (isCompact_Icc.image AffineMap.lineMap_continuous).isClosed
      have avoid : ∀ᶠ z in 𝓝 (R.chain.point i t),
          z ∉ segment ℝ (R.chain.vertex j.castSucc) (R.chain.vertex j.succ) :=
        closed.isOpen_compl.mem_nhds
          (R.point_not_mem_other_segment outward genuine i t bounds j different)
      exact avoid.mono (fun _ outside _ => outside)
    · exact Filter.Eventually.of_forall (fun _ impossible => (different impossible).elim)
  filter_upwards [no_source, no_tail, eventually_all.mpr no_other] with z first last other
  rw [carrier, R.chain.path_range_eq_segments]
  change z ∉ ({R.chain.vertex 0} : Set ℂ) at first
  simp only [Set.mem_union, first, last, false_or, or_false, Set.mem_iUnion]
  constructor
  · rintro ⟨j, member⟩
    by_cases same : j = i
    · simpa only [same] using member
    · exact (other j same member).elim
  · exact fun member => ⟨i, member⟩

/-- The full original forward and reverse edge rays, with their actual edge label, are
the exact bank direction model at every strict interior edge point. -/
theorem complexCarrierGerm_edge_point (outward : R.Outward) (nonzero : R.direction ≠ 0)
    (genuine : ∀ i : Fin n, R.chain.vertex i.castSucc ≠ R.chain.vertex i.succ)
    (i : Fin n) (t : unitInterval) (bounds : 0 < t ∧ t < 1) :
    R.complexCarrierGerm (R.chain.point i t) =
      nonnegativeRay (-R.chain.edge i) ∪ nonnegativeRay (R.chain.edge i) := by
  have isolated := R.eventually_mem_carrier_iff_segment outward nonzero genuine i t bounds
  have segment_model := eventually_mem_segment_iff_direction_line_normed
    (R.chain.vertex i.castSucc) (R.chain.vertex i.succ) (genuine i) t bounds
  have near : ∀ᶠ z in 𝓝 (R.chain.point i t), z ∈ R.carrier ↔
      z - R.chain.point i t ∈ nonnegativeRay (-R.chain.edge i) ∪
        nonnegativeRay (R.chain.edge i) := by
    filter_upwards [isolated, segment_model] with z pieces model
    rw [pieces, model, range_smul_eq_nonnegativeRays, Set.union_comm]
    rfl
  apply eq_of_local_homogeneous_models (R.chain.point i t)
    (fun v _r positive => R.mem_complexCarrierGerm_smul_iff _ v positive) _
    (R.eventually_mem_carrier_iff_complexGerm _) near
  intro v r positive
  simp only [Set.mem_union, mem_nonnegativeRay_smul_iff _ _ positive]

end Unfoldings.PolygonalRay
