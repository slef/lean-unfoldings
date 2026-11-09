module

public import Unfoldings.Path.Chart
public import Mathlib.Topology.Order.IntermediateValue

/-!
# Geodesic continuation through Euclidean charts

In a chart, agreement at the start and one later interior parameter determines
the other endpoint of a geodesic subpath. Continuous induction propagates an
initial shared interval along a path with Euclidean charts at every interior
time. The endpoints themselves need no chart.
-/

@[expose] public section

open Topology

namespace Path

variable {X : Type*} [EMetricSpace X]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [StrictConvexSpace ℝ E]
  {a b c d : X} {p : Path a b} {q : Path c d}
  {D : Set X} {U : Set E}

/-- Two chart-straight subpaths agreeing at their start and one later interior
parameter have the same target. No target equality is assumed. -/
theorem IsGeodesic.chart_subpath_target_eq (geodesic : p.IsGeodesic)
    (other : q.IsGeodesic) (chart : D ≃ᵢ U) {r t : unitInterval} (ordered : r < t)
    (inside : ∀ u ∈ Set.Icc r t, p u ∈ D)
    (other_inside : ∀ u ∈ Set.Icc r t, q u ∈ D)
    (v : unitInterval) (positive : 0 < v) (start : p r = q r)
    (middle : p (intervalParam r t v) = q (intervalParam r t v)) : p t = q t := by
  have coordinates {x y : X} (hx : x ∈ D) (hy : y ∈ D) (equal : x = y) :
      (chart ⟨x, hx⟩).val = (chart ⟨y, hy⟩).val :=
    congrArg (fun z : D => (chart z).val) (Subtype.ext equal)
  have first := coordinates (inside r ⟨le_rfl, ordered.le⟩)
    (other_inside r ⟨le_rfl, ordered.le⟩) start
  have between := coordinates (inside _ (intervalParam_mem_Icc ordered.le v))
    (other_inside _ (intervalParam_mem_Icc ordered.le v)) middle
  have line := (geodesic.chart_subpath_eq_lineMap chart ordered.le inside v).symm.trans
    (between.trans (other.chart_subpath_eq_lineMap chart ordered.le other_inside v))
  rw [← first, AffineMap.lineMap_apply_module', AffineMap.lineMap_apply_module'] at line
  have scaled := add_right_cancel line
  have nonzero : (v : ℝ) ≠ 0 := (show (0 : ℝ) < (v : ℝ) from positive).ne'
  have endpoints := sub_left_inj.mp (smul_right_injective E nonzero scaled)
  exact congrArg Subtype.val (chart.injective (Subtype.ext endpoints))

/-- A common initial germ has a unique continuation along Euclidean points.
The two paths may have different endpoint types; equality is pointwise. -/
theorem IsGeodesic.eq_of_initial_interval (geodesic : p.IsGeodesic) (other : q.IsGeodesic)
    (initial : ∃ ε : unitInterval, 0 < ε ∧ ∀ t ≤ ε, p t = q t)
    (charts : ∀ t ∈ Set.Ioo (0 : unitInterval) 1,
      ∃ D : Set X, ∃ U : Set E, IsOpen D ∧ p t ∈ D ∧ Nonempty (D ≃ᵢ U)) :
    ∀ t, p t = q t := by
  obtain ⟨ε, positive, initial⟩ := initial
  let S : Set unitInterval := {t | p t = q t}
  have closed : IsClosed S := isClosed_eq p.continuous q.continuous
  have full : Set.Icc ε (1 : unitInterval) ⊆ S := by
    apply (closed.inter isClosed_Icc).Icc_subset_of_forall_mem_nhdsGT_of_Icc_subset
      (initial ε le_rfl)
    intro t ht agreement
    have time_positive : (0 : unitInterval) < t := positive.trans_le ht.1
    have shared : p t = q t := agreement ⟨ht.1, le_rfl⟩
    obtain ⟨D, U, open_D, at_t, ⟨chart⟩⟩ := charts t ⟨time_positive, ht.2⟩
    have at_q : q t ∈ D := shared ▸ at_t
    have near : (p ⁻¹' D) ∩ (q ⁻¹' D) ∈ 𝓝 t :=
      ((open_D.preimage p.continuous).inter (open_D.preimage q.continuous)).mem_nhds
        ⟨at_t, at_q⟩
    obtain ⟨l, h, ⟨lt, th⟩, inside⟩ :=
      (mem_nhds_iff_exists_Ioo_subset' ⟨0, time_positive⟩ ⟨1, ht.2⟩).mp near
    obtain ⟨r, lr, rt⟩ := exists_between lt
    have start : p r = q r := by
      rcases le_total r ε with before | after
      · exact initial r before
      · exact agreement ⟨after, rt.le⟩
    apply (mem_nhdsGT_iff_exists_Ioo_subset' th).mpr
    refine ⟨h, th, ?_⟩
    intro u hu
    have order : r < u := rt.trans hu.1
    have p_inside : ∀ v ∈ Set.Icc r u, p v ∈ D := fun v hv =>
      (inside ⟨lr.trans_le hv.1, hv.2.trans_lt hu.2⟩).1
    have q_inside : ∀ v ∈ Set.Icc r u, q v ∈ D := fun v hv =>
      (inside ⟨lr.trans_le hv.1, hv.2.trans_lt hu.2⟩).2
    let v := intervalFraction r u t order ⟨rt.le, hu.1.le⟩
    have v_positive : (0 : unitInterval) < v :=
      intervalFraction_pos r u t order ⟨rt.le, hu.1.le⟩ rt
    have middle : p (intervalParam r u v) = q (intervalParam r u v) := by
      rw [show intervalParam r u v = t from
        intervalParam_fraction r u t order ⟨rt.le, hu.1.le⟩]
      exact shared
    exact geodesic.chart_subpath_target_eq other chart order p_inside q_inside
      v v_positive start middle
  intro t
  rcases le_total t ε with before | after
  · exact initial t before
  · exact full ⟨after, t.property.2⟩

end Path
