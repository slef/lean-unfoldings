module

public import Unfoldings.Metric.Polygonal
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Analysis.Normed.Group.Bounded
public import Mathlib.Topology.UniformSpace.UniformApproximation

/-!
# Intrinsic topology of radially accessible regions

If every proper radial contraction lands in the interior, boundedness makes
the intrinsic polygonal topology agree with the ambient topology, including
at the boundary. Radial contraction supplies the continuous approximations;
their intrinsic errors are exactly their Euclidean radial distances.
-/

@[expose] public section

open scoped ENNReal Topology
open Filter

noncomputable section

namespace Unfoldings.PolygonalPoint

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {s : Set E} (star : StarConvex ℝ (0 : E) s)

def radialPoint (t : unitInterval) (x : PolygonalPoint s) : PolygonalPoint s :=
  ⟨(t : ℝ) • x.val, star.smul_mem x.property t.property.1 t.property.2⟩

theorem radial_edist (t : unitInterval) (x : PolygonalPoint s) :
    edist x (radialPoint star t x) =
      ENNReal.ofReal ((1 - (t : ℝ)) * ‖x.val‖) := by
  have radial_mem : (t : ℝ) • x.val ∈ segment ℝ (0 : E) x.val := by
    simpa only [AffineMap.lineMap_apply_module', sub_zero, add_zero] using
      lineMap_mem_segment ℝ (0 : E) x.val t.property
  have included : segment ℝ x.val ((t : ℝ) • x.val) ⊆ s :=
    ((convex_segment (0 : E) x.val).segment_subset
      (right_mem_segment ℝ _ _) radial_mem).trans (star.segment_subset x.property)
  rw [edist_eq_of_segment included]
  change edist x.val ((t : ℝ) • x.val) = _
  rw [edist_dist, dist_eq_norm]
  have difference : x.val - (t : ℝ) • x.val = (1 - (t : ℝ)) • x.val := by
    rw [sub_smul, one_smul]
  rw [difference, norm_smul, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr t.property.2)]

def radialApproximation (n : ℕ) : unitInterval :=
  ⟨(n : ℝ) / (n + 1), div_nonneg (Nat.cast_nonneg n) (by positivity),
    (div_le_one (by positivity)).mpr (by linarith)⟩

theorem radialApproximation_lt_one (n : ℕ) : radialApproximation n < 1 := by
  change (n : ℝ) / (n + 1) < 1
  exact (div_lt_one (by positivity)).mpr (by linarith)

theorem tendsto_radialApproximation :
    Tendsto (fun n => (radialApproximation n : ℝ)) atTop (𝓝 1) :=
  tendsto_natCast_div_add_atTop 1

variable (radial_interior : ∀ x ∈ s, ∀ t : unitInterval, t < 1 →
  (t : ℝ) • x ∈ interior s)

include star radial_interior

theorem continuous_radialPoint (t : unitInterval) (before : t < 1) :
    Continuous (fun x : s => radialPoint star t (ofSubtype x)) := by
  let into (x : s) : interior s :=
    ⟨(t : ℝ) • x.val, radial_interior x.val x.property t before⟩
  have continuous_into : Continuous into :=
    (continuous_const.smul continuous_subtype_val).subtype_mk _
  exact (inclusion_lipschitz (s := interior s) (t := s) interior_subset).continuous.comp
    ((continuous_ofSubtype isOpen_interior).comp continuous_into)

theorem continuous_ofSubtype_of_radial_interior (bounded : Bornology.IsBounded s) :
    Continuous (ofSubtype (s := s)) := by
  obtain ⟨B, positive, bound⟩ := bounded.exists_pos_norm_le
  have limit : Tendsto (fun n => (1 - (radialApproximation n : ℝ)) * B) atTop (𝓝 0) := by
    simpa only [sub_self, zero_mul] using
      ((tendsto_const_nhds (x := (1 : ℝ))).sub tendsto_radialApproximation).mul_const B
  have uniform : TendstoUniformly
      (fun n (x : s) => radialPoint star (radialApproximation n) (ofSubtype x))
      ofSubtype atTop := by
    apply EMetric.tendstoUniformly_iff.mpr
    intro ε hε
    obtain ⟨δ, _nonnegative, hδ, below⟩ := ENNReal.lt_iff_exists_real_btwn.mp hε
    have eventually_small := (tendsto_order.mp limit).2 δ (ENNReal.ofReal_pos.mp hδ)
    filter_upwards [eventually_small] with n small x
    rw [radial_edist]
    apply lt_of_le_of_lt _ below
    apply ENNReal.ofReal_le_ofReal
    exact (mul_le_mul_of_nonneg_left (bound x.val x.property)
      (sub_nonneg.mpr (radialApproximation n).property.2)).trans small.le
  exact uniform.continuous (Filter.Eventually.frequently (Filter.Eventually.of_forall fun n =>
    continuous_radialPoint star radial_interior _ (radialApproximation_lt_one n)))

def radialHomeomorph (bounded : Bornology.IsBounded s) : PolygonalPoint s ≃ₜ s where
  toFun := toSubtype
  invFun := ofSubtype
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := continuous_toSubtype
  continuous_invFun := continuous_ofSubtype_of_radial_interior star radial_interior bounded

end Unfoldings.PolygonalPoint
