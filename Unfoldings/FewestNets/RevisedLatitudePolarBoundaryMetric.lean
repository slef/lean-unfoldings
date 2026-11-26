module

public import Unfoldings.FewestNets.RevisedLatitudeSelectorBoundary
public import Unfoldings.FewestNets.SphericalSelectorMetric

/-! Verify the literal sides and corners meet the revised per-selector counting budgets. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FewestNets.RevisedLatitudeGrid

open Real Cap InnerProductGeometry SphericalSelectorBoundary
open AcuteLatitudeGrid (polarFrame polarRadius)

private theorem sum_endpointFactors_of_permutation {J : Type*} [Fintype J]
    (L : ℝ) (corner : J → ℝ) (step : Equiv.Perm J) :
    (∑ p : J × Bool, L / (sin L * sin (min (corner (if p.2 then step p.1 else p.1)) (π / 2)))) / π =
      ∑ j : J, (2 * L / (π * sin L)) / sin (min (corner j) (π / 2)) := by
  let factor (j : J) := L / (sin L * sin (min (corner j) (π / 2)))
  change (∑ p : J × Bool, factor (if p.2 then step p.1 else p.1)) / π = _
  rw [Fintype.sum_prod_type]
  simp only [Fintype.sum_bool, Bool.false_eq_true, ite_false, ite_true]
  rw [Finset.sum_add_distrib, Equiv.sum_comp step factor, ← Finset.sum_add_distrib, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j _
  simp only [factor, div_eq_mul_inv, mul_inv]
  ring

variable {a : ℝ} (positive : 0 < a) (small : a ≤ π / 6)

/-- Orthogonal coordinates preserve the length of each polar side. -/
theorem polarSideEndpoint_length (pole : Fin 2) (j : Fin (rowSize a 0)) :
    angle (polarSideEndpoint pole j false) (polarSideEndpoint pole j true) = polarSideLength j :=
  (selectorFrame (a := a) (.inl pole)).symm.toLinearIsometry.angle_map _ _

include positive small in
private theorem polarSlopeVertex_mod (j : ℕ) :
    polarSlopeVertex a (j % rowSize a 0) = polarSlopeVertex a j := by
  let k := rowSize a 0
  have sides : 3 ≤ k := by have := polar_rows_ge_six positive small; dsimp [k]; omega
  have periodic (i : ℕ) : polarSlopeVertex a (i + k) = polarSlopeVertex a i :=
    regularRingVertex_add_sideCount polarFrame sides (tan (polarRadius a)) i
  have periods (n q : ℕ) : polarSlopeVertex a (n + k * q) = polarSlopeVertex a n := by
    induction q with
    | zero => simp only [Nat.mul_zero, Nat.add_zero]
    | succ q ih => rw [Nat.mul_succ, ← Nat.add_assoc, periodic, ih]
  exact (periods (j % k) (j / k)).symm.trans (congrArg (polarSlopeVertex a) (Nat.mod_add_div j k))

include positive small in
private theorem polarSlopeVertex_injective :
    Function.Injective (fun j : Fin (rowSize a 0) => polarSlopeVertex a j.val) := by
  intro i j equal
  let k := rowSize a 0
  have npos : 0 < k := rowSize_pos positive small (Nat.zero_le _)
  have kpos : (0 : ℝ) < k := Nat.cast_pos.mpr npos
  have step_pos : 0 < π / (k : ℝ) := div_pos pi_pos kpos
  have different {u v : Fin k} (order : u < v) :
      polarSlopeVertex a u.val ≠ polarSlopeVertex a v.val := by
    have strict : (u.val : ℝ) < v.val := by exact_mod_cast order
    have to_last : (v.val : ℝ) < k := by exact_mod_cast v.isLt
    have head : (0 : ℝ) ≤ u.val := Nat.cast_nonneg _
    have cycle : (k : ℝ) * (π / (k : ℝ)) = π := by field_simp [kpos.ne']
    have swing : ((v.val : ℝ) - u.val) * (π / (k : ℝ)) < π := by
      have diff : (v.val : ℝ) - u.val < (k : ℝ) := by linarith only [to_last, head]
      exact (mul_lt_mul_of_pos_right diff step_pos).trans_eq cycle
    have sin_pos := sin_pos_of_pos_of_lt_pi (mul_pos (sub_pos.mpr strict) step_pos) swing
    have d := regularRingVertex_dist_eq polarFrame k u.val v.val
      (tan_polarRadius_bounds positive small).1.le
    change dist (polarSlopeVertex a u.val) (polarSlopeVertex a v.val) = _ at d
    intro same
    rw [same, dist_self, abs_of_pos sin_pos] at d
    exact (mul_pos (mul_pos (by norm_num) (tan_polarRadius_bounds positive small).1) sin_pos).ne'
      d.symm
  rcases lt_trichotomy i j with before | same | after
  · exact (different before equal).elim
  · exact same
  · exact (different after equal.symm).elim

include positive small in
private theorem polarSideEndpoint_true_eq_next (pole : Fin 2) (j : Fin (rowSize a 0)) :
    polarSideEndpoint pole j true =
      polarSideEndpoint pole (finRotate (rowSize a 0) j) false := by
  let k := rowSize a 0
  have next_val : (finRotate k j).val = (j.val + 1) % k := by
    rw [finRotate_apply, Fin.val_add, Fin.val_one', Nat.add_mod_mod]
  unfold polarSideEndpoint
  rw [show (if true then j.val + 1 else j.val) = j.val + 1 from rfl,
    show (if false then (finRotate k j).val + 1 else (finRotate k j).val) =
      (finRotate k j).val from rfl, next_val, polarSlopeVertex_mod positive small]

include positive small in
private theorem polarCornerAngle_eq_consecutive (pole : Fin 2) (j : Fin (rowSize a 0)) :
    polarCornerAngle j =
      angle (minorArcTangent (polarSideEndpoint pole j true) (polarSideEndpoint pole j false))
        (minorArcTangent (polarSideEndpoint pole j true)
          (polarSideEndpoint pole (finRotate (rowSize a 0) j) true)) := by
  let k := rowSize a 0
  let T := (selectorFrame (a := a) (.inl pole)).symm
  have next_val : (finRotate k j).val = (j.val + 1) % k := by
    rw [finRotate_apply, Fin.val_add, Fin.val_one', Nat.add_mod_mod]
  have next_corner : polarSlopeVertex a ((finRotate k j).val + 1) =
      polarSlopeVertex a (j.val + 2) := by
    calc
      _ = polarSlopeVertex a (((finRotate k j).val + 1) % k) :=
        (polarSlopeVertex_mod positive small _).symm
      _ = polarSlopeVertex a ((j.val + 1 + 1) % k) := by rw [next_val, Nat.mod_add_mod]
      _ = _ := polarSlopeVertex_mod positive small _
  have angle_map (x y : Space) : angle (T x) (T y) = angle x y :=
    T.toLinearIsometry.angle_map _ _
  have tangent_map (x y : Space) :
      T (minorArcTangent x y) = minorArcTangent (T x) (T y) := by
    simp only [minorArcTangent, map_sub, map_smul, angle_map]
  change _ = angle
    (minorArcTangent (T (gnomonicNormal (polarSlopeVertex a (j.val + 1))))
      (T (gnomonicNormal (polarSlopeVertex a j.val))))
    (minorArcTangent (T (gnomonicNormal (polarSlopeVertex a (j.val + 1))))
      (T (gnomonicNormal (polarSlopeVertex a ((finRotate k j).val + 1)))))
  rw [next_corner, ← tangent_map, ← tangent_map, angle_map]
  rfl

/-- Each endpoint of a polar side uses the corner at its actual ring vertex. -/
def polarEndpointCorner {a : ℝ} (j : Fin (rowSize a 0)) (b : Bool) : ℝ :=
  polarCornerAngle (if b then j else (finRotate (rowSize a 0)).symm j)

include positive small in
/-- Every polar corner is positive, including both sides' names for the wrap vertex. -/
theorem polarEndpointCorner_pos (j : Fin (rowSize a 0)) (b : Bool) :
    0 < polarEndpointCorner j b := by
  unfold polarEndpointCorner
  let i := if b then j else (finRotate (rowSize a 0)).symm j
  change 0 < polarCornerAngle i
  have lower := polar_corner_capped_sine positive small i
  by_contra! upper
  have zero : polarCornerAngle i = 0 := upper.antisymm (angle_nonneg _ _)
  rw [zero, min_eq_left pi_div_two_pos.le, sin_zero] at lower
  norm_num at lower

include positive small in
/-- The only incidences are consecutive sides of the ring, and their
angle is the actual polar corner. -/
theorem polarEndpointCorner_incident (pole : Fin 2) {j k : Fin (rowSize a 0)} {b c : Bool}
    (different : j ≠ k) (common : polarSideEndpoint pole j b = polarSideEndpoint pole k c) :
    polarEndpointCorner j b ≤
      angle (minorArcTangent (polarSideEndpoint pole j b) (polarSideEndpoint pole j (!b)))
        (minorArcTangent (polarSideEndpoint pole k c) (polarSideEndpoint pole k (!c))) := by
  let step := finRotate (rowSize a 0)
  have injective : Function.Injective (fun j => polarSideEndpoint pole j false) :=
    ((selectorFrame (a := a) (.inl pole)).symm.injective.comp gnomonicNormal_injective).comp
      (polarSlopeVertex_injective positive small)
  have forward := polarSideEndpoint_true_eq_next positive small pole
  cases b <;> cases c
  · exact (different (injective common)).elim
  · have same : j = step k := injective (common.trans (forward k))
    subst j
    change polarCornerAngle (step.symm (step k)) ≤
      angle (minorArcTangent (polarSideEndpoint pole (step k) false)
        (polarSideEndpoint pole (step k) true))
        (minorArcTangent (polarSideEndpoint pole k true) (polarSideEndpoint pole k false))
    rw [step.symm_apply_apply, ← forward k, angle_comm]
    exact (polarCornerAngle_eq_consecutive positive small pole k).le
  · have same : step j = k := injective ((forward j).symm.trans common)
    subst k
    change polarCornerAngle j ≤
      angle (minorArcTangent (polarSideEndpoint pole j true) (polarSideEndpoint pole j false))
        (minorArcTangent (polarSideEndpoint pole (step j) false)
          (polarSideEndpoint pole (step j) true))
    rw [← forward j]
    exact (polarCornerAngle_eq_consecutive positive small pole j).le
  · rw [forward, forward] at common
    exact (different (step.injective (injective common))).elim

private theorem polarEndpoint_arc_eq (pole : Fin 2) (j : Fin (rowSize a 0)) :
    networkEdge (polarSideEndpoint pole) j = polarSide pole j := by
  let T := selectorFrame (a := a) (.inl pole)
  have eq : T '' networkEdge (polarSideEndpoint pole) j = T '' polarSide pole j := by
    rw [polarSide_chart, networkEdge, SpatialRotation.image_closedMinorArc_linearIsometry]
    simp only [polarSideEndpoint, T, Bool.false_eq_true, ite_false, ite_true,
      LinearIsometryEquiv.apply_symm_apply]
  ext x
  exact ⟨fun h => T.injective.mem_set_image.mp (eq ▸ Set.mem_image_of_mem T h),
    fun h => T.injective.mem_set_image.mp (eq.symm ▸ Set.mem_image_of_mem T h)⟩

include positive small in
/-- The separation bound applies to every nonincident pair of actual polar sides. -/
theorem polarEndpoint_separated (pole : Fin 2) {j k : Fin (rowSize a 0)} (different : j ≠ k)
    (nonincident : ∀ b c, polarSideEndpoint pole j b ≠ polarSideEndpoint pole k c)
    {x y : Space} (hx : x ∈ networkEdge (polarSideEndpoint pole) j)
    (hy : y ∈ networkEdge (polarSideEndpoint pole) k) :
    polarSideCutoff a ≤ angle x y := by
  let n := rowSize a 0
  have next_val (i : Fin n) : (finRotate n i).val = (i.val + 1) % n := by
    rw [finRotate_apply, Fin.val_add, Fin.val_one', Nat.add_mod_mod]
  have ordered {i j : Fin n} (before : i < j)
      (separate : ∀ b c, polarSideEndpoint pole i b ≠ polarSideEndpoint pole j c)
      {u v : Space} (hu : u ∈ polarSide pole i) (hv : v ∈ polarSide pole j) :
      polarSideCutoff a ≤ angle u v := by
    have upcoming : i.val + 2 ≤ j.val := by
      by_contra! near
      have same : i.val + 1 = j.val := by omega
      have after_i : finRotate n i = j := by
        apply Fin.ext
        rw [next_val, same, Nat.mod_eq_of_lt j.isLt]
      exact separate true false ((polarSideEndpoint_true_eq_next positive small pole i).trans
        (congrArg (fun k => polarSideEndpoint pole k false) after_i))
    have wrap : j.val + 2 ≤ i.val + n := by
      by_contra! near
      have last : j.val + 1 = n := by omega
      have first : i.val = 0 := by omega
      have after_j : finRotate n j = i := by
        apply Fin.ext
        rw [next_val, last, Nat.mod_self, first]
      exact separate false true (((polarSideEndpoint_true_eq_next positive small pole j).trans
        (congrArg (fun k => polarSideEndpoint pole k false) after_j)).symm)
    exact polarSideCutoff_le_angle_of_nonincident positive small pole i j upcoming wrap hu hv
  rw [polarEndpoint_arc_eq] at hx hy
  rcases lt_or_gt_of_ne different with order | order
  · exact ordered order nonincident hx hy
  · rw [angle_comm]
    exact ordered order (fun b c => (nonincident c b).symm) hy hx


/-- The polar selector's sides and the actual longest side give the
separation and endpoint data for the sharp crossing bounds. -/
def polarSelectorMetric (pole : Fin 2) (longest : Fin (rowSize a 0))
    (maximum : ∀ j : Fin (rowSize a 0), polarSideLength j ≤ polarSideLength longest) :
    MetricData (polarSelectorBoundary positive small pole) where
  longest := polarSideLength longest
  longest_pos := polarSideLength_pos positive small longest
  longest_small := by linarith only [polarSideLength_lt positive small longest, pi_gt_d2]
  side_pos := fun j => (polarSideEndpoint_length pole j).symm ▸ polarSideLength_pos positive small j
  side_le := fun j => (polarSideEndpoint_length pole j).symm ▸ maximum j
  separation := polarSideCutoff a
  separation_pos := (polarSideCutoff_bounds positive small).1
  separation_small := (polarSideCutoff_bounds positive small).2.le.trans (by norm_num)
  separated := by
    intro i j distinct disjoint x hx y hy
    exact polarEndpoint_separated positive small pole distinct disjoint hx hy
  corner := polarEndpointCorner
  corner_pos := polarEndpointCorner_pos positive small
  incident := by
    intro i j b c distinct shared
    exact polarEndpointCorner_incident positive small pole distinct shared

include positive small in
/-- The crossing budget of either actual polar selector is at most 0.640 times
its ring size, using both endpoint factors and the full perimeter. -/
theorem exists_polarSelectorMetric_crossingBudget_le (pole : Fin 2) :
    ∃ M : MetricData (polarSelectorBoundary positive small pole),
      M.crossingBudget ≤ 0.640 * (rowSize a 0 : ℝ) := by
  obtain ⟨best, maximum, bound⟩ := polar_crossing_cutoff_le positive small
  let M := polarSelectorMetric positive small pole best maximum
  let L := polarSideLength best
  let step := finRotate (rowSize a 0)
  refine ⟨M, ?_⟩
  have per : (∑ j : Fin (rowSize a 0),
      angle (polarSideEndpoint pole j false) (polarSideEndpoint pole j true)) = polarPerimeter a :=
    Finset.sum_congr rfl (fun j _ => polarSideEndpoint_length pole j)
  have corner (p : Fin (rowSize a 0) × Bool) :
      polarEndpointCorner p.1 p.2 =
        (polarCornerAngle ∘ step.symm) (if p.2 then step p.1 else p.1) := by
    rcases p with ⟨j, b⟩
    cases b
    · rfl
    · change polarCornerAngle j = polarCornerAngle (step.symm (step j))
      rw [step.symm_apply_apply]
  have sum := sum_endpointFactors_of_permutation L (polarCornerAngle ∘ step.symm) step
  have reindex :
      (∑ j : Fin (rowSize a 0), (2 * L / (π * sin L)) /
        sin (min ((polarCornerAngle ∘ step.symm) j) (π / 2))) =
      ∑ j : Fin (rowSize a 0), (2 * L / (π * sin L)) /
        sin (min (polarCornerAngle j) (π / 2)) :=
    Equiv.sum_comp step.symm (fun j => (2 * L / (π * sin L)) /
      sin (min (polarCornerAngle j) (π / 2)))
  change max
    ((∑ p : Fin (rowSize a 0) × Bool, L / (sin L *
      sin (min (polarEndpointCorner p.1 p.2) (π / 2)))) / π)
    ((∑ j : Fin (rowSize a 0), angle (polarSideEndpoint pole j false) (polarSideEndpoint pole j true)) /
      (π * polarSideCutoff a)) ≤ _
  simp only [corner, sum, reindex, per]
  exact bound

end Unfoldings.FewestNets.RevisedLatitudeGrid
