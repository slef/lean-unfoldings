module

public import Unfoldings.Metric.BankPairChartSteps

/-! Fill a plane disk using the inverse charts on its two closed half-disks. -/

@[expose] public section

noncomputable section

open scoped ENNReal

namespace Unfoldings.MetricGluing.BankPairChart

variable {I : Type*} {X : I → Type*} [∀ i, EMetricSpace (X i)]
  {a : Bool → Total X} {R : ℝ} (C : BankPairChart X a R)
  (glue : Total X → Total X → Prop) {r : ℝ} (small : r ≤ R)

/-- Invert the chosen original chart on the corresponding closed half-disk. -/
def patch (side : Bool) (z : bankHalfDisk side r) : Total X :=
  C.tagged side ((C.chart side).symm
    ⟨z.val, Metric.ball_subset_ball small z.property.1, z.property.2⟩)

@[simp] theorem coordinates_patch (side : Bool) (z : bankHalfDisk side r) :
    C.coordinates (C.patch small side z) = z.val := by
  unfold patch
  rw [C.coordinates_tagged, (C.chart side).apply_symm_apply]

/-- Fill the open disk through the two original bank charts. -/
def fill (z : Metric.ball (0 : ℂ) r) : Realization X glue :=
  if hi : 0 ≤ z.val.im then point X glue (C.patch small false ⟨z.val, z.property, hi⟩)
  else point X glue (C.patch small true ⟨z.val, z.property, (lt_of_not_ge hi).le⟩)

theorem fill_upper (z : bankHalfDisk false r) :
    C.fill glue small ⟨z.val, z.property.1⟩ = point X glue (C.patch small false z) := by
  simp only [fill, dite_eq_left (show 0 ≤ z.val.im from z.property.2)]

variable (diameter : ∀ z : Metric.ball (0 : ℂ) r, ∀ h : z.val.im = 0,
  point X glue (C.patch small false ⟨z.val, z.property, h.ge⟩) =
    point X glue (C.patch small true ⟨z.val, z.property, h.le⟩))

include diameter in
theorem fill_lower (z : bankHalfDisk true r) :
    C.fill glue small ⟨z.val, z.property.1⟩ = point X glue (C.patch small true z) := by
  unfold fill
  split
  · rename_i above
    exact diameter ⟨z.val, z.property.1⟩ (le_antisymm z.property.2 above)
  · rfl

include diameter in
theorem fill_patch (side : Bool) (z : bankHalfDisk side r) :
    C.fill glue small ⟨z.val, z.property.1⟩ = point X glue (C.patch small side z) := by
  cases side
  · exact C.fill_upper glue small z
  · exact C.fill_lower glue small diameter z

theorem edist_point_patch_le (side : Bool) (z w : bankHalfDisk side r) :
    edist (point X glue (C.patch small side z)) (point X glue (C.patch small side w)) ≤
      edist z w := by
  unfold patch tagged
  apply (edist_of_le X glue _ _ _).trans
  exact ((C.chart side).symm.isometry.edist_eq _ _).le

include diameter in
theorem fill_lipschitz (side : Bool) :
    LipschitzOnWith 1 (C.fill glue small)
      {z | if side then z.val.im ≤ 0 else 0 ≤ z.val.im} := by
  intro z hz w hw
  rw [ENNReal.coe_one, one_mul]
  let z' : bankHalfDisk side r := ⟨z.val, z.property, hz⟩
  let w' : bankHalfDisk side r := ⟨w.val, w.property, hw⟩
  exact (congrArg₂ edist (C.fill_patch glue small diameter side z')
    (C.fill_patch glue small diameter side w')).le.trans
      (C.edist_point_patch_le glue small side z' w')

theorem fill_center (positive : 0 < r) :
    C.fill glue small ⟨0, Metric.mem_ball_self positive⟩ = point X glue (a false) := by
  have chart_eq : C.chart false
      ⟨(a false).2, Metric.mem_eball_self (ENNReal.ofReal_pos.mpr C.positive)⟩ =
        (⟨0, Metric.ball_subset_ball small (Metric.mem_ball_self positive),
          (show 0 ≤ (0 : ℂ).im from le_rfl)⟩ : bankHalfDisk false R) :=
    Subtype.ext (C.centered false)
  have inverse := (C.chart false).symm_apply_eq.mpr chart_eq.symm
  rw [fill, dite_eq_left (show 0 ≤ (0 : ℂ).im from le_rfl), patch, inverse]
  rfl

theorem fill_representatives (z : Metric.ball (0 : ℂ) r) :
    ∃ b, point X glue b = C.fill glue small z ∧ C.coordinates b = z.val := by
  by_cases above : 0 ≤ z.val.im
  · let w : bankHalfDisk false r := ⟨z.val, z.property, above⟩
    exact ⟨C.patch small false w, (C.fill_upper glue small w).symm,
      C.coordinates_patch small false w⟩
  · let w : bankHalfDisk true r := ⟨z.val, z.property, (lt_of_not_ge above).le⟩
    refine ⟨C.patch small true w, ?_, C.coordinates_patch small true w⟩
    rw [fill, dite_eq_right above]

include diameter in
theorem fill_of_near (side : Bool) (b : Total X)
    (near : faceCost X (a side) b < ENNReal.ofReal r) :
    ∃ z, C.fill glue small z = point X glue b := by
  have near' : C.Near side b := near.trans_le (ENNReal.ofReal_le_ofReal small)
  let u := C.nearPoint side b near'
  let w := C.chart side u
  have radial : edist w.val 0 = faceCost X (a side) b :=
    (congrArg (edist · (0 : ℂ)) (C.coordinates_near side b near')).symm.trans
      (C.coordinates_edist_center side b near')
  have in_ball : w.val ∈ Metric.ball (0 : ℂ) r :=
    (ENNReal.ofReal_lt_ofReal_iff_of_nonneg dist_nonneg).mp
      ((edist_dist _ _).symm.trans_lt (radial.trans_lt near))
  let z : bankHalfDisk side r := ⟨w.val, in_ball, w.property.2⟩
  refine ⟨⟨w.val, in_ball⟩, (C.fill_patch glue small diameter side z).trans ?_⟩
  have inverse : (C.chart side).symm
      ⟨z.val, Metric.ball_subset_ball small z.property.1, z.property.2⟩ = u :=
    (C.chart side).symm_apply_apply u
  rw [patch, inverse]
  exact congrArg (point X glue) (C.tagged_nearPoint side b near')

end Unfoldings.MetricGluing.BankPairChart
