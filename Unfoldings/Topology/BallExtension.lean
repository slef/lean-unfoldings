module

public import Unfoldings.Topology.CommonFibers
public import Unfoldings.Topology.DiskDegree

/-!
# Extending boundary homeomorphisms to closed balls

The unit ball is the compact quotient of its unit sphere times the unit
interval, collapsing precisely the zero-radius fiber. Changing the sphere
coordinate therefore gives a homeomorphism of balls. This construction fixes
radius and explicitly agrees with the prescribed map at every boundary point.
It supplies boundary matching for subsequent disk gluing.
-/

@[expose] public section

noncomputable section

namespace Unfoldings.UnitBall

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def radialProjection (p : Metric.sphere (0 : E) 1 × unitInterval) :
    Metric.closedBall (0 : E) 1 :=
  ⟨(p.2 : ℝ) • p.1.val, by
    rw [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg p.2.property.1,
      (show ‖p.1.val‖ = 1 by
        simpa only [Metric.mem_sphere, dist_zero_right] using p.1.property), mul_one]
    exact p.2.property.2⟩

theorem continuous_radialProjection : Continuous (radialProjection (E := E)) :=
  ((continuous_subtype_val.comp continuous_snd).smul
    (continuous_subtype_val.comp continuous_fst)).subtype_mk _

@[simp] theorem norm_radialProjection (p : Metric.sphere (0 : E) 1 × unitInterval) :
    ‖(radialProjection p).val‖ = (p.2 : ℝ) := by
  change ‖(p.2 : ℝ) • p.1.val‖ = _
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg p.2.property.1,
    (show ‖p.1.val‖ = 1 by
      simpa only [Metric.mem_sphere, dist_zero_right] using p.1.property), mul_one]

theorem radialProjection_surjective [Nontrivial E] :
    Function.Surjective (radialProjection (E := E)) := by
  intro x
  by_cases zero : x.val = 0
  · obtain ⟨u, hu⟩ := (NormedSpace.sphere_nonempty (x := (0 : E))).mpr zero_le_one
    exact ⟨(⟨u, hu⟩, 0), Subtype.ext (by simpa [radialProjection] using zero.symm)⟩
  · let direction := unitDirection ⟨x.val, zero⟩
    let radius : unitInterval := ⟨‖x.val‖, norm_nonneg _, by
      simpa only [Metric.mem_closedBall, dist_zero_right] using x.property⟩
    refine ⟨(direction, radius), Subtype.ext ?_⟩
    change ‖x.val‖ • (‖x.val‖⁻¹ • x.val) = x.val
    rw [smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr zero), one_smul]

theorem radialProjection_fibers (a b : Metric.sphere (0 : E) 1 × unitInterval) :
    radialProjection a = radialProjection b ↔
      a.2 = b.2 ∧ (a.2 = 0 ∨ a.1 = b.1) := by
  constructor
  · intro equal
    have radii : a.2 = b.2 := by
      apply Subtype.ext
      simpa only [norm_radialProjection] using
        congrArg (fun p : Metric.closedBall (0 : E) 1 => ‖p.val‖) equal
    refine ⟨radii, ?_⟩
    by_cases zero : a.2 = 0
    · exact Or.inl zero
    · right
      apply Subtype.ext
      have value : (a.2 : ℝ) • a.1.val = (b.2 : ℝ) • b.1.val := congrArg Subtype.val equal
      rw [← radii] at value
      exact smul_right_injective E (by
        intro h
        exact zero (Subtype.ext h)) value
  · rintro ⟨radii, zero | directions⟩
    · apply Subtype.ext
      change (a.2 : ℝ) • a.1.val = (b.2 : ℝ) • b.1.val
      simp only [← radii, zero, Set.Icc.coe_zero, zero_smul]
    · apply Subtype.ext
      change (a.2 : ℝ) • a.1.val = (b.2 : ℝ) • b.1.val
      rw [radii, directions]

variable (e : Metric.sphere (0 : E) 1 ≃ₜ Metric.sphere (0 : F) 1)

def changeDirection (p : Metric.sphere (0 : E) 1 × unitInterval) :
    Metric.closedBall (0 : F) 1 := radialProjection (e p.1, p.2)

omit [NormedSpace ℝ E] in
theorem continuous_changeDirection : Continuous (changeDirection e) :=
  continuous_radialProjection.comp ((e.continuous.comp continuous_fst).prodMk continuous_snd)

omit [NormedSpace ℝ E] in
theorem changeDirection_surjective [Nontrivial F] : Function.Surjective (changeDirection e) := by
  intro y
  obtain ⟨⟨u, t⟩, equal⟩ := radialProjection_surjective y
  exact ⟨(e.symm u, t), by simpa only [changeDirection, Homeomorph.apply_symm_apply] using equal⟩

theorem changeDirection_fibers (a b : Metric.sphere (0 : E) 1 × unitInterval) :
    radialProjection a = radialProjection b ↔ changeDirection e a = changeDirection e b := by
  rw [radialProjection_fibers]
  change _ ↔ radialProjection (e a.1, a.2) = radialProjection (e b.1, b.2)
  rw [radialProjection_fibers]
  simp only [e.injective.eq_iff]

variable [ProperSpace E] [Nontrivial E] [Nontrivial F]

/-- Radial extension of an arbitrary unit-sphere homeomorphism. -/
def extend : Metric.closedBall (0 : E) 1 ≃ₜ Metric.closedBall (0 : F) 1 :=
  homeomorphOfCompactCommonFibers radialProjection (changeDirection e)
    continuous_radialProjection (continuous_changeDirection e)
    radialProjection_surjective (changeDirection_surjective e) (changeDirection_fibers e)

@[simp] theorem extend_radialProjection (p : Metric.sphere (0 : E) 1 × unitInterval) :
    extend e (radialProjection p) = radialProjection (e p.1, p.2) :=
  homeomorphOfCompactCommonFibers_apply radialProjection (changeDirection e)
    continuous_radialProjection (continuous_changeDirection e)
    radialProjection_surjective (changeDirection_surjective e) (changeDirection_fibers e) p

@[simp] theorem extend_boundary (u : Metric.sphere (0 : E) 1) :
    extend e (unitSphereDiskInclusion u) = unitSphereDiskInclusion (e u) := by
  have value := extend_radialProjection e (u, 1)
  simpa only [radialProjection, Set.Icc.coe_one, one_smul, unitSphereDiskInclusion,
    ContinuousMap.coe_mk] using value

@[simp] theorem norm_extend (x : Metric.closedBall (0 : E) 1) :
    ‖(extend e x).val‖ = ‖x.val‖ := by
  obtain ⟨p, rfl⟩ := radialProjection_surjective x
  rw [extend_radialProjection, norm_radialProjection, norm_radialProjection]

theorem extend_boundary_iff (x : Metric.closedBall (0 : E) 1) :
    (extend e x).val ∈ Metric.sphere (0 : F) 1 ↔ x.val ∈ Metric.sphere (0 : E) 1 := by
  simp only [Metric.mem_sphere, dist_zero_right, norm_extend]

end Unfoldings.UnitBall
