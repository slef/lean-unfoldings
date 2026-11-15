module

public import Unfoldings.Geometry.AffineArrangement
public import Unfoldings.Geometry.LineCoordinate
public import Unfoldings.Basic
public import Mathlib.Topology.Instances.NNReal.Lemmas

/-! Actual planar segments and terminal rays as fixed finite affine inequality systems. -/

@[expose] public section

noncomputable section

open scoped NNReal

namespace Unfoldings

/-- Displacement from the actual affine-coordinate projection to the endpoint line. -/
def lineResidual (a b : Plane) : Plane →ᵃ[ℝ] Plane :=
  AffineMap.id ℝ Plane - (AffineMap.lineMap a b).comp (lineCoordinate a b)

/-- Four weak inequalities impose exact equality with the supporting line. -/
def lineResidualInequalities (a b : Plane) : Fin 4 → Plane →ᵃ[ℝ] ℝ :=
  ![(EuclideanSpace.proj 0).toLinearMap.toAffineMap.comp (lineResidual a b),
    -(EuclideanSpace.proj 0).toLinearMap.toAffineMap.comp (lineResidual a b),
    (EuclideanSpace.proj 1).toLinearMap.toAffineMap.comp (lineResidual a b),
    -(EuclideanSpace.proj 1).toLinearMap.toAffineMap.comp (lineResidual a b)]

/-- The four line constraints plus the two actual segment endpoint bounds. -/
def segmentInequalities (a b : Plane) : Fin 6 → Plane →ᵃ[ℝ] ℝ :=
  ![lineResidualInequalities a b 0, lineResidualInequalities a b 1,
    lineResidualInequalities a b 2, lineResidualInequalities a b 3,
    lineCoordinate a b, AffineMap.const ℝ Plane 1 - lineCoordinate a b]

theorem mem_lineResidualInequalities_iff (a b z : Plane) :
    z ∈ AffineArrangement.closedChamber (lineResidualInequalities a b) (fun _ => true) ↔
      z = AffineMap.lineMap a b (lineCoordinate a b z) := by
  constructor
  · intro member
    have first := member 0
    have second := member 1
    have third := member 2
    have fourth := member 3
    change 0 ≤ lineResidual a b z 0 at first
    change 0 ≤ -(lineResidual a b z 0) at second
    change 0 ≤ lineResidual a b z 1 at third
    change 0 ≤ -(lineResidual a b z 1) at fourth
    have residual_zero : lineResidual a b z = 0 := by
      ext i
      fin_cases i
      · change lineResidual a b z 0 = 0
        linarith
      · change lineResidual a b z 1 = 0
        linarith
    have equal : z - AffineMap.lineMap a b (lineCoordinate a b z) = 0 := residual_zero
    exact sub_eq_zero.mp equal
  · intro equal i
    have residual_zero : lineResidual a b z = 0 := by
      change z - AffineMap.lineMap a b (lineCoordinate a b z) = 0
      exact sub_eq_zero.mpr equal
    fin_cases i <;> simp [lineResidualInequalities, AffineMap.comp_apply, residual_zero]

/-- The finite weak halfspaces describe the exact original segment, including a single point. -/
theorem segment_eq_closedChamber (a b : Plane) :
    segment ℝ a b = AffineArrangement.closedChamber (segmentInequalities a b) (fun _ => true) := by
  ext z
  constructor
  · intro member
    have data : z = AffineMap.lineMap a b (lineCoordinate a b z) ∧
        lineCoordinate a b z ∈ Set.Icc (0 : ℝ) 1 := by
      by_cases different : a ≠ b
      · rw [segment_eq_image_lineMap] at member
        obtain ⟨t, bounds, rfl⟩ := member
        rw [lineCoordinate_lineMap different]
        exact ⟨rfl, bounds⟩
      · have same : a = b := not_ne_iff.mp different
        have point : z = a := by simpa only [same, segment_same, Set.mem_singleton_iff] using member
        subst z
        subst b
        simp [lineCoordinate_apply]
    have line := (mem_lineResidualInequalities_iff a b z).mpr data.1
    intro i
    fin_cases i
    · exact line 0
    · exact line 1
    · exact line 2
    · exact line 3
    · exact data.2.1
    · change 0 ≤ 1 - lineCoordinate a b z
      linarith [data.2.2]
  · intro member
    have line : z ∈ AffineArrangement.closedChamber (lineResidualInequalities a b)
        (fun _ => true) := by
      intro i
      fin_cases i
      · exact member 0
      · exact member 1
      · exact member 2
      · exact member 3
    have first : 0 ≤ lineCoordinate a b z := member 4
    have last : 0 ≤ 1 - lineCoordinate a b z := member 5
    rw [(mem_lineResidualInequalities_iff a b z).mp line]
    exact lineMap_mem_segment ℝ a b ⟨first, by linarith⟩

/-- The four line constraints and the initial endpoint bound, with an unused sixth slot. -/
def rayInequalities (a b : Plane) : Fin 6 → Plane →ᵃ[ℝ] ℝ :=
  ![lineResidualInequalities a b 0, lineResidualInequalities a b 1,
    lineResidualInequalities a b 2, lineResidualInequalities a b 3, lineCoordinate a b, 0]

/-- Fixed finite weak halfspaces describe the exact entire ray, allowing a zero direction. -/
theorem ray_eq_closedChamber (a b : Plane) :
    Set.range (fun t : ℝ≥0 => AffineMap.lineMap a b (t : ℝ)) =
      AffineArrangement.closedChamber (rayInequalities a b) (fun _ => true) := by
  ext z
  constructor
  · rintro ⟨t, rfl⟩
    have data : AffineMap.lineMap a b (t : ℝ) =
        AffineMap.lineMap a b (lineCoordinate a b (AffineMap.lineMap a b (t : ℝ))) ∧
        0 ≤ lineCoordinate a b (AffineMap.lineMap a b (t : ℝ)) := by
      by_cases different : a ≠ b
      · rw [lineCoordinate_lineMap different]
        exact ⟨rfl, t.coe_nonneg⟩
      · have same : a = b := not_ne_iff.mp different
        subst b
        simp [lineCoordinate_apply]
    have line := (mem_lineResidualInequalities_iff a b _).mpr data.1
    intro i
    fin_cases i
    · exact line 0
    · exact line 1
    · exact line 2
    · exact line 3
    · exact data.2
    · change (0 : ℝ) ≤ 0
      exact le_rfl
  · intro member
    have line : z ∈ AffineArrangement.closedChamber (lineResidualInequalities a b)
        (fun _ => true) := by
      intro i
      fin_cases i
      · exact member 0
      · exact member 1
      · exact member 2
      · exact member 3
    have nonnegative : 0 ≤ lineCoordinate a b z := member 4
    exact ⟨⟨lineCoordinate a b z, nonnegative⟩,
      ((mem_lineResidualInequalities_iff a b z).mp line).symm⟩

end Unfoldings
