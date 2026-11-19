module

public import Unfoldings.Cone.ComplementarySectorPlane
public import Unfoldings.Cone.DirectedIntervalChart
public import Unfoldings.Metric.PolygonalRigid

/-! Radial distance and apex balls in the two complementary intrinsic sectors. -/

@[expose] public section

noncomputable section

open scoped NNReal

namespace Unfoldings

theorem planarSector_eq_closedAngularSector {θ : ℝ} (pos : 0 < θ) (small : θ < Real.pi) :
    planarSector θ = closedAngularSector θ := by
  ext z
  constructor
  · intro inside
    by_cases zero : z = 0
    · exact zero.symm ▸ (closedAngularSectorOrigin pos.le).property
    · obtain ⟨r, positive, angle, bounds, equal⟩ :=
        exists_polar_of_mem_planarSector θ pos small z inside zero
      exact ⟨⟨r, positive.le⟩, angle, bounds, equal⟩
  · rintro ⟨r, angle, bounds, rfl⟩
    have ray := (polarRay_mem_planarSector_iff θ angle pos small
      ⟨bounds.1, bounds.2.trans small.le⟩).mpr bounds
    obtain ⟨a, ha, b, hb, equal⟩ := ray
    refine ⟨(r : ℝ) * a, mul_nonneg r.property ha, (r : ℝ) * b, mul_nonneg r.property hb, ?_⟩
    rw [equal, mul_add, Complex.ofReal_mul]
    simp only [Complex.real_smul, Complex.ofReal_mul]
    ring

theorem closedAngularSector_smul_mem {θ : ℝ} {z : ℂ} (inside : z ∈ closedAngularSector θ)
    {c : ℝ} (nonnegative : 0 ≤ c) : c • z ∈ closedAngularSector θ := by
  obtain ⟨r, φ, bounds, rfl⟩ := inside
  refine ⟨⟨c * r, mul_nonneg nonnegative r.property⟩, φ, bounds, ?_⟩
  change c • ((r : ℂ) * polarRay φ) = ((c * (r : ℝ) : ℝ) : ℂ) * polarRay φ
  rw [Complex.real_smul, Complex.ofReal_mul, mul_assoc]

theorem complementarySectorRegion_smul_mem {θ : ℝ} {side : Bool} {z : ℂ}
    (inside : z ∈ complementarySectorRegion θ side) {c : ℝ} (nonnegative : 0 ≤ c) :
    c • z ∈ complementarySectorRegion θ side := by
  cases side
  · exact closedAngularSector_smul_mem inside nonnegative
  · obtain ⟨x, hx, rfl⟩ := inside
    exact ⟨c • x, closedAngularSector_smul_mem hx nonnegative,
      (rotation (Circle.exp θ)).map_smul c x⟩

/-- The apex is a common point of both geometric sectors. -/
def complementarySectorOrigin {θ : ℝ} (pos : 0 < θ) (small : θ < 2 * Real.pi) (side : Bool) :
    PolygonalPoint (complementarySectorRegion θ side) := by
  have pair : (0 : ℂ) ∈ closedAngularSector θ ∩ complementarySector θ := by
    rw [closedAngularSector_inter_complementary θ pos small]
    exact Or.inl ⟨0, by simp⟩
  refine ⟨0, ?_⟩
  cases side
  · exact pair.1
  · exact pair.2

@[simp] theorem complementarySectorOrigin_val {θ : ℝ} (pos : 0 < θ) (small : θ < 2 * Real.pi)
    (side : Bool) : (complementarySectorOrigin pos small side).val = 0 := rfl

/-- A piece distance to the apex is the actual planar radius, even for a reentrant sector. -/
theorem edist_complementarySectorOrigin {θ : ℝ} (pos : 0 < θ) (small : θ < 2 * Real.pi)
    (side : Bool) (z : PolygonalPoint (complementarySectorRegion θ side)) :
    edist z (complementarySectorOrigin pos small side) = edist z.val (0 : ℂ) := by
  have segment_inside : segment ℝ z.val (complementarySectorOrigin pos small side).val ⊆
      complementarySectorRegion θ side := by
    rw [complementarySectorOrigin_val, segment_symm, segment_eq_image_lineMap]
    rintro _ ⟨t, ht, rfl⟩
    rw [AffineMap.lineMap_apply_module', sub_zero, add_zero]
    exact complementarySectorRegion_smul_mem z.property ht.1
  exact PolygonalPoint.edist_eq_of_segment segment_inside

end Unfoldings
