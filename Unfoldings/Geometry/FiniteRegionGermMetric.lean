module

public import Unfoldings.Geometry.AffineArrangementGerm
public import Unfoldings.Metric.PolygonalGerm

/-! Exact intrinsic corner models for finite unions of affine cells, including reentrant corners. -/

@[expose] public section

noncomputable section

open Filter Topology

namespace Unfoldings.AffineArrangement

variable {E I J : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Finite I] [Finite J]
  (f : J → I → E →ᵃ[ℝ] ℝ) (signs : J → I → Bool)

/-- All and only the incident original cell cones contribute to a region's corner model. -/
def regionGerm (x : E) : Set E := ⋃ j, cellGerm (f j) (signs j) x

/-- Retain the physical center when comparing the actual region to its conical model. -/
def translatedRegionGerm (x : E) : Set E := {z | z - x ∈ regionGerm f signs x}

omit [FiniteDimensional ℝ E] [Finite I] in
theorem starConvex_cellGerm (g : I → E →ᵃ[ℝ] ℝ) (σ : I → Bool) (x : E) :
    StarConvex ℝ 0 (cellGerm g σ x) := by
  classical
  unfold cellGerm
  split
  · exact (convex_tangentCell g σ x).starConvex (zero_mem_tangentCell g σ x)
  · exact starConvex_empty _

omit [FiniteDimensional ℝ E] [Finite I] [Finite J] in
theorem starConvex_regionGerm (x : E) : StarConvex ℝ 0 (regionGerm f signs x) :=
  starConvex_iUnion (fun j => starConvex_cellGerm (f j) (signs j) x)

omit [FiniteDimensional ℝ E] [Finite I] [Finite J] in
theorem starConvex_translatedRegionGerm (x : E) :
    StarConvex ℝ x (translatedRegionGerm f signs x) := by
  let shift := AffineMap.id ℝ E - AffineMap.const ℝ E x
  have star : StarConvex ℝ (shift x) (regionGerm f signs x) := by
    change StarConvex ℝ (x - x) (regionGerm f signs x)
    simpa only [sub_self] using starConvex_regionGerm f signs x
  exact star.affine_preimage shift

theorem eventually_mem_region_iff_germ (x : E) :
    ∀ᶠ z in 𝓝 x, z ∈ (⋃ j, closedChamber (f j) (signs j)) ↔
      z ∈ translatedRegionGerm f signs x := by
  have near : ∀ᶠ z in 𝓝 x, ∀ j,
      z ∈ closedChamber (f j) (signs j) ↔ z - x ∈ cellGerm (f j) (signs j) x :=
    eventually_all.mpr (fun j =>
      eventually_mem_closedChamber_iff_cellGerm (f j) (signs j) x)
  filter_upwards [near] with z hz
  simp only [translatedRegionGerm, regionGerm, Set.mem_ofPred_eq, Set.mem_iUnion, hz]

/-- Every point of an actual finite affine-cell region has an intrinsic cone-ball isometry.
The cone is constructed from the actual active inequalities, without supplied corner angles. -/
theorem exists_regionGerm_ball_isometry
    (x : PolygonalPoint (⋃ j, closedChamber (f j) (signs j))) :
    ∃ r : ℝ, 0 < r ∧ ∃ a : PolygonalPoint (translatedRegionGerm f signs x.val),
      a.val = x.val ∧ ∃ A : Metric.eball x (ENNReal.ofReal r) ≃ᵢ
        Metric.eball a (ENNReal.ofReal r), ∀ z, (A z).val.val = z.val.val := by
  obtain ⟨δ, positive, included⟩ := Metric.mem_nhds_iff.mp
    (eventually_mem_region_iff_germ f signs x.val)
  have local_eq (z : E) (near : dist z x.val < δ) :
      z ∈ (⋃ j, closedChamber (f j) (signs j)) ↔
        z ∈ translatedRegionGerm f signs x.val := included (Metric.mem_ball.mpr near)
  let a : PolygonalPoint (translatedRegionGerm f signs x.val) :=
    ⟨x.val, (local_eq x.val (by simpa only [dist_self] using positive)).mp x.property⟩
  obtain ⟨A, physical⟩ := PolygonalPoint.exists_local_starConvex_ball_isometry x a rfl positive
    (starConvex_translatedRegionGerm f signs x.val) local_eq
  exact ⟨δ / 4, div_pos positive (by norm_num), a, rfl, A, physical⟩

end Unfoldings.AffineArrangement
