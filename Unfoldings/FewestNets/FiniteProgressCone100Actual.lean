module

public import Unfoldings.FewestNets.FiniteProgressConeExample
public import Unfoldings.FewestNets.IcosahedronCellFrontier
public import Unfoldings.FewestNets.IcosahedronChartGenuine
public import Unfoldings.FewestNets.IcosahedronRealizedInteriorStar
public import Unfoldings.FewestNets.FiniteMeshCorner100Bounds

/-! The first saved record gives routing margins on the entire exact cell rim. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FewestNets.Icosahedron

open InnerProductGeometry Real MeshStar

set_option maxRecDepth 8192 in
theorem q100FirstDerivativeRadius_pos : 0 < (face 100 1 1).derivativeRadius 100 :=
  CheckedReal.positive_of_isPositive certificateDenominator_pos
    ((checkFace certificateDenominator_pos 100 1 1).derivativeRadius certificateDenominator_pos 100)
    (by decide +kernel)

set_option maxHeartbeats 800000 in
-- The represented star introduces several dependent casts on its cyclic indices.
/-- Every point on the first exact normalized cell rim has a certified
outward normal and an angular progress cone with both required margins. -/
theorem q100First_progressCone_on_rim {p : Plane}
    (on_rim : p ∈ frontier (convexHull ℝ (Set.range q100FirstCorner))) :
    let L := convexHull ℝ (Set.range q100FirstBody)
    let θ := 81.841 * π / 180
    ∃ side : Fin 6,
      ‖q100FirstNormal side‖ = 1 ∧
      inner ℝ (q100FirstNormal side) p = q100FirstOffset side ∧
      0 < q100FirstOffset side ∧
      (∃ (axis : Plane) (width : ℝ), axis ≠ 0 ∧ θ < width ∧ width < π - θ ∧
        ∀ z : Plane, z ≠ 0 → (z ∈ SlopeEnvelope.historyCone L p ↔ angle axis z ≤ width / 2)) ∧
      ∀ z : Plane, z ∈ SlopeEnvelope.historyCone L p →
        0.0073243 * ‖z‖ ≤ inner ℝ z (q100FirstNormal side) := by
  dsimp only
  have hq : (0 : ℕ) < 100 := by decide
  have qbig : (100 : ℕ) ≤ 100 := le_rfl
  have sum : (1 : ℕ) + 98 < 100 := by decide
  have real := nonempty_interiorStarRealization hq 0
    (by decide : (0 : ℕ) < 1) (by decide : (0 : ℕ) < 98) sum
  rw [modelInteriorStar_eq_face sum] at real
  obtain ⟨R⟩ := real
  have key : (1, 1) ∈ faceMeshKeys 100 := mem_faceMeshKeys.mpr (by norm_num)
  have outward (k : Fin 6) : 0 < inner ℝ (face 100 1 1).direction ((face 100 1 1).dual k) :=
    (q100_face_corner_bounds key k).1
  have genuine := face_tangent_firstAxis_ne_zero 100 1 1
  have side (k : Fin 6) : bisectorTangent (face 100 1 1).direction
      ((face 100 1 1).neighborDirection k) ≠ 0 := R.bisectorTangent_neighbor_ne_zero hq k
  have hits := R.frontier_normalizedPolygon_subset_sides qbig hq outward genuine side
    (fun k => by fin_cases k <;> decide) q100FirstDerivativeRadius_pos.ne' on_rim
  obtain ⟨k, present⟩ := Set.mem_iUnion.mp hits
  obtain ⟨t, ht, ht_eq⟩ := (segment_eq_image_lineMap ℝ _ _).le present
  change AffineMap.lineMap (q100FirstCorner (k - 1)) (q100FirstCorner k) t = p at ht_eq
  have eq : inner ℝ (q100FirstNormal k) p = q100FirstOffset k := by
    rw [← ht_eq, real_inner_comm]
    exact (face 100 1 1).normalizedSide_on_support_line (R.direction_unit hq) genuine k
      (R.neighborDirection_unit hq k) (side k) outward _ t
  have positive : 0 < q100FirstOffset k := by
    have origin : (0 : Plane) ∈ convexHull ℝ (Set.range q100FirstBody) :=
      closedBall_subset_first_progressBody (by
        simp [Metric.mem_closedBall, q100FirstInradius]; norm_num)
    have h := q100FirstBody_strict_side k origin
    change inner ℝ (q100FirstNormal k) 0 < q100FirstOffset k at h
    simpa only [inner_zero_right] using h
  refine ⟨k, q100FirstNormal_unit k, eq, positive, ?_⟩
  have cone := q100First_progressCone_on_side k ht (by rw [ht_eq, eq])
  rwa [ht_eq] at cone

end Unfoldings.FewestNets.Icosahedron
