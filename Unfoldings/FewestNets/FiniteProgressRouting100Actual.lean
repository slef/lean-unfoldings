module

public import Unfoldings.FewestNets.FiniteProgressCone100Actual
public import Unfoldings.Roof.ScaledAdaptiveRouting

/-! Instantiate adaptive routing with the first record's actual physical slope polygon. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FewestNets.Icosahedron

open InnerProductGeometry Real MeshStar Topology

universe u v

/-- The verified first record supplies all rim data and a positive inradius
for the physical roof's adaptive parent forest. -/
theorem exists_q100First_compatibleAdaptiveRouting
    {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexRoof C)
    {a : meshSites 100} (R : MeshStarRealization a (face 100 1 1))
    (no_boundary : ∀ f, K.normalSlope f ∉
      frontier (convexHull ℝ (Set.range (face 100 1 1).physicalVertex)))
    {θ : ℝ} (nonnegative : 0 ≤ θ) (acute : θ < 81.841 * π / 180)
    (angles : ∀ f, K.normalSlope f ∈ convexHull ℝ (Set.range (face 100 1 1).physicalVertex) →
      ∀ i, (K.projectedTriangle f).cornerAngle i ≤ θ) :
    let M := face 100 1 1
    let slopes := convexHull ℝ (Set.range M.physicalVertex)
    let L := convexHull ℝ (Set.range q100FirstBody)
    let compact : IsCompact slopes := (Set.finite_range _).isCompact_convexHull ℝ
    let present : slopes.Nonempty := ⟨M.physicalVertex 0, subset_convexHull ℝ _ ⟨0, rfl⟩⟩
    let ρ := M.derivativeRadius 100
    ∃ boundary : (frontier slopes).Nonempty,
      Nonempty (K.CompatibleAdaptiveRouting {f | K.normalSlope f ∈ slopes}
        (K.clippedExtension slopes compact present) boundary ((fun w : Plane => ρ • w) '' L)
        (ρ * (q100FirstInradius : ℝ)) (cos ((π - 81.841 * π / 180 + θ) / 2)) 0.0073243) := by
  let M := face 100 1 1
  let slopes := convexHull ℝ (Set.range M.physicalVertex)
  let L := convexHull ℝ (Set.range q100FirstBody)
  let ρ := M.derivativeRadius 100
  have pos := q100FirstDerivativeRadius_pos
  have hq : (0 : ℕ) < 100 := by decide
  have compact : IsCompact slopes := (Set.finite_range _).isCompact_convexHull ℝ
  have present : slopes.Nonempty :=
    ⟨M.physicalVertex 0, subset_convexHull ℝ _ ⟨0, rfl⟩⟩
  have genuine := face_tangent_firstAxis_ne_zero 100 1 1
  have key : (1, 1) ∈ faceMeshKeys 100 := mem_faceMeshKeys.mpr (by norm_num)
  have outward (k : Fin 6) : 0 < inner ℝ M.direction (M.dual k) :=
    (q100_face_corner_bounds key k).1
  have sides := R.bisectorTangent_neighbor_ne_zero hq
  have halfplanes := R.mem_physicalPolygon_iff_side_le (by decide : 100 ≤ 100) hq
    outward genuine sides
  have proper : slopes ≠ Set.univ := by
    intro full
    let k : Fin 6 := 0
    let n := M.physicalSideNormal k
    let off := M.physicalSideOffset k
    have unit : ‖n‖ = 1 := q100FirstNormal_unit k
    have member : (off + 1) • n ∈ slopes := by rw [full]; trivial
    have h := (halfplanes _).mp member k
    change inner ℝ ((off + 1) • n) n ≤ off at h
    rw [real_inner_smul_left, real_inner_self_eq_norm_sq, unit] at h
    linarith
  have boundary : (frontier slopes).Nonempty := nonempty_frontier_iff.mpr ⟨present, proper⟩
  refine ⟨boundary, ?_⟩
  have image_eq : (fun w : Plane => ρ⁻¹ • w) '' slopes =
      convexHull ℝ (Set.range q100FirstCorner) := by
    let scale : Plane →ₗ[ℝ] Plane := ρ⁻¹ • LinearMap.id
    change scale '' convexHull ℝ (Set.range M.physicalVertex) = _
    rw [scale.image_convexHull, ← Set.range_comp]
    rfl
  have contained : L ⊆ (fun w : Plane => ρ⁻¹ • w) '' slopes := by
    intro w hw
    refine ⟨ρ • w, (halfplanes _).mpr ?_, ?_⟩
    · intro k
      have h := q100FirstBody_strict_side k hw
      change inner ℝ (M.physicalSideNormal k) w < M.physicalSideOffset k / ρ at h
      change inner ℝ (ρ • w) (M.physicalSideNormal k) ≤ M.physicalSideOffset k
      rw [real_inner_smul_left, real_inner_comm (M.physicalSideNormal k) w]
      exact le_of_lt (by
        rw [mul_comm]
        exact (lt_div_iff₀ pos).mp h)
    · change ρ⁻¹ • (ρ • w) = w
      rw [smul_smul, inv_mul_cancel₀ pos.ne', one_smul]
  apply K.exists_compatibleAdaptiveRouting_of_scaled_rim (convex_convexHull ℝ _) compact present
    boundary no_boundary (ρ := ρ) pos L contained (by norm_num [q100FirstInradius])
    closedBall_subset_first_progressBody nonnegative (by linarith only [acute]) angles
  intro p hp
  rw [image_eq] at hp
  obtain ⟨k, unit, line, offset, cone, polar⟩ := q100First_progressCone_on_rim hp
  refine ⟨q100FirstNormal k, unit, by simpa only [line] using offset, ?_, ?_, polar⟩
  · rintro _ ⟨w, hw, rfl⟩
    have h := (halfplanes w).mp hw k
    rw [real_inner_smul_right, line]
    change ρ⁻¹ * inner ℝ (M.physicalSideNormal k) w ≤ M.physicalSideOffset k / ρ
    rw [← div_eq_inv_mul]
    rw [real_inner_comm w (M.physicalSideNormal k)]
    exact div_le_div_of_nonneg_right h pos.le
  · obtain ⟨axis, width, nz, lower, upper, eq⟩ := cone
    exact ⟨axis, width, nz, (acute.trans lower).le, upper.le, eq⟩

end Unfoldings.FewestNets.Icosahedron
