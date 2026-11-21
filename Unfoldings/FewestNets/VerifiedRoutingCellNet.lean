module

public import Unfoldings.FewestNets.RotatedCheckedCell
public import Unfoldings.FewestNets.CheckedMeshRoutingRecord
public import Unfoldings.FewestNets.IcosahedronFrequency100Scalars
public import Unfoldings.FewestNets.IcosahedronChartGenuine

/-! A verified keyed routing record discharges the original component-net obligation. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FewestNets.Icosahedron

open MeshStar Real InnerProductGeometry

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {F : SpatialFolding C}

theorem MeshRecordKey.model_chart_genuine (q : ℕ) (key : MeshRecordKey) :
    bisectorTangent (key.model q).direction (WithLp.toLp 2 ![1, 0, 0]) ≠ 0 := by
  cases key with
  | face i j => exact face_tangent_firstAxis_ne_zero q i j
  | seam i => exact seam_tangent_firstAxis_ne_zero q i
  | vertex => exact pentagon_tangent_firstAxis_ne_zero q

theorem MeshRecordKey.pred_ne (key : MeshRecordKey) (k : Fin (key.sidePred + 1)) :
    k ≠ k - 1 := by
  have hex (i : Fin 6) : i ≠ i - 1 := by fin_cases i <;> decide
  have pent (i : Fin 5) : i ≠ i - 1 := by fin_cases i <;> decide
  cases key with
  | face => exact hex k
  | seam => exact hex k
  | vertex => exact pent k

/-- The checked tilt alternatives bound the whole spherical cell in the same record's model. -/
theorem angle_le_of_verified_mesh_routing_tilt {q : ℕ} (hq : 0 < q) (qbig : 100 ≤ q)
    {a : meshSites q} {key : MeshRecordKey} (R : MeshStarRealization a (key.model q))
    (outward : ∀ k, 0 < inner ℝ (key.model q).direction ((key.model q).dual k))
    {φ : ℚ} (pos : 0 ≤ φ) (check : checkDevelopmentCellTilt q key φ = true)
    {x : Space} (member : x ∈ sphericalVoronoiCell (fun a : meshSites q => (a : Space)) a) :
    angle (a : Space) x ≤ φ := by
  have same : checkDevelopmentCellTilt q key φ =
      (checkUniformRecordTilt q φ ||
        MeshStar.Checked.checkGnomonicRadius certificateDenominator_pos (key.checkedModel q) φ) := by
    cases key <;> rfl
  rw [same, Bool.or_eq_true] at check
  rcases check with uniform | radius
  · have unit : ‖x‖ = 1 := by
      simpa only [Metric.mem_sphere, dist_zero_right] using member.2
    rw [angle_comm]
    exact (angle_le_meshTilt_of_mem_normalCone hq unit a member.1).trans
      (meshTilt_le_of_checkUniformRecordTilt hq uniform)
  · exact R.angle_le_of_gnomonicVertex_radius qbig hq outward (by exact_mod_cast pos)
      (fun k => MeshStar.Checked.gnomonicVertex_norm_le_tan_of_check certificateDenominator_pos
        (key.checkedModel q) radius k) member

/-- A record with a passed geometric and scalar check supplies a net of every
original component whose faces have the realized site's strict label. -/
theorem hasOriginalEdgeNet_of_verified_routing_record {q : ℕ} (hq : 0 < q) (qbig : 100 ≤ q)
    {a : meshSites q} {key : MeshRecordKey} (R : MeshStarRealization a (key.model q))
    (outward : ∀ k, 0 < inner ℝ (key.model q).direction ((key.model q).dual k))
    {target : ℚ} (target_nonneg : 0 ≤ target)
    (row : MeshRoutingRecord q key) (verified : row.Verified target)
    (P : F.ConvexBoundary) (N : F.SupportingNormals) (g : SpatialRotation)
    (label : Face → meshSites q)
    (chosen : ∀ f, N.normal f ∈ strictVoronoiCone (fun b : meshSites q =>
      SpatialRotation.linear g (b : Space)) (label f))
    (angles : ∀ f i, (C.triangle f).cornerAngle i ≤ (target : ℝ) * π / 180)
    (seed : Face) (seed_label : label seed = a) :
    C.HasOriginalEdgeNet ((C.labeledSeamGraph label).connectedComponentMk seed).supp := by
  obtain ⟨valid, gaps, cot, interior_gap⟩ :=
    row.scalar.bounds_of_check certificateDenominator_pos target verified.development
  have small : (row.scalar.tilt : ℝ) ≤ 1 / 2 := by
    have h : (row.scalar.tilt : ℝ) ≤ ((1 / 2 : ℚ) : ℝ) := Rat.cast_le.mpr verified.tilt_small
    norm_num at h ⊢
    exact h
  have nonnegative : (0 : ℝ) ≤ row.scalar.tilt := by exact_mod_cast valid.1.le
  have sq := pow_le_pow_left₀ nonnegative small 2
  have height_bound : (3 : ℝ) / 4 ≤ cos row.scalar.tilt := by
    norm_num at sq
    linarith only [sq, one_sub_sq_div_two_le_cos (x := row.scalar.tilt)]
  have scale := CheckedReal.positive_of_isPositive certificateDenominator_pos _ verified.scale
  exact R.hasOriginalEdgeNet_rotated_checked_cell hq qbig outward
    (MeshRecordKey.model_chart_genuine q key) (MeshRecordKey.pred_ne key)
    P N g label chosen scale certificateDenominator_pos (row.checkedCorner verified.chart)
    (row.checkedNormal verified.chart) (row.checkedOffset verified.chart)
    row.scalar row.witness target_nonneg valid cot interior_gap verified.geometry height_bound
    (gaps 0) (fun _ hx => angle_le_of_verified_mesh_routing_tilt hq qbig R outward valid.1.le
      verified.tilt hx) angles seed seed_label

end Unfoldings.FewestNets.Icosahedron
