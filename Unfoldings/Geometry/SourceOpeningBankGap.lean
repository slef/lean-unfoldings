module

public import Unfoldings.Geometry.OrientedBankGap
public import Unfoldings.Geometry.PolygonalRayAffineMap
public import Unfoldings.Geometry.PolygonalRayOpening
public import Unfoldings.Geometry.RadialVertexCoordinates
public import Unfoldings.Geometry.BankCornerTurn

/-! A source-only opening retains every downstream turn of the saved frontier. -/

@[expose] public section

noncomputable section

open scoped NNReal

namespace Unfoldings.PolygonalRay

variable {n : ℕ} (R : PolygonalRay ℂ n)

/-- Opening only at the source is precisely a rigid motion of the whole bank and tail. -/
theorem rotateSuffix_zero_eq_affineMap (θ : ℝ) :
    R.rotateSuffix 0 θ = R.affineMap (sourceRotation R.start θ).toAffineMap := by
  have vertices (i : Fin (n + 1)) :
      (R.rotateSuffix 0 θ).chain.vertex i =
        (R.affineMap (sourceRotation R.start θ).toAffineMap).chain.vertex i := by
    change (R.chain.rotateSuffix 0 θ).vertex i = sourceRotation R.start θ (R.chain.vertex i)
    rw [sourceRotation_apply]
    exact R.chain.rotateSuffix_vertex_ge 0 θ i (Fin.zero_le i)
  have chains := congrArg (PolygonalChain.mk (E := ℂ) (n := n)) (funext vertices)
  exact congrArg₂ (PolygonalRay.mk (E := ℂ) (n := n)) chains rfl

theorem rotateSuffix_zero_vertex_sub_start (θ : ℝ) (i : Fin (n + 1)) :
    (R.rotateSuffix 0 θ).chain.vertex i - (R.rotateSuffix 0 θ).start =
      complexRotation θ (R.chain.vertex i - R.start) := by
  rw [R.rotateSuffix_start, R.rotateSuffix_zero_eq_affineMap]
  change sourceRotation R.start θ (R.chain.vertex i) - R.start = _
  rw [sourceRotation_apply, add_sub_cancel_left]

theorem rotateSuffix_zero_edge (θ : ℝ) (i : Fin n) :
    (R.rotateSuffix 0 θ).chain.edge i = complexRotation θ (R.chain.edge i) := by
  change (R.chain.rotateSuffix 0 θ).edge i = complexRotation θ (R.chain.edge i)
  rw [R.chain.rotateSuffix_edge, ite_eq_left (Fin.zero_le _), complexRotation_apply]

theorem rotateSuffix_zero_outward (outward : R.Outward) (θ : ℝ) :
    (R.rotateSuffix 0 θ).Outward := by
  constructor
  · intro i before
    apply (monotone_dist_lineMap_iff _ _ _).mpr
    change 0 ≤ inner ℝ ((R.rotateSuffix 0 θ).chain.vertex i.castSucc -
      (R.rotateSuffix 0 θ).start) ((R.rotateSuffix 0 θ).chain.edge i)
    rw [R.rotateSuffix_zero_vertex_sub_start, R.rotateSuffix_zero_edge,
      LinearIsometry.inner_map_map]
    exact (monotone_dist_lineMap_iff _ _ _).mp (outward.1 i before)
  · change 0 ≤ inner ℝ
      ((R.rotateSuffix 0 θ).chain.vertex (Fin.last n) - (R.rotateSuffix 0 θ).start)
      (complexRotation θ R.direction)
    rw [R.rotateSuffix_zero_vertex_sub_start, LinearIsometry.inner_map_map]
    exact outward.2

/-- A rigid source opening of angle between zero and a half-turn gives an oriented gap. -/
theorem orientedGap_rotateSuffix_zero (outward : R.Outward) (nonzero : R.direction ≠ 0)
    {θ : ℝ} (positive : 0 < θ) (small : θ < Real.pi) :
    OrientedBankGap R (R.rotateSuffix 0 θ) := by
  let Q := R.rotateSuffix 0 θ
  let S := sourceRotation R.start θ
  have last := R.rotateSuffix_zero_outward outward θ
  have genuine : Q.direction ≠ 0 := by
    change complexRotation θ R.direction ≠ 0
    simpa only [map_zero] using (complexRotation θ).injective.ne nonzero
  have common : Q.start = R.start := R.rotateSuffix_start 0 θ
  refine ⟨outward, nonzero, last, genuine, ?_, common⟩
  intro r hr
  have member : S (R.radialPoint outward nonzero r) ∈ Q.carrier := by
    rw [show Q = R.affineMap S.toAffineMap from R.rotateSuffix_zero_eq_affineMap θ,
      R.affineMap_carrier]
    exact ⟨_, R.radialPoint_mem outward nonzero r, rfl⟩
  have radius : ‖S (R.radialPoint outward nonzero r) - Q.start‖₊ = r := by
    apply NNReal.eq
    rw [coe_nnnorm, common]
    change ‖sourceRotation R.start θ (R.radialPoint outward nonzero r) - R.start‖ = _
    rw [sourceRotation_apply, add_sub_cancel_left, LinearIsometry.norm_map,
      R.norm_radialPoint_sub_start]
  have rotated : Q.radialPoint last genuine r = S (R.radialPoint outward nonzero r) := by
    have point := Q.radialPoint_norm_eq_of_mem last genuine member
    rwa [radius] at point
  have factor : Q.radialCoefficient last genuine r =
      polarRay θ * R.radialCoefficient outward nonzero r := by
    unfold radialCoefficient
    rw [rotated, common]
    change (sourceRotation R.start θ (R.radialPoint outward nonzero r) - R.start) / (r : ℂ) = _
    rw [sourceRotation_apply, add_sub_cancel_left, complexRotation_apply, mul_div_assoc]
  have unit : R.radialCoefficient outward nonzero r ≠ 0 := by
    apply norm_ne_zero_iff.mp
    rw [R.radialCoefficient_unit outward nonzero r hr]
    exact one_ne_zero
  rw [twoBankRatio, factor, mul_div_cancel_right₀ _ unit, polarRay_im]
  exact Real.sin_pos_of_pos_of_lt_pi positive small

/-- A source-only opening rotates both incident edge bearings and the radial vector together,
so the left and right occupied apertures add to exactly one full turn at every bend. -/
theorem sourceOpening_corner_widths_add (θ : ℝ) {m : ℕ} {B : PolygonalRay ℂ (m + 1)}
    (k : Fin m) :
    let Q := B.rotateSuffix 0 θ
    let r := B.chain.vertex k.succ.castSucc - B.start
    let q := Q.chain.vertex k.succ.castSucc - Q.start
    radialLeftCornerWidth r (B.chain.edge k.castSucc) (B.chain.edge k.succ) +
      radialRightCornerWidth q (Q.chain.edge k.castSucc) (Q.chain.edge k.succ) =
        2 * Real.pi := by
  dsimp only
  rw [B.rotateSuffix_zero_vertex_sub_start, B.rotateSuffix_zero_edge,
    B.rotateSuffix_zero_edge]
  simp only [complexRotation_apply, radialRightCornerWidth, radialLeftCornerWidth, neg_div_neg_eq,
    mul_div_mul_left _ _ (polarRay_ne_zero θ)]
  ring

end Unfoldings.PolygonalRay
