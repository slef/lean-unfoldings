module

public import Unfoldings.Cap.ClipRealization
public import Unfoldings.Metric.ConvexCover

/-! Uniform intrinsic metric bounds for the actual assembled roof clips. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap.ClipSpatialTriangles

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexCap C} {Z : ℝ} (T : K.ClipSpatialTriangles Z)

local instance : Fintype T.Index := @Fintype.ofFinite _ T.finite

theorem paired_edist_ne_top (conforming : TriangleFamily.Conforming T.projectedTriangle)
    (x y : T.pairedComplex.Realization Set.univ) : edist x y ≠ ⊤ := by
  let := T.paired_preconnectedSpace conforming
  exact edist_ne_top_of_preconnected x y

/-- The physical roof clip carries its actual finite route metric. -/
@[instance_reducible] def pairedMetricSpace
    (conforming : TriangleFamily.Conforming T.projectedTriangle) :
    MetricSpace (T.pairedComplex.Realization Set.univ) :=
  EMetricSpace.toMetricSpace (T.paired_edist_ne_top conforming)

theorem paired_projection_lipschitz
    (conforming : TriangleFamily.Conforming T.projectedTriangle) :
    LipschitzWith 1 (T.pairedFootprintHomeomorph conforming) := by
  have horizontal : LipschitzWith 1 Cap.horizontal := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simpa only [NNReal.coe_one, one_mul, dist_eq_norm, ← map_sub] using
      Cap.horizontal_norm_le (x - y)
  have composition := horizontal.comp (T.pairedFolding.toSpace_lipschitz Set.univ)
  intro x y
  simpa only [mul_one, Subtype.edist_eq, Function.comp_apply,
    T.pairedFootprintHomeomorph_apply] using composition.edist_le_mul x y

/-- The inverse uses the physical metric, with a bound independent of clip size or mesh count. -/
theorem paired_inverse_projection_lipschitz
    (conforming : TriangleFamily.Conforming T.projectedTriangle)
    {c : ℝ} (positive : 0 < c) (height : ∀ f, c ≤ K.normal f 2) :
    LipschitzWith ⟨c⁻¹, inv_nonneg.mpr positive.le⟩
      (T.pairedFootprintHomeomorph conforming).symm := by
  let := T.pairedMetricSpace conforming
  let pieces (i : T.Index) : Set (K.clipFootprint Z) :=
    Subtype.val ⁻¹' (T.projectedTriangle i).carrier
  have closed (i : T.Index) : IsClosed (pieces i) :=
    (T.projectedTriangle i).compact_carrier.isClosed.preimage continuous_subtype_val
  have cover : (⋃ i, pieces i) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro p
    obtain ⟨i, member⟩ := Set.mem_iUnion.mp (T.cover.subset p.property)
    exact Set.mem_iUnion.mpr ⟨i, member⟩
  have inverse_copy (i : T.Index) (p : K.clipFootprint Z)
      (member : p.val ∈ (T.projectedTriangle i).carrier) :
      (T.pairedFootprintHomeomorph conforming).symm p = T.pointCopy i p.val member := by
    apply (T.pairedFootprintHomeomorph conforming).injective
    apply Subtype.ext
    exact (congrArg Subtype.val
      ((T.pairedFootprintHomeomorph conforming).apply_symm_apply p)).trans
        (T.pairedFootprintHomeomorph_pointCopy conforming i p.val member).symm
  have bounded (i : T.Index) :
      LipschitzOnWith ⟨c⁻¹, inv_nonneg.mpr positive.le⟩
        (T.pairedFootprintHomeomorph conforming).symm (pieces i) := by
    apply LipschitzOnWith.of_dist_le_mul
    intro p hp q hq
    change p.val ∈ (T.projectedTriangle i).carrier at hp
    change q.val ∈ (T.projectedTriangle i).carrier at hq
    let x := (K.projectFaceEquiv (T.face i)).symm p.val
    let y := (K.projectFaceEquiv (T.face i)).symm q.val
    have first : (T.pairedFootprintHomeomorph conforming).symm p =
        T.pairedComplex.faceMap Set.univ i
          ⟨x, (T.triangle_carrier i).symm.subset ⟨p.val, hp, rfl⟩⟩ := inverse_copy i p hp
    have last : (T.pairedFootprintHomeomorph conforming).symm q =
        T.pairedComplex.faceMap Set.univ i
          ⟨y, (T.triangle_carrier i).symm.subset ⟨q.val, hq, rfl⟩⟩ := inverse_copy i q hq
    rw [first, last, (T.pairedFolding.faceMap_isometry Set.univ i).dist_eq]
    change dist x y ≤ c⁻¹ * dist p.val q.val
    have lower : c * dist x y ≤ dist p.val q.val := by
      calc
        c * dist x y ≤ K.normal (T.face i) 2 * dist x y :=
          mul_le_mul_of_nonneg_right (height (T.face i)) dist_nonneg
        _ ≤ dist (K.projectFace (T.face i) x) (K.projectFace (T.face i) y) :=
          K.face_projection_lower (T.face i) x y
        _ = dist p.val q.val := congrArg₂ dist
          ((K.projectFaceEquiv (T.face i)).apply_symm_apply p.val)
          ((K.projectFaceEquiv (T.face i)).apply_symm_apply q.val)
    have result : dist x y ≤ dist p.val q.val / c := (le_div_iff₀ positive).mpr (by
      simpa only [mul_comm] using lower)
    simpa only [div_eq_mul_inv, mul_comm] using result
  exact convex_subtype_lipschitzWith_of_finite_closed_cover (K.clipFootprint Z)
    (K.convex_clipFootprint Z) pieces closed cover
    (T.pairedFootprintHomeomorph conforming).symm _ bounded

end Unfoldings.ConvexCap.ClipSpatialTriangles
