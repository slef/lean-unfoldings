module

public import Unfoldings.Convex.ExteriorRayFaceGerms
public import Unfoldings.Convex.ExteriorSpatialRays
public import Unfoldings.Geometry.SpatialEnvelopeHalfspaceChart
public import Unfoldings.Metric.PlanarRayCutBanks

/-! Entire original exterior ray banks in the actual one-ray cut, with exact spatial speed. -/

@[expose] public section

noncomputable section

open scoped NNReal ENNReal

namespace Unfoldings.SlopeEnvelope.ExteriorPlan

variable {E : SlopeEnvelope} {V : Type*} (R : E.ExteriorPlan V) (M : E.FiniteSlopeModel)
  {A : Type} [Finite A] (P : SpatialEnvelope.WholePartition M.plane A)
  (v : V) (anchor : A) (signs : A → Bool)
  (aligned : ∀ a x, x ∈ P.footprint a →
    0 ≤ AffineArrangement.signed (orientMap (R.point v) (R.ray v 1)) (signs a) x)
  (T : ℝ) (tail : ∀ t : ℝ, T ≤ t → R.ray v t ∈ P.footprint anchor)

/-- An eventual cell's actual support contains the entire closed positive ray in its
convex face-side region, even where the ray has left that individual partition cell. -/
def faceSideRaySource (t : ℝ≥0) : PolygonalPoint
    ((M.plane (P.support anchor)).project.symm ''
      P.faceSideRegion anchor (orientMap (R.point v) (R.ray v 1)) signs) :=
  ⟨(M.plane (P.support anchor)).project.symm (R.ray v t.val), by
    refine ⟨R.ray v t.val, ⟨?_, ?_⟩, rfl⟩
    · exact (AffineEnvelope.mem_cell_iff _ _ _).mpr
        (R.terminal_cell_support_active M P v anchor T tail t.val t.property)
    · change 0 ≤ AffineArrangement.signed
        (orientMap (R.point v) (R.ray v 1)) (signs anchor) (R.ray v t.val)
      rw [← R.ray_lineMap v t.val, AffineArrangement.signed_apply, orientMap_apply,
        orient_lineMap]
      split <;> norm_num⟩

/-- The complete one-sided bank, including its source, in the original cut metric.
No terminal cutoff is part of its domain. -/
def faceSideRayBank (t : ℝ≥0) : P.Cut (MetricGluing.rayCut (R.point v) (R.ray v 1)) :=
  P.faceSideRegionMap anchor (orientMap (R.point v) (R.ray v 1))
    (orientMap_ne_zero (R.ray_endpoints_ne v)) signs aligned
    (MetricGluing.rayCut (R.point v) (R.ray v 1))
    (MetricGluing.isClosed_rayCut (R.point v) (R.ray v 1))
    (MetricGluing.rayCut_on_line (R.point v) (R.ray v 1))
    (R.faceSideRaySource M P v anchor signs T tail t)

/-- Every point folds to the actual spatial roof ray, with its full height component. -/
theorem restoreCut_faceSideRayBank (t : ℝ≥0) :
    (P.restoreCut (MetricGluing.rayCut (R.point v) (R.ray v 1))
      (R.faceSideRayBank M P v anchor signs aligned T tail t)).val =
        SpatialEnvelope.point M.plane (R.ray v t.val) := by
  unfold faceSideRayBank
  rw [P.restoreCut_faceSideRegionMap]
  exact (SpatialEnvelope.point_eq_place M.plane (P.support anchor)
    (R.terminal_cell_support_active M P v anchor T tail t.val t.property)).symm

/-- Exact distances along the entire original bank, with the intrinsic spatial speed. -/
theorem edist_faceSideRayBank (s t : ℝ≥0) :
    edist (R.faceSideRayBank M P v anchor signs aligned T tail s)
      (R.faceSideRayBank M P v anchor signs aligned T tail t) =
        (‖R.spatialDirection v‖₊ : ℝ≥0∞) * edist s t := by
  let f := orientMap (R.point v) (R.ray v 1)
  have proper : f ≠ 0 := orientMap_ne_zero (R.ray_endpoints_ne v)
  let cuts := MetricGluing.rayCut (R.point v) (R.ray v 1)
  have closed : IsClosed cuts := MetricGluing.isClosed_rayCut (R.point v) (R.ray v 1)
  have level : ∀ x ∈ cuts, f x = 0 := by
    rintro x ⟨u, rfl⟩
    exact MetricGluing.rayCut_on_line (R.point v) (R.ray v 1) _ ⟨u, rfl⟩
  let source := R.faceSideRaySource M P v anchor signs T tail
  have convex := (P.convex_faceSideRegion anchor f signs).affine_image
    (M.plane (P.support anchor)).project.symm.toAffineMap
  calc
    _ = edist (source s) (source t) :=
      (P.faceSideRegionMap_isometry anchor f proper signs aligned cuts closed level).edist_eq _ _
    _ = edist (source s).val (source t).val :=
      PolygonalPoint.edist_eq_of_segment
        (convex.segment_subset (source s).property (source t).property)
    _ = edist (SpatialEnvelope.point M.plane (R.ray v s.val))
        (SpatialEnvelope.point M.plane (R.ray v t.val)) := by
      rw [SpatialEnvelope.point_eq_place M.plane (P.support anchor)
        (R.terminal_cell_support_active M P v anchor T tail s.val s.property),
        SpatialEnvelope.point_eq_place M.plane (P.support anchor)
        (R.terminal_cell_support_active M P v anchor T tail t.val t.property),
        (M.plane (P.support anchor)).place.isometry.edist_eq]
      rfl
    _ = _ := R.edist_spatial_ray M v s.property t.property

/-- The whole bank is a dilation of a closed Euclidean half-line. -/
def faceSideRayBankDilation : ℝ≥0 →ᵈ P.Cut
    (MetricGluing.rayCut (R.point v) (R.ray v 1)) where
  toFun := R.faceSideRayBank M P v anchor signs aligned T tail
  edist_eq' := ⟨‖R.spatialDirection v‖₊,
    nnnorm_ne_zero_iff.mpr (R.spatialDirection_ne_zero v),
    R.edist_faceSideRayBank M P v anchor signs aligned T tail⟩

theorem faceSideRayBank_isClosedEmbedding :
    Topology.IsClosedEmbedding (R.faceSideRayBank M P v anchor signs aligned T tail) :=
  Dilation.isClosedEmbedding (R.faceSideRayBankDilation M P v anchor signs aligned T tail)

/-- Every positive point of the whole bank has a whole original rigid halfplane ball.
The cut line and the support face germ are derived from the actual exterior ray. -/
theorem exists_faceSideRayBank_chart (t : ℝ≥0) (positive : 0 < t.val) :
    ∃ ε : ℝ, 0 < ε ∧
      ∃ a : P.faceSideHalfspace anchor (orientMap (R.point v) (R.ray v 1)) signs,
        a.val = (M.plane (P.support anchor)).project.symm (R.ray v t.val) ∧
        ∃ B : Metric.eball (R.faceSideRayBank M P v anchor signs aligned T tail t)
          (ENNReal.ofReal ε) ≃ᵢ Metric.ball a ε,
          ∀ y, (M.plane (P.support anchor)).place (B y).val.val =
            (P.restoreCut (MetricGluing.rayCut (R.point v) (R.ray v 1)) y.val).val := by
  let Q := M.plane (P.support anchor)
  let source := R.faceSideRaySource M P v anchor signs T tail t
  have horizontal : Cap.horizontal (Q.place source.val) = R.ray v t.val :=
    (Q.horizontal_place _).trans (Q.project.apply_symm_apply _)
  obtain ⟨δ, δpos, face⟩ := R.terminal_cell_ray_germ M P v anchor T tail (signs anchor)
    (aligned anchor) positive
  apply P.exists_faceSideHalfspace_ball_chart anchor
    (orientMap (R.point v) (R.ray v 1)) (orientMap_ne_zero (R.ray_endpoints_ne v)) signs aligned
    (MetricGluing.rayCut (R.point v) (R.ray v 1))
    (MetricGluing.isClosed_rayCut (R.point v) (R.ray v 1))
    (MetricGluing.rayCut_on_line (R.point v) (R.ray v 1)) source
    (isOpen_rayForwardHalfspace (R.point v) (R.ray v 1))
  · intro z forward zero
    obtain ⟨s, spos, expression⟩ := exists_positive_ray_parameter
      (R.ray_endpoints_ne v) forward zero
    exact ⟨⟨s, spos.le⟩, expression.symm⟩
  · rw [horizontal, ← R.ray_lineMap v t.val]
    exact lineMap_mem_rayForwardHalfspace (R.ray_endpoints_ne v) positive
  · exact δpos
  · intro z near on_side
    exact face z (horizontal ▸ near) on_side

end Unfoldings.SlopeEnvelope.ExteriorPlan
