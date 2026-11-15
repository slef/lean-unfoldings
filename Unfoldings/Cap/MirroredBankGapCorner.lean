module

public import Unfoldings.Cap.SplitBankSector
public import Unfoldings.Complex.BoundaryChainAperture
public import Unfoldings.Geometry.TwoBankGapInternalCorner
public import Unfoldings.Geometry.ConjugateGapAngle

/-! Mirrored original banks retain the complementary cap aperture in their opposite orientation. -/

@[expose] public section

noncomputable section

open scoped NNReal

namespace Unfoldings.ConvexCap

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexCap C)
  {retain : Set C.Seam} {n m : ℕ}
  (chain : (C.boundarySystem retain).Chain (n + 1))
  (R : PolygonalRay ℂ (n + 2)) (Q : PolygonalRay ℂ m)
  (first_outward : R.Outward) (first_nonzero : R.direction ≠ 0)
  (last_outward : Q.Outward) (last_nonzero : Q.direction ≠ 0)
  (positive_phase : ∀ r : ℝ≥0, 0 < r →
    0 < (R.twoBankRatio Q first_outward first_nonzero last_outward last_nonzero r).im)

include K in
/-- When the first bank mirrors the actual original intrinsic boundary roll, its derived metric
corner has exactly the complementary retained cap angle. A distinct original cut copy
supplies the strict full-turn bound; no complementary aperture is assumed. -/
theorem exists_first_mirrored_bank_complement_chart (common : Q.start = R.start)
    (matching : R.chain = (C.boundaryChainRoll chain).conjugate) (k : Fin (n + 1))
    (z : C.Vertex retain)
    (distinct : C.boundaryEndVertex retain (chain.point k.succ) ≠ z)
    (same : C.vertexForgetCuts (Set.subset_univ retain) z =
      C.vertexForgetCuts (Set.subset_univ retain)
        (C.boundaryEndVertex retain (chain.point k.succ)))
    (internal : ¬ C.IsBoundaryVertex Set.univ (C.vertexForgetCuts (Set.subset_univ retain)
      (C.boundaryEndVertex retain (chain.point k.succ))))
    (outgoing_radial : 0 < inner ℝ (R.chain.vertex k.succ.castSucc - R.start)
      (R.chain.vertex k.succ.succ - R.chain.vertex k.succ.castSucc)) :
    let p := R.chain.vertex k.succ.castSucc
    let width := 2 * Real.pi - C.totalAngle retain
      (C.boundaryEndVertex retain (chain.point k.succ))
    let frame := radialLeftCornerFrame (p - R.start) (R.chain.vertex k.succ.succ - p)
    ∃ (positive : 0 < width) (small : width < 2 * Real.pi),
      ∃ δ : ℝ, 0 < δ ∧ ∃ A : Metric.eball
        (R.twoBankFirstVertexPoint Q first_outward first_nonzero last_outward last_nonzero
          positive_phase common k.succ.castSucc) (ENNReal.ofReal δ) ≃ᵢ
        Metric.eball (bisectedSectorFan width positive small).origin (ENNReal.ofReal δ),
        ∀ y, p + frame ((bisectedSectorFan width positive small).develop (A y).val) =
          y.val.val := by
  dsimp only
  have genuine (i : Fin (n + 2)) : R.chain.vertex i.castSucc ≠ R.chain.vertex i.succ := by
    intro equal
    have nonzero : ((C.boundaryChainRoll chain).conjugate).edge i ≠ 0 := by
      rw [PolygonalChain.conjugate_edge]
      simpa only [map_zero] using
        (starRingEnd ℂ).injective.ne (C.boundaryChainRoll_edge_ne_zero chain i)
    apply nonzero
    rw [← matching, PolygonalChain.edge, equal, sub_self]
  obtain ⟨positive, small, angle, δ, δpos, A, physical⟩ :=
    R.exists_first_internal_vertex_chart Q first_outward first_nonzero last_outward last_nonzero
      positive_phase common genuine k outgoing_radial
  have actual_angle := C.boundaryChainRoll_complementary_angle chain k
    (K.split_bank_totalAngle_lt_full _ z distinct same internal)
  have mirror_angle := (C.boundaryChainRoll chain).conjugate_left_aperture k
    (C.boundaryChainRoll_edge_ne_zero chain k.castSucc)
    (C.boundaryChainRoll_edge_ne_zero chain k.succ)
  have bank_angle : positiveGapAngle
      (R.chain.vertex k.succ.succ - R.chain.vertex k.succ.castSucc)
      (-(R.chain.vertex k.succ.castSucc - R.chain.vertex k.castSucc.castSucc)) =
        2 * Real.pi - C.totalAngle retain (C.boundaryEndVertex retain (chain.point k.succ)) := by
    simpa only [← matching, PolygonalChain.edge, Fin.succ_castSucc] using
      mirror_angle.trans actual_angle
  have width_eq := angle.trans bank_angle
  have result : ∃ (positive : 0 < radialLeftCornerWidth
      (R.chain.vertex k.succ.castSucc - R.start)
      (R.chain.vertex k.succ.castSucc - R.chain.vertex k.castSucc.castSucc)
      (R.chain.vertex k.succ.succ - R.chain.vertex k.succ.castSucc))
      (small : radialLeftCornerWidth (R.chain.vertex k.succ.castSucc - R.start)
        (R.chain.vertex k.succ.castSucc - R.chain.vertex k.castSucc.castSucc)
        (R.chain.vertex k.succ.succ - R.chain.vertex k.succ.castSucc) < 2 * Real.pi),
      ∃ δ : ℝ, 0 < δ ∧ ∃ A : Metric.eball
        (R.twoBankFirstVertexPoint Q first_outward first_nonzero last_outward last_nonzero
          positive_phase common k.succ.castSucc) (ENNReal.ofReal δ) ≃ᵢ
        Metric.eball (bisectedSectorFan _ positive small).origin (ENNReal.ofReal δ),
        ∀ y, R.chain.vertex k.succ.castSucc + radialLeftCornerFrame
          (R.chain.vertex k.succ.castSucc - R.start)
          (R.chain.vertex k.succ.succ - R.chain.vertex k.succ.castSucc)
          ((bisectedSectorFan _ positive small).develop (A y).val) = y.val.val :=
    ⟨positive, small, δ, δpos, A, physical⟩
  rwa [width_eq] at result

end Unfoldings.ConvexCap
