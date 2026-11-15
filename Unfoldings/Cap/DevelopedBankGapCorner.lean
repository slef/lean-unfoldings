module

public import Unfoldings.Cap.SplitBankSector
public import Unfoldings.Development.BoundaryChainAperture
public import Unfoldings.Geometry.TwoBankGapSecondInternalCorner

/-! Actual physical developed banks give complementary intrinsic gap-corner charts. -/

@[expose] public section

noncomputable section

open scoped NNReal

namespace Unfoldings.ConvexCap

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexCap C)
  {retain : Set C.Seam} (D : FacewiseDevelopment C retain) {n m : ℕ}
  (chain : (C.boundarySystem retain).Chain (m + 1))
  (R : PolygonalRay ℂ n) (Q : PolygonalRay ℂ (m + 2))
  (first_outward : R.Outward) (first_nonzero : R.direction ≠ 0)
  (last_outward : Q.Outward) (last_nonzero : Q.direction ≠ 0)
  (positive_phase : ∀ r : ℝ≥0, 0 < r →
    0 < (R.twoBankRatio Q first_outward first_nonzero last_outward last_nonzero r).im)

include K in
/-- When the second bank follows the actual developed original boundary edges, its derived
metric corner has exactly the complementary retained cap angle. A distinct original cut copy
supplies the strict full-turn bound; no complementary aperture is assumed. -/
theorem exists_second_developed_bank_complement_chart (common : Q.start = R.start)
    (matching : ∀ i : Fin (m + 2), Q.chain.edge i =
      D.boundaryCycleFrame chain (D.boundaryRay (chain.point i))) (k : Fin (m + 1))
    (z : C.Vertex retain)
    (distinct : C.boundaryEndVertex retain (chain.point k.succ) ≠ z)
    (same : C.vertexForgetCuts (Set.subset_univ retain) z =
      C.vertexForgetCuts (Set.subset_univ retain)
        (C.boundaryEndVertex retain (chain.point k.succ)))
    (internal : ¬ C.IsBoundaryVertex Set.univ (C.vertexForgetCuts (Set.subset_univ retain)
      (C.boundaryEndVertex retain (chain.point k.succ))))
    (outgoing_radial : 0 < inner ℝ (Q.chain.vertex k.succ.castSucc - Q.start)
      (Q.chain.vertex k.succ.succ - Q.chain.vertex k.succ.castSucc)) :
    let p := Q.chain.vertex k.succ.castSucc
    let incoming := p - Q.chain.vertex k.castSucc.castSucc
    let width := 2 * Real.pi - C.totalAngle retain
      (C.boundaryEndVertex retain (chain.point k.succ))
    let frame := radialRightCornerFrame (p - Q.start) incoming
    ∃ (positive : 0 < width) (small : width < 2 * Real.pi),
      ∃ δ : ℝ, 0 < δ ∧ ∃ A : Metric.eball
        (R.twoBankSecondVertexPoint Q first_outward first_nonzero last_outward last_nonzero
          positive_phase common k.succ.castSucc) (ENNReal.ofReal δ) ≃ᵢ
        Metric.eball (bisectedSectorFan width positive small).origin (ENNReal.ofReal δ),
        ∀ y, p + frame ((bisectedSectorFan width positive small).develop (A y).val) =
          y.val.val := by
  dsimp only
  have genuine (i : Fin (m + 2)) : Q.chain.vertex i.castSucc ≠ Q.chain.vertex i.succ := by
    intro equal
    have nonzero : Q.chain.edge i ≠ 0 := by
      rw [matching i]
      simpa only [map_zero] using (D.boundaryCycleFrame chain).injective.ne
        (D.boundaryRay_ne_zero (chain.point i))
    exact nonzero (by rw [PolygonalChain.edge, equal, sub_self])
  obtain ⟨positive, small, angle, δ, δpos, A, physical⟩ :=
    R.exists_second_internal_vertex_chart Q first_outward first_nonzero last_outward last_nonzero
      positive_phase common genuine k outgoing_radial
  have actual_angle := D.boundaryChain_complementary_angle chain k
    (K.split_bank_totalAngle_lt_full _ z distinct same internal)
  have bank_angle : positiveGapAngle
      (-(Q.chain.vertex k.succ.castSucc - Q.chain.vertex k.castSucc.castSucc))
      (Q.chain.vertex k.succ.succ - Q.chain.vertex k.succ.castSucc) =
        2 * Real.pi - C.totalAngle retain (C.boundaryEndVertex retain (chain.point k.succ)) := by
    rw [← matching k.castSucc, ← matching k.succ] at actual_angle
    simpa only [PolygonalChain.edge, Fin.succ_castSucc] using actual_angle
  have width_eq := angle.trans bank_angle
  have result : ∃ (positive : 0 < radialRightCornerWidth
      (Q.chain.vertex k.succ.castSucc - Q.start)
      (Q.chain.vertex k.succ.castSucc - Q.chain.vertex k.castSucc.castSucc)
      (Q.chain.vertex k.succ.succ - Q.chain.vertex k.succ.castSucc))
      (small : radialRightCornerWidth (Q.chain.vertex k.succ.castSucc - Q.start)
        (Q.chain.vertex k.succ.castSucc - Q.chain.vertex k.castSucc.castSucc)
        (Q.chain.vertex k.succ.succ - Q.chain.vertex k.succ.castSucc) < 2 * Real.pi),
      ∃ δ : ℝ, 0 < δ ∧ ∃ A : Metric.eball
        (R.twoBankSecondVertexPoint Q first_outward first_nonzero last_outward last_nonzero
          positive_phase common k.succ.castSucc) (ENNReal.ofReal δ) ≃ᵢ
        Metric.eball (bisectedSectorFan _ positive small).origin (ENNReal.ofReal δ),
        ∀ y, Q.chain.vertex k.succ.castSucc + radialRightCornerFrame
          (Q.chain.vertex k.succ.castSucc - Q.start)
          (Q.chain.vertex k.succ.castSucc - Q.chain.vertex k.castSucc.castSucc)
          ((bisectedSectorFan _ positive small).develop (A y).val) = y.val.val :=
    ⟨positive, small, δ, δpos, A, physical⟩
  rwa [width_eq] at result

end Unfoldings.ConvexCap
