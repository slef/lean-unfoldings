module

public import Unfoldings.Source.SeamEndpointTransition
public import Unfoldings.Complex.SeamWordMotion

/-! Actual oriented source-motion transitions between tagged face copies. -/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialFolding.ConvexBoundary

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {F : SpatialFolding C} (P : F.ConvexBoundary)

def sourceTaggedMotion :
    letI := P.metricSpace
    {source : C.Realization Set.univ} → (R : SourceFrame source) → (a : C.Total) →
      (MetricGluing.point C.Cell (C.glue Set.univ) a ∉ sourceCutLocus source) →
        (Plane ≃ᵃⁱ[ℝ] Plane) := by
  let := P.metricSpace
  intro source R a outside
  exact P.sourceFaceMotion R a.1 ⟨a.2, outside⟩

theorem sourceTaggedMotion_congr :
    letI := P.metricSpace
    ∀ {source : C.Realization Set.univ} (R : SourceFrame source) {a b : C.Total}, a = b →
      ∀ outside_a : MetricGluing.point C.Cell (C.glue Set.univ) a ∉ sourceCutLocus source,
        ∀ outside_b : MetricGluing.point C.Cell (C.glue Set.univ) b ∉ sourceCutLocus source,
          P.sourceTaggedMotion R a outside_a = P.sourceTaggedMotion R b outside_b := by
  let := P.metricSpace
  intro source R a b equal outside_a outside_b
  cases equal
  rfl

theorem sourceTaggedMotion_seam :
    letI := P.metricSpace
    ∀ {source : C.Realization Set.univ} (R : SourceFrame source) (s : C.Seam) (side : Bool)
      (q : (C.triangle (C.seamSide s side).face).Edge (C.seamSide s side).edge),
      ∀ outside_a : MetricGluing.point C.Cell (C.glue Set.univ)
          (C.edgePoint (C.seamSide s side) q) ∉ sourceCutLocus source,
        ∀ outside_b : MetricGluing.point C.Cell (C.glue Set.univ)
            (C.edgePoint (C.seamSide s (!side)) (C.across s side q)) ∉ sourceCutLocus source,
          P.sourceTaggedMotion R
            (C.edgePoint (C.seamSide s (!side)) (C.across s side q)) outside_b =
          (C.seamTransition s side).trans
            (P.sourceTaggedMotion R (C.edgePoint (C.seamSide s side) q) outside_a) := by
  let := P.metricSpace
  intro source R s side q outside_a outside_b
  cases side
  · exact P.sourceFaceMotion_seam R s q outside_a outside_b
  · let left_q := (C.identify s).symm q
    have edge : C.identify s left_q = q := (C.identify s).apply_symm_apply q
    have right_outside : C.faceMap Set.univ (C.right s).face
        ((C.triangle (C.right s).face).edgeMap (C.right s).edge (C.identify s left_q)) ∉
          sourceCutLocus source := by
      rw [edge]
      exact outside_a
    have actual := P.sourceFaceMotion_seam R s left_q outside_b right_outside
    simp only [edge] at actual
    change P.sourceFaceMotion R (C.left s).face
        ⟨(C.triangle (C.left s).face).edgeMap (C.left s).edge left_q, outside_b⟩ =
      (C.seamHinge s).place.symm.trans (P.sourceFaceMotion R (C.right s).face
        ⟨(C.triangle (C.right s).face).edgeMap (C.right s).edge q, outside_a⟩)
    rw [actual]
    ext z
    simp only [AffineIsometryEquiv.coe_trans, Function.comp_apply,
      AffineIsometryEquiv.apply_symm_apply]

end Unfoldings.SpatialFolding.ConvexBoundary
