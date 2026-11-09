module

public import Unfoldings.Source.TerminalPiece

/-!
# A terminal virtual source determines the whole shortest path

In one original endpoint face, the terminal inverse rigid formula is the
straight line from its virtual source to the endpoint. Equal virtual sources
therefore give a common final path interval. Actual convex-surface geodesic
continuation proves equality of the whole original paths.
-/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialFolding.ConvexBoundary

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {F : SpatialFolding C} (P : F.ConvexBoundary)

theorem source_terminal_inverse_endpoint :
    letI := P.metricSpace
    ∀ {source : C.Realization Set.univ} (R : SourceFrame source) (f : Face) (x : C.Cell f)
      (p : SourcePath source), p.target = C.faceMap Set.univ f x →
      ∀ (A : Plane ≃ᵃⁱ[ℝ] Plane) (a : unitInterval),
        (∀ t : unitInterval, a ≤ t → F.toSpace Set.univ (p.path t) =
          F.place f (A.symm ((t : ℝ) • R.coordinate p.path p.geodesic))) →
        A.symm (R.coordinate p.path p.geodesic) = x.val := by
  let := P.metricSpace
  intro source R f x p target A a formula
  have endpoint := formula 1 a.property.2
  simp only [Path.target, Set.Icc.coe_one, one_smul] at endpoint
  have placed : F.toSpace Set.univ p.target = F.place f x.val :=
    (congrArg (F.toSpace Set.univ) target).trans (F.toSpace_faceMap _ _ _)
  exact ((F.place f).injective (placed.symm.trans endpoint)).symm

theorem sourcePaths_eq_of_terminal_image :
    letI := P.metricSpace
    ∀ {source : C.Realization Set.univ} (R : SourceFrame source) (f : Face) (x : C.Cell f)
      (p q : SourcePath source), p.target = C.faceMap Set.univ f x →
      q.target = C.faceMap Set.univ f x →
      ∀ (A B : Plane ≃ᵃⁱ[ℝ] Plane) (a b : unitInterval), a < 1 → b < 1 →
        (∀ t : unitInterval, a ≤ t → F.toSpace Set.univ (p.path t) =
          F.place f (A.symm ((t : ℝ) • R.coordinate p.path p.geodesic))) →
        (∀ t : unitInterval, b ≤ t → F.toSpace Set.univ (q.path t) =
          F.place f (B.symm ((t : ℝ) • R.coordinate q.path q.geodesic))) →
        A.symm 0 = B.symm 0 → p = q := by
  let := P.metricSpace
  intro source R f x p q target_p target_q A B a b before_a before_b formula_p formula_q images
  by_cases constant : p.target = source
  · have constant_q : q.target = source := target_q.trans (target_p.symm.trans constant)
    apply SourcePath.ext
    intro t
    exact (SourcePath.eq_source_of_target_eq constant t).trans
      (SourcePath.eq_source_of_target_eq constant_q t).symm
  have endpoint_p := P.source_terminal_inverse_endpoint R f x p target_p A a formula_p
  have endpoint_q := P.source_terminal_inverse_endpoint R f x q target_q B b formula_q
  have line_p (t : unitInterval) : A.symm ((t : ℝ) • R.coordinate p.path p.geodesic) =
      AffineMap.lineMap (A.symm 0) x.val (t : ℝ) := by
    have equal := A.symm.toAffineMap.apply_lineMap
      (0 : Plane) (R.coordinate p.path p.geodesic) (t : ℝ)
    change A.symm (AffineMap.lineMap 0 (R.coordinate p.path p.geodesic) (t : ℝ)) =
      AffineMap.lineMap (A.symm 0) (A.symm (R.coordinate p.path p.geodesic)) (t : ℝ) at equal
    rw [endpoint_p] at equal
    simpa only [AffineMap.lineMap_apply_module', sub_zero, add_zero] using equal
  have line_q (t : unitInterval) : B.symm ((t : ℝ) • R.coordinate q.path q.geodesic) =
      AffineMap.lineMap (B.symm 0) x.val (t : ℝ) := by
    have equal := B.symm.toAffineMap.apply_lineMap
      (0 : Plane) (R.coordinate q.path q.geodesic) (t : ℝ)
    change B.symm (AffineMap.lineMap 0 (R.coordinate q.path q.geodesic) (t : ℝ)) =
      AffineMap.lineMap (B.symm 0) (B.symm (R.coordinate q.path q.geodesic)) (t : ℝ) at equal
    rw [endpoint_q] at equal
    simpa only [AffineMap.lineMap_apply_module', sub_zero, add_zero] using equal
  have final_agreement : ∃ ε : unitInterval, ε < 1 ∧ ∀ t, ε ≤ t → p.path t = q.path t := by
    refine ⟨max a b, max_lt before_a before_b, ?_⟩
    intro t after
    apply P.embedded
    rw [formula_p t ((le_max_left _ _).trans after),
      formula_q t ((le_max_right _ _).trans after), line_p, line_q, images]
  exact SourcePath.ext (P.geodesics_eq_of_final_interval p.geodesic q.geodesic
    (Ne.symm constant) final_agreement)

end Unfoldings.SpatialFolding.ConvexBoundary
