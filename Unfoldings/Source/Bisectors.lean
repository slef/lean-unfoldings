module

public import Unfoldings.Source.TerminalUniqueness

/-!
# Actual nonunique face-interior endpoints lie on finitely many genuine bisectors

The virtual images of actual terminal motions realize source distance.
Distinct shortest paths have distinct terminal images, by the proved final
continuation theorem. Thus their equal lengths give a genuine perpendicular
bisector, rather than an equality between coincident candidate images.
-/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialFolding.ConvexBoundary

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {F : SpatialFolding C} (P : F.ConvexBoundary)

def sourceImages :
    letI := P.metricSpace
    {source : C.Realization Set.univ} → (R : SourceFrame source) →
      C.PointFiber Set.univ source → Set Plane := by
  let := P.metricSpace
  intro source R base
  exact (fun A : Plane ≃ᵃⁱ[ℝ] Plane => A.symm 0) '' P.sourceMotionCandidates R base

theorem finite_sourceImages :
    letI := P.metricSpace
    ∀ {source : C.Realization Set.univ} (R : SourceFrame source)
      (base : C.PointFiber Set.univ source), (P.sourceImages R base).Finite := by
  let := P.metricSpace
  intro source R base
  exact (P.finite_sourceMotionCandidates R base).image _

def sourceBisectors :
    letI := P.metricSpace
    {source : C.Realization Set.univ} → (R : SourceFrame source) →
      C.PointFiber Set.univ source → Set Plane := by
  let := P.metricSpace
  intro source R base
  exact ⋃ v ∈ P.sourceImages R base, ⋃ w ∈ P.sourceImages R base,
    ⋃ (_different : v ≠ w), {x | dist x v = dist x w}

theorem isClosed_sourceBisectors :
    letI := P.metricSpace
    ∀ {source : C.Realization Set.univ} (R : SourceFrame source)
      (base : C.PointFiber Set.univ source), IsClosed (P.sourceBisectors R base) := by
  let := P.metricSpace
  intro source R base
  exact (P.finite_sourceImages R base).isClosed_biUnion (fun v _ =>
    (P.finite_sourceImages R base).isClosed_biUnion (fun w _ =>
      isClosed_iUnion_of_finite (fun _ => isClosed_eq
        (continuous_id.dist continuous_const) (continuous_id.dist continuous_const))))

theorem source_terminal_image_distance :
    letI := P.metricSpace
    ∀ {source : C.Realization Set.univ} (R : SourceFrame source) (f : Face) (x : C.Cell f)
      (p : SourcePath source), p.target = C.faceMap Set.univ f x →
      ∀ (A : Plane ≃ᵃⁱ[ℝ] Plane) (a : unitInterval),
        (∀ t : unitInterval, a ≤ t → F.toSpace Set.univ (p.path t) =
          F.place f (A.symm ((t : ℝ) • R.coordinate p.path p.geodesic))) →
        dist x.val (A.symm 0) = dist source (C.faceMap Set.univ f x) := by
  let := P.metricSpace
  intro source R f x p target A a formula
  have inverse := P.source_terminal_inverse_endpoint R f x p target A a formula
  have value : A x.val = R.coordinate p.path p.geodesic := by
    rw [← inverse, A.apply_symm_apply]
  calc
    dist x.val (A.symm 0) = dist (A x.val) (A (A.symm 0)) := (A.isometry.dist_eq _ _).symm
    _ = ‖R.coordinate p.path p.geodesic‖ := by rw [A.apply_symm_apply, value, dist_zero_right]
    _ = dist source (C.faceMap Set.univ f x) :=
      (R.norm_coordinate p.path p.geodesic).trans (congrArg (dist source) target)

theorem nonunique_face_interior_mem_sourceBisectors :
    letI := P.metricSpace
    ∀ {source : C.Realization Set.univ} (R : SourceFrame source)
      (base : C.PointFiber Set.univ source) (f : Face) (x : C.Cell f),
      x.val ∈ interior (C.triangle f).carrier →
      C.faceMap Set.univ f x ∈ nonuniqueSourcePoints source → x.val ∈ P.sourceBisectors R base := by
  let := P.metricSpace
  intro source R base f x inside nonunique
  obtain ⟨p, q, geodesic_p, geodesic_q, different⟩ := nonunique
  let sp : SourcePath source := ⟨C.faceMap Set.univ f x, p, geodesic_p⟩
  let sq : SourcePath source := ⟨C.faceMap Set.univ f x, q, geodesic_q⟩
  obtain ⟨A, member_A, a, before_a, formula_A⟩ :=
    P.exists_source_terminal_formula_in_face R base f x inside sp rfl
  obtain ⟨B, member_B, b, before_b, formula_B⟩ :=
    P.exists_source_terminal_formula_in_face R base f x inside sq rfl
  have images_different : A.symm 0 ≠ B.symm 0 := by
    intro equal
    have paths := P.sourcePaths_eq_of_terminal_image R f x sp sq rfl rfl A B a b
      before_a before_b formula_A formula_B equal
    apply different
    ext t
    exact congrArg (fun r : SourcePath source => r.path t) paths
  have lengths := (P.source_terminal_image_distance R f x sp rfl A a formula_A).trans
    (P.source_terminal_image_distance R f x sq rfl B b formula_B).symm
  simp only [sourceBisectors, Set.mem_iUnion, Set.mem_ofPred_eq]
  exact ⟨A.symm 0, ⟨A, member_A, rfl⟩, B.symm 0, ⟨B, member_B, rfl⟩, images_different, lengths⟩

end Unfoldings.SpatialFolding.ConvexBoundary
