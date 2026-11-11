module

public import Unfoldings.Cap.ClippedCap
public import Unfoldings.Cap.UniformCurvature

/-! Uniform curvature control includes every actual vertex of every conforming roof clip. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap.ClipSpatialTriangles

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexCap C} {Z : ℝ} (T : K.ClipSpatialTriangles Z)

local instance clipCurvatureIndexFintype : Fintype T.Index := @Fintype.ofFinite _ T.finite

/-- The same normal budget controls original and newly introduced clip vertices together. -/
theorem totalCurvature_le_normal_budget
    (conforming : TriangleFamily.Conforming T.projectedTriangle) (lower : Z < 0)
    {c : ℝ} (height_lower : (3 : ℝ) / 4 ≤ c) (height : ∀ f, c ≤ K.normal f 2) :
    T.pairedComplex.totalInteriorAngularDefect Set.univ ≤
      81 * (Real.sqrt (1 - c ^ 2) / c) ^ 2 * Real.pi :=
  (T.normalizedCap conforming lower).totalCurvature_le_normal_budget height_lower
    (fun i => height (T.face i))

end Unfoldings.ConvexCap.ClipSpatialTriangles

namespace Unfoldings.ConvexCap

universe u v

/-- Choose a single numerical threshold before the original mesh, the clip height,
and every extra refinement used for its physical triangulation. -/
theorem exists_uniform_tilt_clipCurvature_lt {ε : ℝ} (positive : 0 < ε) :
    ∃ φ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      ∀ {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
        (K : ConvexCap C), K.TiltBound φ →
        ∀ {Z : ℝ} (T : K.ClipSpatialTriangles Z),
          TriangleFamily.Conforming T.projectedTriangle → Z < 0 →
            @TriangleComplex.totalInteriorAngularDefect T.Index (@Fintype.ofFinite _ T.finite)
              T.pairedComplex Set.univ < ε := by
  obtain ⟨φ, bounds, lower, budget⟩ := exists_positive_tilt_curvature_budget positive
  exact ⟨φ, bounds, fun K tilt _Z T conforming clipped =>
    (T.totalCurvature_le_normal_budget conforming clipped lower tilt).trans_lt budget⟩

end Unfoldings.ConvexCap
