module

public import Unfoldings.Roof.GradientSelection
public import Unfoldings.Roof.ProjectedLink
public import Unfoldings.Polyhedron.GermDirections

/-! Actual supporting inequalities along incident spatial edge rays. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexRoof C)

theorem normalSlope_inner_add_height (f : Face) (z : Space) :
    inner ℝ (K.normalSlope f) (Cap.horizontal z) + z 2 =
      (K.normal f 2)⁻¹ * inner ℝ (K.normal f) z := by
  rw [normalSlope, real_inner_smul_left, Cap.horizontal_inner, mul_add,
    ← mul_assoc, inv_mul_cancel₀ (K.normal_upward f).ne', one_mul]

variable {v : C.Vertex Set.univ}

theorem horizontal_germDirection (p : C.LinkGerm Set.univ v) :
    Cap.horizontal (K.folding.germDirection p.val) = K.projectedGermRay p := by
  rw [SpatialFolding.germDirection, map_sub, K.folding.linkGerm_apex Set.univ v p]
  rfl

/-- Each incident face supports every actual edge direction at this vertex. -/
theorem incident_normal_germ_nonpos (a : C.CornerAt Set.univ v)
    (p : C.LinkGerm Set.univ v) :
    inner ℝ (K.normal a.val.1) (K.folding.germDirection p.val) ≤ 0 := by
  let f := a.val.1
  let x := (C.triangle f).vertex a.val.2
  have apex : K.folding.place f x = K.folding.toSpace Set.univ (C.vertexPoint Set.univ v) := by
    rw [← a.property]
    rfl
  have support := K.supporting f (C.germFarCorner p.val).1
    ⟨(C.triangle (C.germFarCorner p.val).1).vertex (C.germFarCorner p.val).2,
      (C.triangle _).vertex_mem _⟩
  have tangent := K.normal_tangent_chord f x 0
  rw [inner_sub_right] at support tangent
  rw [apex] at tangent
  rw [SpatialFolding.germDirection, inner_sub_right, K.folding.linkGerm_apex Set.univ v p]
  change inner ℝ (K.normal f) (K.folding.germFarPoint p.val) -
    inner ℝ (K.normal f) (K.folding.toSpace Set.univ (C.vertexPoint Set.univ v)) ≤ 0
  change inner ℝ (K.normal f) (K.folding.germFarPoint p.val) -
    inner ℝ (K.normal f) (K.folding.place f 0) ≤ 0 at support
  linarith

/-- The scalar product on a face is bounded above by every incident support plane. -/
def germUpperForm (v : C.Vertex Set.univ) (n : Space)
    (a : C.CornerAt Set.univ v) : Plane →ₗ[ℝ] ℝ :=
  (innerSL ℝ (Cap.horizontal n)).toLinearMap -
    n 2 • (innerSL ℝ (K.normalSlope a.val.1)).toLinearMap

theorem germUpperForm_apply (n : Space) (a : C.CornerAt Set.univ v) (q : Plane) :
    K.germUpperForm v n a q =
      inner ℝ (Cap.horizontal n) q - n 2 * inner ℝ (K.normalSlope a.val.1) q := rfl

theorem germUpperForm_bound (n : Space) (upward : 0 < n 2)
    (a : C.CornerAt Set.univ v) (p : C.LinkGerm Set.univ v) :
    inner ℝ n (K.folding.germDirection p.val) ≤
      K.germUpperForm v n a (K.projectedGermRay p) := by
  have support := K.incident_normal_germ_nonpos a p
  have scaled := mul_nonpos_of_nonneg_of_nonpos
    (inv_nonneg.mpr (K.normal_upward a.val.1).le) support
  rw [← K.normalSlope_inner_add_height,
    K.horizontal_germDirection] at scaled
  rw [germUpperForm_apply, Cap.horizontal_inner, K.horizontal_germDirection]
  nlinarith

theorem germUpperForm_own (n : Space) (p : C.LinkGerm Set.univ v) :
    K.germUpperForm v n ⟨p.val.1, p.property⟩ (K.projectedGermRay p) =
      inner ℝ n (K.folding.germDirection p.val) := by
  obtain ⟨x, equal⟩ := K.folding.germDirection_mem_range p.val
  have tangent : inner ℝ (K.normal p.val.1.1) (K.folding.germDirection p.val) = 0 := by
    rw [← equal]
    exact K.normal_tangent _ x
  have scaled := congrArg (fun t : ℝ => (K.normal p.val.1.1 2)⁻¹ * t) tangent
  rw [← K.normalSlope_inner_add_height, mul_zero, K.horizontal_germDirection] at scaled
  change inner ℝ (Cap.horizontal n) (K.projectedGermRay p) -
    n 2 * inner ℝ (K.normalSlope p.val.1.1) (K.projectedGermRay p) = _
  rw [Cap.horizontal_inner, K.horizontal_germDirection]
  linear_combination -(n 2) * scaled

end Unfoldings.ConvexRoof
