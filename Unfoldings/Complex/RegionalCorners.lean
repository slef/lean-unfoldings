module

public import Unfoldings.Complex.Angles

/-! Summing actual corner contributions over arbitrary unions of original faces. -/

@[expose] public section

noncomputable section

namespace Unfoldings.TriangleComplex

universe u v

variable {Face : Type u} [Fintype Face] (C : TriangleComplex.{u, v} Face)

/-- A vertex's complete original corner star belongs to this actual face selection. -/
def FullStarIn (faces : Set Face) (v : C.Vertex Set.univ) : Prop :=
  ∀ c : C.Corner, C.vertexOfCorner Set.univ c = v → c.1 ∈ faces

/-- Add specified contributions only from selected faces at this actual original vertex. -/
def regionalCornerSum (faces : Set Face) (weight : C.Corner → ℝ) (v : C.Vertex Set.univ) : ℝ := by
  classical
  exact ∑ c : C.Corner, if c.1 ∈ faces ∧ C.vertexOfCorner Set.univ c = v then weight c else 0

open scoped Classical in
theorem sum_regionalCornerSum (faces : Set Face) (weight : C.Corner → ℝ) :
    (∑ v : C.Vertex Set.univ, C.regionalCornerSum faces weight v) =
      ∑ c : C.Corner, if c.1 ∈ faces then weight c else 0 := by
  classical
  simp only [regionalCornerSum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro c _
  by_cases present : c.1 ∈ faces <;> simp [present]

open scoped Classical in
/-- Complete stars retain all contributions, with no manifold or region-boundary certificate. -/
theorem regionalCornerSum_of_fullStar (faces : Set Face) (weight : C.Corner → ℝ)
    (v : C.Vertex Set.univ) (full : C.FullStarIn faces v) :
    C.regionalCornerSum faces weight v =
      ∑ c : C.Corner, if C.vertexOfCorner Set.univ c = v then weight c else 0 := by
  classical
  apply Finset.sum_congr rfl
  intro c _
  by_cases same : C.vertexOfCorner Set.univ c = v
  · simp only [same, full c same, and_self, ite_eq_left]
  · simp only [same, and_false, ite_false]

end Unfoldings.TriangleComplex
