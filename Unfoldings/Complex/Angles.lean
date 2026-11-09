module

public import Unfoldings.Complex.Vertices
public import Unfoldings.Geometry.Angles

/-!
# Total angles at cut vertex copies

Every original corner contributes its actual positive Euclidean angle to exactly
one retained-seam vertex class. Cutting partitions these contributions rather
than assigning new curvature to an unrelated abstract vertex type.
-/

@[expose] public section

noncomputable section

namespace Unfoldings.TriangleComplex

universe u v

variable {Face : Type u} [Fintype Face] (C : TriangleComplex.{u, v} Face)

/-- The sum of the original Euclidean corner angles in one retained vertex class. -/
def totalAngle (retain : Set C.Seam) (v : C.Vertex retain) : ℝ := by
  classical
  exact ∑ c : C.Corner,
    if C.vertexOfCorner retain c = v then (C.triangle c.1).cornerAngle c.2 else 0

theorem totalAngle_pos (retain : Set C.Seam) (v : C.Vertex retain) : 0 < C.totalAngle retain v := by
  classical
  obtain ⟨c, rfl⟩ := C.vertexOfCorner_surjective retain v
  unfold totalAngle
  have nonnegative (d : C.Corner) : 0 ≤
      (if C.vertexOfCorner retain d = C.vertexOfCorner retain c then
        (C.triangle d.1).cornerAngle d.2 else 0) := by
    split_ifs
    · exact (C.triangle d.1).cornerAngle_pos d.2 |>.le
    · exact le_rfl
  exact (Finset.sum_pos_iff_of_nonneg (fun d _ => nonnegative d)).mpr
    ⟨c, Finset.mem_univ c, by simpa using (C.triangle c.1).cornerAngle_pos c.2⟩

theorem sum_totalAngle (retain : Set C.Seam) :
    ∑ v : C.Vertex retain, C.totalAngle retain v = Fintype.card Face * Real.pi := by
  classical
  calc
    _ = ∑ c : C.Corner, (C.triangle c.1).cornerAngle c.2 := by
      simp only [totalAngle]
      rw [Finset.sum_comm]
      simp
    _ = _ := by
      rw [Fintype.sum_prod_type]
      simp [Triangle.sum_cornerAngle, nsmul_eq_mul]

open scoped Classical in
/-- The angles of all cut copies add up to the original vertex angle. -/
theorem sum_totalAngle_vertexForgetCuts {retain retain' : Set C.Seam}
    (inclusion : retain ⊆ retain') (v : C.Vertex retain') :
    (∑ w : C.Vertex retain,
      if C.vertexForgetCuts inclusion w = v then C.totalAngle retain w else 0) =
        C.totalAngle retain' v := by
  classical
  simpa only [totalAngle, Finset.sum_filter, Finset.mem_filter, Finset.mem_univ,
    true_and, C.vertexForgetCuts_vertexOfCorner] using
    Finset.sum_fiberwise_eq_sum_filter (Finset.univ : Finset C.Corner)
      (Finset.univ.filter fun w => C.vertexForgetCuts inclusion w = v)
      (C.vertexOfCorner retain) (fun c => (C.triangle c.1).cornerAngle c.2)

end Unfoldings.TriangleComplex
