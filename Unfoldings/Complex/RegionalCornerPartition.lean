module

public import Unfoldings.Complex.RegionalCorners

/-! Exact angular partitions of original corner stars into complementary face selections. -/

@[expose] public section

noncomputable section

namespace Unfoldings.TriangleComplex

universe u v

variable {Face : Type u} [Fintype Face] (C : TriangleComplex.{u, v} Face)

open Classical in
/-- Complementary selections retain each actual corner contribution exactly once. -/
theorem regionalCornerSum_add_compl (U : Set Face) (weight : C.Corner → ℝ)
    (w : C.Vertex Set.univ) :
    C.regionalCornerSum U weight w + C.regionalCornerSum Uᶜ weight w =
      ∑ c : C.Corner, if C.vertexOfCorner Set.univ c = w then weight c else 0 := by
  classical
  simp only [regionalCornerSum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro c _
  by_cases selected : c.1 ∈ U <;>
    by_cases same : C.vertexOfCorner Set.univ c = w <;> simp [selected, same]

/-- Arbitrary original corner weights add over disjoint selected face sets. -/
theorem regionalCornerSum_union {U V : Set Face} (disjoint : Disjoint U V)
    (weight : C.Corner → ℝ) (w : C.Vertex Set.univ) :
    C.regionalCornerSum (U ∪ V) weight w =
      C.regionalCornerSum U weight w + C.regionalCornerSum V weight w := by
  classical
  simp only [regionalCornerSum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro c _
  have exclusive : ¬ (c.1 ∈ U ∧ c.1 ∈ V) :=
    fun h => Set.disjoint_left.mp disjoint h.1 h.2
  by_cases first : c.1 ∈ U <;> by_cases last : c.1 ∈ V <;>
    by_cases same : C.vertexOfCorner Set.univ c = w <;> simp_all

end Unfoldings.TriangleComplex
