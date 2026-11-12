module

public import Unfoldings.Complex.Vertices

/-! Forgetting cuts preserves exactly the intrinsic vertex points. -/

@[expose] public section

noncomputable section

namespace Unfoldings.TriangleComplex

universe u v

variable {Face : Type u} [Fintype Face] (C : TriangleComplex.{u, v} Face)

theorem forgetCuts_mem_range_vertexPoint_iff {small large : Set C.Seam}
    (inclusion : small ⊆ large) (x : C.Realization small) :
    C.forgetCuts inclusion x ∈ Set.range (C.vertexPoint large) ↔
      x ∈ Set.range (C.vertexPoint small) := by
  obtain ⟨⟨f, a⟩, rfl⟩ := MetricGluing.point_surjective C.Cell (C.glue small) x
  change C.forgetCuts inclusion (C.faceMap small f a) ∈ Set.range (C.vertexPoint large) ↔ _
  rw [C.forgetCuts_faceMap]
  exact (C.mem_range_vertexPoint_iff large ⟨f, a⟩).trans
    (C.mem_range_vertexPoint_iff small ⟨f, a⟩).symm

/-- A fiber through a vertex consists only of vertex copies of that same original vertex. -/
theorem exists_vertex_copy_of_forgetCuts_eq {small large : Set C.Seam}
    (inclusion : small ⊆ large) (v : C.Vertex small) (y : C.Realization small)
    (same : C.forgetCuts inclusion (C.vertexPoint small v) = C.forgetCuts inclusion y) :
    ∃ w : C.Vertex small, C.vertexPoint small w = y ∧
      C.vertexForgetCuts inclusion v = C.vertexForgetCuts inclusion w := by
  have original_vertex : C.forgetCuts inclusion y ∈ Set.range (C.vertexPoint large) :=
    ⟨C.vertexForgetCuts inclusion v,
      (C.vertexPoint_vertexForgetCuts inclusion v).trans same⟩
  obtain ⟨w, equal⟩ := (C.forgetCuts_mem_range_vertexPoint_iff inclusion y).mp original_vertex
  refine ⟨w, equal, C.vertexPoint_injective large ?_⟩
  rw [C.vertexPoint_vertexForgetCuts, C.vertexPoint_vertexForgetCuts, equal]
  exact same

end Unfoldings.TriangleComplex
