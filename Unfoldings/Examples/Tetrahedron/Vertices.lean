module

public import Unfoldings.Examples.Tetrahedron.Boundary
public import Unfoldings.Complex.CutSeamGraph

/-! The metric tetrahedron has exactly its four declared vertex classes. -/

@[expose] public section

noncomputable section

namespace Unfoldings.Examples.Tetrahedron

def vertexIndex : complex.Vertex Set.univ → Fin 4 :=
  Quotient.lift (fun c => corner c.1 c.2) (by
    intro c d related
    have points := congrArg (folding.toSpace Set.univ)
      (MetricGluing.point_eq_of_eqvGen complex.Cell related)
    change placement c.1 ((triangle c.1).vertex c.2) =
      placement d.1 ((triangle d.1).vertex d.2) at points
    rw [placement_vertex, placement_vertex] at points
    exact vertex_injective points)

@[simp] theorem vertexIndex_corner (f : Fin 4) (i : Fin 3) :
    vertexIndex (complex.vertexOfCorner Set.univ (f, i)) = corner f i := rfl

theorem vertexIndex_injective : Function.Injective vertexIndex := by
  intro v w equal
  obtain ⟨⟨f, i⟩, rfl⟩ := complex.vertexOfCorner_surjective Set.univ v
  obtain ⟨⟨g, j⟩, rfl⟩ := complex.vertexOfCorner_surjective Set.univ w
  apply complex.vertexPoint_injective Set.univ
  apply embedded
  change placement f ((triangle f).vertex i) = placement g ((triangle g).vertex j)
  rw [placement_vertex, placement_vertex]
  exact congrArg vertex equal

theorem vertexIndex_surjective : Function.Surjective vertexIndex := by
  intro i
  let f : Fin 4 := if i = 0 then 1 else 0
  have different : i ≠ f := by
    dsimp [f]
    split_ifs with zero
    · exact zero ▸ (by decide : (0 : Fin 4) ≠ 1)
    · exact zero
  obtain ⟨j, equal⟩ := corner_surjective_away f i different
  exact ⟨complex.vertexOfCorner Set.univ (f, j), equal⟩

def vertexEquiv : complex.Vertex Set.univ ≃ Fin 4 :=
  Equiv.ofBijective vertexIndex ⟨vertexIndex_injective, vertexIndex_surjective⟩

@[simp] theorem vertexIndex_cutSeamVertex (retain : Set complex.Seam)
    (s : complex.CutSeam retain) (b : Bool) :
    vertexIndex (complex.cutSeamVertex retain s b) = endpointLabel (left s.val) b := by
  cases b <;> rfl

end Unfoldings.Examples.Tetrahedron
