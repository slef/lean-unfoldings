module

public import Unfoldings.Polyhedron.FigureChain
public import Unfoldings.Polyhedron.FigureGermIncidence
public import Unfoldings.Topology.ChainPairings

/-!
# No repeated vertices in the actual cyclic figure chain

The exact incidence classification and the actual cyclic mate pairings
show that the initial endpoints of distinct ordered face sections differ.
-/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialFolding.VertexFigure

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {F : SpatialFolding C} {v : C.Vertex Set.univ} (V : F.VertexFigure v)
  {n : ℕ} (c : (C.linkSystem Set.univ v).Chain n)

theorem germPoint_chain_injective (embedded : F.IsEmbedded)
    (closes : C.linkMate Set.univ v (C.linkTurn Set.univ v c.last) = c.first) :
    Function.Injective (fun i => V.germPoint (c.point i)) := by
  intro i j equal
  rcases (V.germPoint_eq_iff embedded _ _).mp equal with same | paired
  · exact c.injective same
  · exact (c.mate_point_ne_point closes i j paired).elim

end Unfoldings.SpatialFolding.VertexFigure
