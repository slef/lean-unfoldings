module

public import Unfoldings.Polyhedron.GermRays
public import Unfoldings.Topology.ChainPairings

/-! The actual initial unit directions in a cyclic embedded link are all distinct. -/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialFolding

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  (F : SpatialFolding C)

theorem linkDirection_chain_injective (embedded : F.IsEmbedded)
    {v : C.Vertex Set.univ} {n : ℕ} (c : (C.linkSystem Set.univ v).Chain n)
    (closes : C.linkMate Set.univ v (C.linkTurn Set.univ v c.last) = c.first) :
    Function.Injective (fun i => F.germUnitDirection (c.point i).val) := by
  intro i j equal
  rcases (F.linkGerm_unitDirection_eq_iff embedded _ _).mp equal with same | paired
  · exact c.injective same
  · exact (c.mate_point_ne_point closes i j paired).elim

end Unfoldings.SpatialFolding
