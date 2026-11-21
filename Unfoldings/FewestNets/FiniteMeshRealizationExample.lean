module

public import Unfoldings.FewestNets.FiniteMeshExample
public import Unfoldings.FewestNets.IcosahedronInteriorDualEdges

/-! The first frequency-100 length checks apply to genuine Voronoi network arcs. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FewestNets.Icosahedron

open InnerProductGeometry MeshStar

/-- Each of the six verified sides in the first record is an actual edge
with that angular length in every corresponding frequency-100 face star. -/
theorem actual_meshEdge_short_q100_face_one_one (f : Fin 20) (k : Fin 6) :
    ∃ e : MeshEdge 100,
      angle (meshEndpoint (by decide : 0 < 100) e false) (meshEndpoint (by decide) e true) <
        2 * (icosahedronEdge / 100) := by
  have same : modelInteriorStar 100 1 98 = face 100 1 1 :=
    modelInteriorStar_eq_face (by decide : 1 + 98 < 100)
  have outward (i : Fin 6) : 0 < inner ℝ (modelInteriorStar 100 1 98).direction
      ((modelInteriorStar 100 1 98).dual i) := by
    rw [same]
    exact (dualAngle_q100_face_one_one i).1
  obtain ⟨e, eq⟩ := exists_meshEdge_angle_eq_interiorStar
    (by decide : 100 ≤ 100) (by decide) f
    (by decide : 0 < 1) (by decide : 0 < 98) (by decide : 1 + 98 < 100)
    k (outward k) (outward (k + 1))
  refine ⟨e, ?_⟩
  rw [eq, same]
  exact (dualAngle_q100_face_one_one k).2

end Unfoldings.FewestNets.Icosahedron
