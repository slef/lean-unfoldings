module

public import Unfoldings.Roof.CompletionSharpRadialBudget
public import Unfoldings.Geometry.FiniteSegmentGerm
public import Unfoldings.Geometry.TriangleBoundary

/-! Old mesh regularity for the endpoints and the new corner of a radial closure. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof.CompletionMesh

open Filter Topology

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexRoof C} {φ : ℝ} {region : Set Plane} {I : Type u}
  {extra : I → Plane →ᵃ[ℝ] ℝ} (E : K.CompletionMesh φ region extra)

/-- A trimmed bank endpoint follows an actual old edge when its short ray
stays in the old triangle union and avoids the old face interiors. -/
theorem regularClosingCorner_of_locally_on_old_skeleton (J : Set Plane) (p bank closing : Plane)
    (not_vertex : ∀ old : E.mesh.Index, ¬ (E.mesh.projectedTriangle old).IsVertex p)
    (on_mesh : ∀ᶠ t : ℝ in 𝓝[>] 0, ∃ old : E.mesh.Index,
      p + t • bank ∈ (E.mesh.projectedTriangle old).carrier ∧
      p + t • bank ∉ interior (E.mesh.projectedTriangle old).carrier)
    (local_curve : ∀ᶠ x in 𝓝 p,
      x ∈ J → x - p ∈ nonnegativeRay bank ∪ nonnegativeRay closing) :
    E.RegularClosingCorner J p := by
  let : Finite E.mesh.Index := E.mesh.finite
  let first (e : E.mesh.Index × Fin 3) := (E.mesh.projectedTriangle e.1).vertex e.2
  let last (e : E.mesh.Index × Fin 3) :=
    (E.mesh.projectedTriangle e.1).vertex (Triangle.next e.2)
  have follows : ∀ᶠ t : ℝ in 𝓝[>] 0, p + t • bank ∈ ⋃ e, segment ℝ (first e) (last e) := by
    filter_upwards [on_mesh] with t ht
    obtain ⟨old, belongs, outside⟩ := ht
    obtain ⟨e, edge⟩ := (E.mesh.projectedTriangle old).exists_edge_of_not_mem_interior
      ⟨p + t • bank, belongs⟩ outside
    exact Set.mem_iUnion.mpr ⟨(old, e), edge⟩
  obtain ⟨⟨old, edge⟩, at_edge, k, aligns⟩ :=
    exists_incident_segment_of_ray_germ first last p bank follows
  exact Or.inr ⟨old, edge, k, closing, at_edge, not_vertex old, aligns ▸ local_curve⟩

/-- A closing point on the old mesh and off all old edges is in the
interior of one old face. -/
theorem regularClosingCorner_of_off_old_edges (J : Set Plane) (p : Plane)
    (on_mesh : ∃ old : E.mesh.Index, p ∈ (E.mesh.projectedTriangle old).carrier)
    (off_edges : ∀ (old : E.mesh.Index) (e : Fin 3), p ∉ (E.mesh.projectedTriangle old).edge e) :
    E.RegularClosingCorner J p := by
  obtain ⟨old, member⟩ := on_mesh
  refine Or.inl ⟨old, ?_⟩
  by_contra outside
  obtain ⟨e, edge⟩ := (E.mesh.projectedTriangle old).exists_edge_of_not_mem_interior
    ⟨p, member⟩ outside
  exact off_edges old e edge

end Unfoldings.ConvexRoof.CompletionMesh
