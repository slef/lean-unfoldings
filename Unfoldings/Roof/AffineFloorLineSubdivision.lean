module

public import Unfoldings.Roof.AffineFloorLineRefinement
public import Unfoldings.Complex.Subdivision

/-! The physical comparison mesh subdivides each coarse triangle in its original coordinates. -/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialEnvelope.FloorMesh.LineRefinement

universe u

variable {I J : Type u} [Fintype I] [Nonempty I]
  {family : I → SpatialPlane} {floor : Plane →ᵃ[ℝ] ℝ} {Z : ℝ}
  {extra : J → Plane →ᵃ[ℝ] ℝ} {T : FloorMesh family floor extra Z}
  {A : Type u} {equation : A → Plane →ᵃ[ℝ] ℝ} (L : T.LineRefinement equation)

local instance coarseIndexFintype : Fintype T.Index := @Fintype.ofFinite _ T.finite
local instance childIndexFintype : Fintype L.mesh.Index := @Fintype.ofFinite _ L.mesh.finite

/-- Each closed coarse triangle is covered by the children of its actual parent label. -/
theorem projected_parent_cover (f : T.Index) :
    (T.projectedTriangle f).carrier =
      ⋃ g : {g : L.mesh.Index // L.parent g = f}, (L.mesh.projectedTriangle g.val).carrier := by
  let patch := ⋃ g : {g : L.mesh.Index // L.parent g = f}, (L.mesh.projectedTriangle g.val).carrier
  have closed : IsClosed patch :=
    isClosed_iUnion_of_finite fun g => (L.mesh.projectedTriangle g.val).compact_carrier.isClosed
  have fine (p : Plane) (hp : p ∈ interior (T.projectedTriangle f).carrier) : p ∈ patch := by
    have in_floor := T.cover.symm.subset
      (Set.mem_iUnion.mpr ⟨f, interior_subset hp⟩)
    obtain ⟨g, member⟩ := Set.mem_iUnion.mp (L.mesh.cover.subset in_floor)
    have same : L.parent g = f := by
      by_contra distinct
      rcases T.conforming f (L.parent g) (fun equal => distinct equal.symm) p
        ⟨interior_subset hp, L.contained g member⟩ with shared | ⟨e, _, _, edge⟩
      · obtain ⟨e, at_corner⟩ := shared.1
        apply (T.projectedTriangle f).not_mem_interior_of_mem_edge e _ hp
        rw [← at_corner]
        exact left_mem_segment ℝ _ _
      · exact (T.projectedTriangle f).not_mem_interior_of_mem_edge e edge hp
    exact Set.mem_iUnion.mpr ⟨⟨g, same⟩, member⟩
  have all := closure_minimal fine closed
  rw [(T.projectedTriangle f).convex_carrier.closure_interior_eq_closure_of_nonempty_interior
      (T.projectedTriangle f).interior_nonempty,
    (T.projectedTriangle f).compact_carrier.isClosed.closure_eq] at all
  refine Set.Subset.antisymm all ?_
  intro p on_patch
  obtain ⟨g, inside⟩ := Set.mem_iUnion.mp on_patch
  have member := L.contained g.val inside
  rwa [g.property] at member

/-- The new physical coordinates are literally the old face coordinates because
the same support placement is used on each child. -/
def subdivision : T.pairedComplex.Subdivision L.mesh.pairedComplex where
  parent := L.parent
  place _ := AffineIsometryEquiv.refl ℝ Plane
  inside g x contained := by
    change x ∈ (L.mesh.triangle g).carrier at contained
    change x ∈ (T.triangle (L.parent g)).carrier
    rw [L.mesh.triangle_carrier, L.same_support] at contained
    rw [T.triangle_carrier]
    obtain ⟨p, member, rfl⟩ := contained
    exact ⟨p, L.contained g member, rfl⟩
  cover f x := by
    have member : x.val ∈ (T.triangle f).carrier := x.property
    rw [T.triangle_carrier] at member
    obtain ⟨p, inside, same⟩ := member
    rw [L.projected_parent_cover f] at inside
    obtain ⟨g, fine⟩ := Set.mem_iUnion.mp inside
    let y := (family (T.support f)).project.symm p
    have fine_point : y ∈ (L.mesh.triangle g.val).carrier := by
      rw [L.mesh.triangle_carrier, L.same_support, g.property]
      exact ⟨p, fine, rfl⟩
    exact ⟨g.val, ⟨y, fine_point⟩, g.property, same⟩

/-- Refinement is exact in ambient physical space, including along shared seams. -/
theorem subdivision_spatial (g : L.mesh.Index) (x : Plane) :
    T.pairedFolding.place (L.subdivision.parent g) (L.subdivision.place g x) =
      L.mesh.pairedFolding.place g x := by
  change (family (T.support (L.parent g))).place x = (family (L.mesh.support g)).place x
  rw [L.same_support]

end Unfoldings.SpatialEnvelope.FloorMesh.LineRefinement
