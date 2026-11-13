module

public import Unfoldings.Roof.CompletionMesh
public import Unfoldings.Roof.SkirtRadialCuts
public import Unfoldings.Roof.OriginalCutLabels

/-! Actual exterior corners are selected before the radial continuation mesh is constructed. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof.CompletionMesh

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexRoof C} {φ : ℝ} {region : Set Plane} {J : Type u}
  {extra : J → Plane →ᵃ[ℝ] ℝ} (E : K.CompletionMesh φ region extra)

local instance completionSkirtIndexFinite : Finite E.mesh.Index := E.mesh.finite

/-- Include all preceding exterior mesh corners and every original rim corner. -/
def skirtSeedSet : Set Plane :=
  (Set.range (fun a : E.mesh.Index × Fin 3 => (E.mesh.projectedTriangle a.1).vertex a.2) ∪
    Set.range (fun a : Face × Fin 3 => (K.projectedTriangle a.1).vertex a.2)) \ interior K.footprint

theorem finite_skirtSeedSet : E.skirtSeedSet.Finite :=
  ((Set.finite_range _).union (Set.finite_range _)).subset Set.sdiff_subset

theorem skirtSeedSet_subset : E.skirtSeedSet ⊆
    SpatialEnvelope.clip (K.completionPlanes E.tentHeight (Real.sin φ / 2)) E.level := by
  rintro p ⟨(⟨⟨i, k⟩, rfl⟩ | ⟨⟨f, k⟩, rfl⟩), _outside⟩
  · exact E.mesh.cover.symm.subset
      (Set.mem_iUnion.mpr ⟨i, (E.mesh.projectedTriangle i).vertex_mem k⟩)
  · exact interior_subset (E.covers (Or.inl
      (K.projectedVertex_mem_footprint (C.vertexOfCorner Set.univ (f, k)))))

/-- All chosen tails live on the actual compact completion domain. -/
def cornerTails {q : Plane} (origin : q ∈ interior K.footprint) :
    K.SkirtTailFamily
      (SpatialEnvelope.clip (K.completionPlanes E.tentHeight (Real.sin φ / 2)) E.level) q := by
  let := E.finite_skirtSeedSet.to_subtype
  have compact : IsCompact (SpatialEnvelope.clip
      (K.completionPlanes E.tentHeight (Real.sin φ / 2)) E.level) := by
    rw [E.mesh.cover]
    exact isCompact_iUnion (fun i => (E.mesh.projectedTriangle i).compact_carrier)
  exact K.skirtTailFamily origin compact
    (AffineEnvelope.convex_clip _ E.level) (fun _ member => E.covers (Or.inl member))
    (fun p : E.skirtSeedSet => p.val) (fun p => E.skirtSeedSet_subset p.property)
    (fun p => p.property.2)

theorem cornerTails_original_rim_corner {q : Plane} (origin : q ∈ interior K.footprint)
    (f : Face) (k : Fin 3) (rim : (K.projectedTriangle f).vertex k ∉ interior K.footprint) :
    (K.projectedTriangle f).vertex k ∈ ⋃ c : (E.cornerTails origin).Component,
      ((E.cornerTails origin).componentTail c).carrier :=
  (E.cornerTails origin).seeds_covered ⟨_, Or.inr ⟨(f, k), rfl⟩, rim⟩

theorem cornerTails_covers_rim {q : Plane} (origin : q ∈ interior K.footprint)
    (w : C.Vertex Set.univ) (boundary : C.IsBoundaryVertex Set.univ w) :
    K.projectedVertex w ∈ ⋃ c : (E.cornerTails origin).Component,
      ((E.cornerTails origin).componentTail c).carrier := by
  obtain ⟨⟨f, k⟩, at_corner⟩ := C.vertexOfCorner_surjective Set.univ w
  have equal : (K.projectedTriangle f).vertex k = K.projectedVertex w :=
    (K.projectedVertex_ofCorner f k).symm.trans (congrArg K.projectedVertex at_corner)
  have rim : (K.projectedTriangle f).vertex k ∉ interior K.footprint := by
    intro member
    exact ((K.projectedVertex_mem_interior_iff w).mp (equal ▸ member)) boundary
  exact equal ▸ E.cornerTails_original_rim_corner origin f k rim

end Unfoldings.ConvexRoof.CompletionMesh
