module

public import Unfoldings.Roof.CompletionMesh
public import Unfoldings.Geometry.ConstrainedTriangleCover
public import Unfoldings.Geometry.AffineSupport

/-! Whole original roof faces are covered by actual contained auxiliary Euclidean triangles. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexRoof C)

/-- The original projected triangle sides, using the original face and local corner names. -/
def originalEdgeEquations (i : Face × Fin 3) : Plane →ᵃ[ℝ] ℝ :=
  (K.projectedTriangle i.1).coord i.2

theorem originalEdgeEquations_ne_zero (i : Face × Fin 3) : K.originalEdgeEquations i ≠ 0 :=
  (K.projectedTriangle i.1).coord_ne_zero i.2

theorem projectedTriangle_subset_footprint (f : Face) :
    (K.projectedTriangle f).carrier ⊆ K.footprint := by
  rw [K.footprint_eq_union_projectedTriangles]
  exact Set.subset_iUnion (fun g => (K.projectedTriangle g).carrier) f

namespace CompletionMesh

variable {K} {φ : ℝ} {region : Set Plane}
  (E : K.CompletionMesh φ region K.originalEdgeEquations)

/-- The physical triangle partition underlying the constrained mesh. -/
abbrev partition := E.mesh.toTriangulation

theorem original_face_covered_by_contained_pieces (f : Face) :
    ∀ p ∈ (K.projectedTriangle f).carrier, ∃ i : E.partition.Index,
      (E.partition.projectedTriangle i).carrier ⊆ (K.projectedTriangle f).carrier ∧
        p ∈ (E.partition.projectedTriangle i).carrier := by
  let := E.partition.finite
  apply (K.projectedTriangle f).covered_by_contained_cells E.partition.projectedTriangle
    (fun _ member => E.partition.cover.subset
      (interior_subset (E.covers (Or.inl (K.projectedTriangle_subset_footprint f member)))))
    (fun i k => E.mesh.signs i (f, k))
  intro i p member k
  exact E.mesh.constrained i p member (f, k)

theorem original_parent_unique (i : E.partition.Index) {f g : Face}
    (first : (E.partition.projectedTriangle i).carrier ⊆ (K.projectedTriangle f).carrier)
    (last : (E.partition.projectedTriangle i).carrier ⊆ (K.projectedTriangle g).carrier) :
    f = g := by
  by_contra different
  obtain ⟨p, member⟩ := (E.partition.projectedTriangle i).interior_nonempty
  exact Set.disjoint_left.mp (K.projectedTriangles_nonoverlapping different)
    (interior_mono first member) (interior_mono last member)

/-- Auxiliary triangles contained in one whole original face. -/
def originalPieceSet : Set E.partition.Index :=
  {i | ∃ f : Face, (E.partition.projectedTriangle i).carrier ⊆ (K.projectedTriangle f).carrier}

def originalParent (i : E.originalPieceSet) : Face := i.property.choose

theorem originalParent_contains (i : E.originalPieceSet) :
    (E.partition.projectedTriangle i.val).carrier ⊆
      (K.projectedTriangle (E.originalParent i)).carrier :=
  i.property.choose_spec

theorem originalParent_eq (i : E.originalPieceSet) {f : Face}
    (contained : (E.partition.projectedTriangle i.val).carrier ⊆ (K.projectedTriangle f).carrier) :
    E.originalParent i = f := E.original_parent_unique i.val (E.originalParent_contains i) contained

theorem original_piece_cover (f : Face) (p : Plane) (member : p ∈ (K.projectedTriangle f).carrier) :
    ∃ i : E.originalPieceSet, E.originalParent i = f ∧
      p ∈ (E.partition.projectedTriangle i.val).carrier := by
  obtain ⟨i, contained, covered⟩ := E.original_face_covered_by_contained_pieces f p member
  let piece : E.originalPieceSet := ⟨i, f, contained⟩
  exact ⟨piece, E.originalParent_eq piece contained, covered⟩

end CompletionMesh
end Unfoldings.ConvexRoof
