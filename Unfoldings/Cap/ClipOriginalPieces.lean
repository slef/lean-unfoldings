module

public import Unfoldings.Cap.ConstrainedClipTriangles
public import Unfoldings.Cap.ClipOriginalCoordinates
public import Unfoldings.Geometry.ConstrainedTriangleCover

/-! Actual contained fine roof triangles cover every whole original input face. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap.LineAlignedClip

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexCap C} {Z : ℝ} (L : K.LineAlignedClip Z K.originalEdgeEquations)

theorem original_face_covered_by_contained_pieces (lower : Z < 0) (f : Face) :
    ∀ p ∈ (K.projectedTriangle f).carrier, ∃ i : L.partition.Index,
      (L.partition.projectedTriangle i).carrier ⊆ (K.projectedTriangle f).carrier ∧
        p ∈ (L.partition.projectedTriangle i).carrier := by
  let := L.partition.finite
  apply (K.projectedTriangle f).covered_by_contained_cells L.partition.projectedTriangle
    (fun _ member => L.partition.cover.subset
      (K.projectedTriangle_subset_clippedSupportCell lower.le f member).1)
    (fun i k => L.signs i ((Fintype.equivFin Face) f, k))
  intro i p member k
  simpa only [ConvexCap.originalEdgeEquations, Equiv.symm_apply_apply] using
    L.side i p member ((Fintype.equivFin Face) f, k)

theorem original_parent_unique (i : L.partition.Index) {f g : Face}
    (first : (L.partition.projectedTriangle i).carrier ⊆ (K.projectedTriangle f).carrier)
    (last : (L.partition.projectedTriangle i).carrier ⊆ (K.projectedTriangle g).carrier) :
    f = g := by
  by_contra different
  obtain ⟨p, member⟩ := (L.partition.projectedTriangle i).interior_nonempty
  exact Set.disjoint_left.mp (K.projectedTriangles_nonoverlapping different)
    (interior_mono first member) (interior_mono last member)

def originalPieceSet : Set L.partition.Index :=
  {i | ∃ f : Face, (L.partition.projectedTriangle i).carrier ⊆ (K.projectedTriangle f).carrier}

def originalParent (i : L.originalPieceSet) : Face := i.property.choose

theorem originalParent_contains (i : L.originalPieceSet) :
    (L.partition.projectedTriangle i.val).carrier ⊆
      (K.projectedTriangle (L.originalParent i)).carrier :=
  i.property.choose_spec

theorem originalParent_eq (i : L.originalPieceSet) {f : Face}
    (contained : (L.partition.projectedTriangle i.val).carrier ⊆ (K.projectedTriangle f).carrier) :
    L.originalParent i = f := L.original_parent_unique i.val (L.originalParent_contains i) contained

theorem original_piece_cover (lower : Z < 0) (f : Face) (p : Plane)
    (member : p ∈ (K.projectedTriangle f).carrier) :
    ∃ i : L.originalPieceSet, L.originalParent i = f ∧
      p ∈ (L.partition.projectedTriangle i.val).carrier := by
  obtain ⟨i, contained, covered⟩ := L.original_face_covered_by_contained_pieces lower f p member
  let piece : L.originalPieceSet := ⟨i, f, contained⟩
  exact ⟨piece, L.originalParent_eq piece contained, covered⟩

end Unfoldings.ConvexCap.LineAlignedClip
