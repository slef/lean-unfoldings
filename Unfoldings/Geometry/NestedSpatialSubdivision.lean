module

public import Unfoldings.Geometry.NestedSpatialPieces
public import Unfoldings.Complex.FaceRestriction
public import Unfoldings.Complex.Subdivision

/-! Nested affine-roof meshes give actual isometric subdivisions of whole old faces. -/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialEnvelope.Triangulation

universe u

variable {I : Type u} [Fintype I] [Nonempty I] {family : I → SpatialPlane}
  {Z W : ℝ} (T : Triangulation family Z) (U : Triangulation family W)

local instance nestedSubdivisionOldFintype : Fintype T.Index := @Fintype.ofFinite _ T.finite
local instance nestedSubdivisionNewFintype : Fintype U.Index := @Fintype.ofFinite _ U.finite

open Classical in
/-- The physical subcomplex consisting of all pieces of old faces. -/
def nestedComplex := U.pairedComplex.restrictFaces (T.nestedPieceSet U)

/-- Whole old faces are covered by contained new triangles, including their boundary. -/
def FaceRefinement : Prop :=
  ∀ f : T.Index, ∀ p ∈ (T.projectedTriangle f).carrier, ∃ i : U.Index,
    (U.projectedTriangle i).carrier ⊆ (T.projectedTriangle f).carrier ∧
      p ∈ (U.projectedTriangle i).carrier

open Classical in
/-- The actual nested physical mesh subdivides every original Euclidean triangle. -/
def nestedSubdivision (cover : T.FaceRefinement U) :
    T.pairedComplex.Subdivision (T.nestedComplex U) where
  parent := T.nestedParent U
  place i := T.nestedPlace U i.val (T.nestedParent U i) (T.nestedParent_contains U i)
  inside i x member := T.nestedCoordinates_inside U i.val (T.nestedParent U i)
    (T.nestedParent_contains U i) member
  cover f x := by
    let p := (family (T.support f)).project x.val
    have projected : p ∈ (T.projectedTriangle f).carrier := by
      have member := x.property
      change x.val ∈ (T.triangle f).carrier at member
      rw [T.triangle_carrier] at member
      obtain ⟨q, member, same⟩ := member
      change (family (T.support f)).project x.val ∈ _
      rw [← same, (family (T.support f)).project.apply_symm_apply]
      exact member
    obtain ⟨i, contained, member⟩ := cover f p projected
    let piece : T.nestedPieceSet U := ⟨i, f, contained⟩
    let P := (family (U.support i)).project
    let y := P.symm p
    have fine : y ∈ (U.triangle i).carrier := by
      rw [U.triangle_carrier]
      exact ⟨p, member, rfl⟩
    have parent : T.nestedParent U piece = f := T.nestedParent_eq U piece contained
    refine ⟨piece, ⟨y, fine⟩, parent, ?_⟩
    rw [T.nestedPlace_apply]
    change (family (T.support (T.nestedParent U piece))).project.symm (P (P.symm p)) = x.val
    rw [P.apply_symm_apply, parent]
    exact (family (T.support f)).project.symm_apply_apply x.val

/-- Respecting every old side equation makes a covering mesh a genuine face refinement. -/
theorem faceRefinement_of_constraints {J : Type u} {extra : J → Plane →ᵃ[ℝ] ℝ}
    (V : ConstrainedTriangulation family extra W)
    (inclusion : clip family Z ⊆ clip family W)
    (label : T.Index × Fin 3 → J)
    (equations : ∀ j, extra (label j) = (T.projectedTriangle j.1).coord j.2) :
    T.FaceRefinement V.toTriangulation := by
  let := V.finite
  intro f
  apply (T.projectedTriangle f).covered_by_contained_cells V.projectedTriangle
    (fun _ member => V.cover.subset
      (inclusion (T.cover.symm.subset (Set.mem_iUnion.mpr ⟨f, member⟩))))
    (fun i k => V.signs i (label (f, k)))
  intro i p member k
  rw [← equations (f, k)]
  exact V.constrained i p member (label (f, k))

end Unfoldings.SpatialEnvelope.Triangulation
