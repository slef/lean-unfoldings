module

public import Unfoldings.Complex.SubdivisionInteriors
public import Unfoldings.Geometry.HingeConverse
public import Unfoldings.Geometry.Hinge

/-! Restrict developments to conforming subdivisions, preserving edge opening and nonoverlap. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FacewiseDevelopment

universe u v w z

variable {Face : Type u} [Fintype Face] {Child : Type w} [Fintype Child]
  {C : TriangleComplex.{u, v} Face} {D : TriangleComplex.{w, z} Child}
  {retain : Set C.Seam} {fineRetain : Set D.Seam}
  (E : FacewiseDevelopment C retain) (S : C.Subdivision D)
  (H : S.Conforming retain fineRetain)

def childPlace (g : Child) : Plane ≃ᵃⁱ[ℝ] Plane := (S.place g).trans (E.place (S.parent g))

include H in
theorem childPlace_joined (s : D.Seam) (kept : s ∈ fineRetain)
    (x : (D.triangle (D.left s).face).Edge (D.left s).edge) :
    E.childPlace S (D.left s).face x.val =
      E.childPlace S (D.right s).face (D.identify s x).val :=
  congrArg E.toPlane ((C.point_eq_iff retain _ _).mpr
    (H.respects _ _ ⟨s, kept, x, rfl, rfl⟩))

include E H in
private theorem child_faces_ne (s : D.Seam) (kept : s ∈ fineRetain) :
    (D.left s).face ≠ (D.right s).face := by
  intro same
  obtain ⟨x, regular⟩ := (D.triangle (D.left s).face).exists_edge_nonvertex (D.left s).edge
  have joined := E.childPlace_joined S H s kept x
  rw [congrArg (E.childPlace S) same] at joined
  have coordinates : x.val = (D.identify s x).val :=
    (E.childPlace S (D.right s).face).injective joined
  have right : D.OnEdge (D.right s) (D.edgePoint (D.left s) x) := by
    refine ⟨same, ?_⟩
    change x.val ∈ (D.triangle (D.right s).face).edge (D.right s).edge
    rw [coordinates]
    exact (D.identify s x).property
  have regular' : ¬ D.IsVertex (D.edgePoint (D.left s) x) := regular
  exact D.distinct s (D.onEdge_unique regular' (D.edgePoint_onEdge (D.left s) x) right)

theorem child_interior_inside (g : Child) :
    interior (E.childPlace S g '' (D.triangle g).carrier) ⊆
      interior (E.faceImage (S.parent g)) := by
  apply interior_mono
  rintro _ ⟨x, hx, rfl⟩
  exact ⟨S.place g x, S.inside g x hx, rfl⟩

include H in
theorem children_same_parent_disjoint {g h : Child} (different : g ≠ h)
    (same : S.parent g = S.parent h) :
    Disjoint (interior (E.childPlace S g '' (D.triangle g).carrier))
      (interior (E.childPlace S h '' (D.triangle h).carrier)) := by
  have disjoint := H.same_parent_disjoint different same
  have moved := Set.disjoint_image_of_injective (E.place (S.parent h)).injective disjoint
  rw [rigid_image_interior, rigid_image_interior] at moved
  apply Set.disjoint_left.mpr
  intro p hp hq
  apply Set.disjoint_left.mp moved
  · simpa only [childPlace, AffineIsometryEquiv.coe_trans, same, Set.image_image,
      Function.comp_def] using hp
  · simpa only [childPlace, AffineIsometryEquiv.coe_trans, Set.image_image,
      Function.comp_def] using hq

include H in
theorem child_hinge_disjoint (s : D.Seam) (kept : s ∈ fineRetain) :
    Disjoint (interior (E.childPlace S (D.left s).face '' (D.triangle (D.left s).face).carrier))
      (interior (E.childPlace S (D.right s).face '' (D.triangle (D.right s).face).carrier)) := by
  rcases H.parent_adjacent s kept with same | ⟨t, ht, parents⟩
  · exact E.children_same_parent_disjoint S H (E.child_faces_ne S H s kept) same
  · rcases parents with ⟨first, last⟩ | ⟨first, last⟩
    · apply (E.hinge_nonoverlap t ht).mono
      · simpa only [first] using E.child_interior_inside S (D.left s).face
      · simpa only [last] using E.child_interior_inside S (D.right s).face
    · apply (E.hinge_nonoverlap t ht).symm.mono
      · simpa only [first] using E.child_interior_inside S (D.left s).face
      · simpa only [last] using E.child_interior_inside S (D.right s).face

/-- A development restricts to every conforming subdivision; no nonoverlap assumption is needed. -/
def subdivide : FacewiseDevelopment D fineRetain where
  place := E.childPlace S
  joined := E.childPlace_joined S H
  opposite s kept := (D.triangle (D.left s).face).placed_opposite_of_disjoint
    (D.triangle (D.right s).face) (D.left s).edge (D.right s).edge (D.identify s)
    (E.childPlace S (D.left s).face) (E.childPlace S (D.right s).face)
    (E.childPlace_joined S H s kept) (E.child_hinge_disjoint S H s kept)

@[simp] theorem subdivide_toPlane (x : D.Realization fineRetain) :
    (E.subdivide S H).toPlane x = E.toPlane (H.metricEquiv x) := by
  obtain ⟨⟨g, y⟩, rfl⟩ := MetricGluing.point_surjective D.Cell (D.glue fineRetain) x
  rfl

theorem Nonoverlapping.subdivide (nonoverlap : E.Nonoverlapping) :
    (E.subdivide S H).Nonoverlapping := by
  intro g h different
  by_cases same : S.parent g = S.parent h
  · exact E.children_same_parent_disjoint S H different same
  · exact (nonoverlap _ _ same).mono (E.child_interior_inside S g) (E.child_interior_inside S h)

end Unfoldings.FacewiseDevelopment
