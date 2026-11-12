module

public import Unfoldings.Cap.LocalClosedFaceSeparation
public import Unfoldings.Development.HingeInteriorContact

/-! Local roof separation excludes foreign contacts at every retained nonvertex hinge. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FacewiseDevelopment

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {retain : Set C.Seam} (D : FacewiseDevelopment C retain) (K : ConvexCap C)

theorem projected_retained_hinge_contact {U : Set Plane} (opened : IsOpen U)
    (separate : Pairwise (fun f g => Disjoint
      (D.projectedPlacement K f '' (interior (K.projectedTriangle f).carrier ∩ U))
      (D.projectedPlacement K g '' (interior (K.projectedTriangle g).carrier ∩ U))))
    (s : C.Seam) (kept : s ∈ retain)
    (x : (C.triangle (C.left s).face).Edge (C.left s).edge)
    (regular : ¬ (C.triangle (C.left s).face).IsVertex x.val)
    (inside : K.projectFace (C.left s).face x.val ∈ U)
    {g : Face} {q : Plane} (member : q ∈ (K.projectedTriangle g).carrier ∩ U)
    (same : D.projectedPlacement K g q = D.place (C.left s).face x.val) :
    (g = (C.left s).face ∨ g = (C.right s).face) ∧
      q = K.projectFace (C.left s).face x.val := by
  let p := K.projectFace (C.left s).face x.val
  let first := (D.projectedPlacement K (C.left s).face).toContinuousAffineEquiv.toHomeomorph
  let last := (D.projectedPlacement K (C.right s).face).toContinuousAffineEquiv.toHomeomorph
  have first_value : D.projectedPlacement K (C.left s).face p = D.place (C.left s).face x.val :=
    D.projectedPlacement_apply K _ x.val
  have last_value : D.projectedPlacement K (C.right s).face p = D.place (C.left s).face x.val := by
    change D.projectedPlacement K (C.right s).face
      (K.projectFace (C.left s).face x.val) = _
    rw [K.projectedTriangle_joined s x, D.projectedPlacement_apply]
    exact (D.joined s kept x).symm
  let V := interior (D.faceImage (C.left s).face ∪ D.faceImage (C.right s).face) ∩
    ((first '' U) ∩ (last '' U))
  have patch_open : IsOpen V := isOpen_interior.inter
    ((first.isOpenMap U opened).inter (last.isOpenMap U opened))
  have center : D.place (C.left s).face x.val ∈ V :=
    ⟨D.retained_hinge_point_mem_interior_union s kept x regular,
      ⟨⟨p, inside, first_value⟩, ⟨p, inside, last_value⟩⟩⟩
  let faces : Set Face := {(C.left s).face, (C.right s).face}
  have support {z : Plane} {f : Face} (named : f ∈ faces) (in_face : z ∈ D.faceImage f)
      (in_region : z ∈ D.projectedPlacement K f '' U) :
      z ∈ ⋃ a ∈ faces,
        D.projectedPlacement K a '' ((K.projectedTriangle a).carrier ∩ U) := by
    rw [← D.projectedPlacement_image_carrier K f] at in_face
    obtain ⟨a, first_member, at_a⟩ := in_face
    obtain ⟨b, last_member, at_b⟩ := in_region
    have coordinates : a = b := (D.projectedPlacement K f).injective (at_a.trans at_b.symm)
    exact Set.mem_iUnion.mpr ⟨f, Set.mem_iUnion.mpr
      ⟨named, a, ⟨first_member, coordinates.symm ▸ last_member⟩, at_a⟩⟩
  have cover : V ⊆ ⋃ f ∈ faces,
      D.projectedPlacement K f '' ((K.projectedTriangle f).carrier ∩ U) := by
    intro z member
    rcases interior_subset member.1 with in_first | in_last
    · exact support (Set.mem_insert _ _) in_first member.2.1
    · exact support (Set.mem_insert_of_mem _ (Set.mem_singleton _)) in_last member.2.2
  have incident : g = (C.left s).face ∨ g = (C.right s).face := by
    by_contra foreign
    have outside : g ∉ faces := by
      simpa only [faces, Set.mem_insert_iff, Set.mem_singleton_iff] using foreign
    have disjoint := D.projected_open_patch_disjoint_closed_piece K opened patch_open
      separate faces cover outside
    exact Set.disjoint_left.mp disjoint center ⟨q, member, same⟩
  refine ⟨incident, ?_⟩
  rcases incident with rfl | rfl
  · exact (D.projectedPlacement K (C.left s).face).injective (same.trans first_value.symm)
  · exact (D.projectedPlacement K (C.right s).face).injective (same.trans last_value.symm)

end Unfoldings.FacewiseDevelopment
