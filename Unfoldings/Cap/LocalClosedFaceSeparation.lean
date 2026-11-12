module

public import Unfoldings.Cap.ProjectedDenseSeparation

/-! Local roof separation excludes foreign closed-face contacts at developed face interiors. -/

@[expose] public section

namespace Unfoldings.FacewiseDevelopment

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {retain : Set C.Seam} (D : FacewiseDevelopment C retain) (K : ConvexCap C)

theorem projectedPlacement_image_carrier (f : Face) :
    D.projectedPlacement K f '' (K.projectedTriangle f).carrier = D.faceImage f := by
  simp only [ConvexCap.projectedTriangle, Triangle.affineImage_carrier,
    Set.image_image, D.projectedPlacement_apply, faceImage]

theorem projected_closed_piece_subset_closure {U : Set Plane} (opened : IsOpen U) (g : Face) :
    D.projectedPlacement K g '' ((K.projectedTriangle g).carrier ∩ U) ⊆
      closure (D.projectedPlacement K g '' (interior (K.projectedTriangle g).carrier ∩ U)) := by
  let chart := (D.projectedPlacement K g).toContinuousAffineEquiv.toHomeomorph
  rintro _ ⟨q, member, rfl⟩
  have regular_closed : closure (interior (K.projectedTriangle g).carrier) =
      (K.projectedTriangle g).carrier :=
    ((K.projectedTriangle g).convex_carrier.closure_interior_eq_closure_of_nonempty_interior
      (K.projectedTriangle g).interior_nonempty).trans
      (K.projectedTriangle g).compact_carrier.isClosed.closure_eq
  have near : q ∈ closure (interior (K.projectedTriangle g).carrier ∩ U) :=
    opened.closure_inter ⟨regular_closed.symm ▸ member.1, member.2⟩
  exact (chart.image_closure _).subset ⟨q, near, rfl⟩

theorem projected_interior_disjoint_closed_piece {U : Set Plane} (opened : IsOpen U)
    {f g : Face}
    (separate : Disjoint
      (D.projectedPlacement K f '' (interior (K.projectedTriangle f).carrier ∩ U))
      (D.projectedPlacement K g '' (interior (K.projectedTriangle g).carrier ∩ U))) :
    Disjoint (D.projectedPlacement K f '' (interior (K.projectedTriangle f).carrier ∩ U))
      (D.projectedPlacement K g '' ((K.projectedTriangle g).carrier ∩ U)) := by
  let first := (D.projectedPlacement K f).toContinuousAffineEquiv.toHomeomorph
  have first_open : IsOpen
      (D.projectedPlacement K f '' (interior (K.projectedTriangle f).carrier ∩ U)) :=
    first.isOpenMap _ (isOpen_interior.inter opened)
  apply (separate.closure_right first_open).mono Set.Subset.rfl
  exact D.projected_closed_piece_subset_closure K opened g

theorem projected_open_patch_disjoint_closed_piece {U V : Set Plane}
    (opened : IsOpen U) (patch_open : IsOpen V)
    (separate : Pairwise (fun f g => Disjoint
      (D.projectedPlacement K f '' (interior (K.projectedTriangle f).carrier ∩ U))
      (D.projectedPlacement K g '' (interior (K.projectedTriangle g).carrier ∩ U))))
    (faces : Set Face)
    (cover : V ⊆ ⋃ f ∈ faces,
      D.projectedPlacement K f '' ((K.projectedTriangle f).carrier ∩ U))
    {g : Face} (outside : g ∉ faces) :
    Disjoint V (D.projectedPlacement K g '' ((K.projectedTriangle g).carrier ∩ U)) := by
  have disjoint : Disjoint V
      (D.projectedPlacement K g '' (interior (K.projectedTriangle g).carrier ∩ U)) := by
    apply Set.disjoint_left.mpr
    intro p in_patch in_g
    obtain ⟨f, in_f⟩ := Set.mem_iUnion.mp (cover in_patch)
    obtain ⟨member, in_f⟩ := Set.mem_iUnion.mp in_f
    have different : g ≠ f := fun same => outside (same.symm ▸ member)
    exact Set.disjoint_left.mp
      (D.projected_interior_disjoint_closed_piece K opened (separate different)) in_g in_f
  exact (disjoint.closure_right patch_open).mono Set.Subset.rfl
    (D.projected_closed_piece_subset_closure K opened g)

theorem projected_points_eq_of_interior_contact {U : Set Plane} (opened : IsOpen U)
    (separate : Pairwise (fun f g => Disjoint
      (D.projectedPlacement K f '' (interior (K.projectedTriangle f).carrier ∩ U))
      (D.projectedPlacement K g '' (interior (K.projectedTriangle g).carrier ∩ U))))
    {f g : Face} {p q : Plane}
    (first : p ∈ interior (K.projectedTriangle f).carrier ∩ U)
    (last : q ∈ (K.projectedTriangle g).carrier ∩ U)
    (same : D.projectedPlacement K f p = D.projectedPlacement K g q) : f = g ∧ p = q := by
  have faces : f = g := by
    by_contra different
    have disjoint := D.projected_interior_disjoint_closed_piece K opened (separate different)
    exact Set.disjoint_left.mp disjoint ⟨p, first, rfl⟩ ⟨q, last, same.symm⟩
  refine ⟨faces, ?_⟩
  rw [faces] at same
  exact (D.projectedPlacement K g).injective same

end Unfoldings.FacewiseDevelopment
