module

public import Unfoldings.Roof.ProjectedSeamCompletion
public import Unfoldings.Roof.OriginalCuts

/-! Intrinsic projected face copies with arbitrary original cuts. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexRoof C)

def pointCopy (retain : Set C.Seam) (f : Face) (p : Plane)
    (member : p ∈ (K.projectedTriangle f).carrier) : C.Realization retain :=
  C.faceMap retain f ⟨(K.projectFaceEquiv f).symm p, by
    rw [projectedTriangle, Triangle.affineImage_carrier] at member
    obtain ⟨x, inside, equal⟩ := member
    have coordinates : (K.projectFaceEquiv f).symm p = x := by
      rw [← equal]
      exact (K.projectFaceEquiv f).symm_apply_apply x
    exact coordinates.symm ▸ inside⟩

theorem pointCopy_of_localPoint (retain : Set C.Seam) (f : Face) (x : C.Cell f) :
    K.pointCopy retain f (K.projectFace f x.val)
        (by rw [projectedTriangle, Triangle.affineImage_carrier]
            exact ⟨x.val, x.property, rfl⟩) = C.faceMap retain f x := by
  apply congrArg (C.faceMap retain f)
  exact Subtype.ext ((K.projectFaceEquiv f).symm_apply_apply x.val)

theorem pointCopy_eq_across_seam (retain : Set C.Seam) (s : C.Seam) (kept : s ∈ retain)
    {p : Plane} (member : p ∈ (K.projectedTriangle (C.left s).face).edge (C.left s).edge) :
    K.pointCopy retain (C.left s).face p ((K.projectedTriangle _).edge_subset _ member) =
      K.pointCopy retain (C.right s).face p ((K.projectedTriangle _).edge_subset _
        ((K.projected_seam_edges_eq s).subset member)) := by
  rw [projectedTriangle, Triangle.affineImage_edge] at member
  obtain ⟨x, inside, equal⟩ := member
  let z : (C.triangle (C.left s).face).Edge (C.left s).edge := ⟨x, inside⟩
  have first_value : (K.projectFaceEquiv (C.left s).face).symm p = x := by
    rw [← equal]
    exact (K.projectFaceEquiv (C.left s).face).symm_apply_apply x
  have last_value : (K.projectFaceEquiv (C.right s).face).symm p = (C.identify s z).val := by
    apply (K.projectFaceEquiv (C.right s).face).injective
    exact ((K.projectFaceEquiv (C.right s).face).apply_symm_apply p).trans
      (equal.symm.trans (K.projectedTriangle_joined s z))
  have joined := C.seam_identified retain s kept z
  change C.faceMap retain (C.left s).face ⟨x, _⟩ =
    C.faceMap retain (C.right s).face ⟨(C.identify s z).val, _⟩ at joined
  simpa only [pointCopy, first_value, last_value] using joined

theorem pointCopy_eq_of_shared_edge (retain : Set C.Seam) {a b : EdgeRef Face}
    (different : a.face ≠ b.face)
    (same : (K.projectedTriangle a.face).edge a.edge =
      (K.projectedTriangle b.face).edge b.edge)
    (uncut : ¬ (K.projectedTriangle a.face).edge a.edge ⊆ K.projectedCutSet retain)
    {p : Plane} (member : p ∈ (K.projectedTriangle a.face).edge a.edge) :
    K.pointCopy retain a.face p ((K.projectedTriangle a.face).edge_subset a.edge member) =
      K.pointCopy retain b.face p ((K.projectedTriangle b.face).edge_subset b.edge
        (same ▸ member)) := by
  obtain ⟨s, ⟨first, last⟩ | ⟨first, last⟩⟩ :=
    K.exists_seam_of_projected_shared_edge different same
  · have kept : s ∈ retain := by
      by_contra cut
      apply uncut
      intro q on_edge
      exact Set.mem_iUnion.mpr ⟨s, Set.mem_iUnion.mpr ⟨cut, by
        simpa only [first] using on_edge⟩⟩
    have at_left : p ∈ (K.projectedTriangle (C.left s).face).edge (C.left s).edge := by
      simpa only [first] using member
    simpa only [first, last] using K.pointCopy_eq_across_seam retain s kept at_left
  · have kept : s ∈ retain := by
      by_contra cut
      apply uncut
      intro q on_edge
      exact Set.mem_iUnion.mpr ⟨s, Set.mem_iUnion.mpr ⟨cut, by
        simpa only [first] using (same ▸ on_edge)⟩⟩
    have at_left : p ∈ (K.projectedTriangle (C.left s).face).edge (C.left s).edge := by
      simpa only [first] using (same ▸ member)
    simpa only [first, last] using (K.pointCopy_eq_across_seam retain s kept at_left).symm

end Unfoldings.ConvexRoof
