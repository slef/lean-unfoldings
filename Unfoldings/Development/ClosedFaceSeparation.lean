module

public import Unfoldings.Development
public import Unfoldings.Geometry.AffineEnd
public import Mathlib.Analysis.Convex.Topology

/-! Face-interior nonoverlap excludes all foreign closed-face contacts at interior points. -/

@[expose] public section

namespace Unfoldings.FacewiseDevelopment

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {retain : Set C.Seam} (D : FacewiseDevelopment C retain)

theorem closure_interior_faceImage (f : Face) :
    closure (interior (D.faceImage f)) = D.faceImage f := by
  have convex : Convex ℝ (D.faceImage f) :=
    (C.triangle f).convex_carrier.affine_image (D.place f).toAffineMap
  have full : (interior (D.faceImage f)).Nonempty := by
    rw [faceImage, ← rigid_image_interior]
    exact (C.triangle f).interior_nonempty.image (D.place f)
  exact (convex.closure_interior_eq_closure_of_nonempty_interior full).trans
    (((C.triangle f).compact_carrier.image (D.place f).continuous).isClosed.closure_eq)

theorem Nonoverlapping.interior_disjoint_closed_face (nonoverlap : D.Nonoverlapping)
    {f g : Face} (different : f ≠ g) :
    Disjoint (interior (D.faceImage f)) (D.faceImage g) := by
  rw [← D.closure_interior_faceImage g]
  exact (nonoverlap f g different).closure_right isOpen_interior

theorem Nonoverlapping.interior_union_disjoint_closed_face (nonoverlap : D.Nonoverlapping)
    {f h g : Face} (first : f ≠ g) (last : h ≠ g) :
    Disjoint (interior (D.faceImage f ∪ D.faceImage h)) (D.faceImage g) := by
  have disjoint : Disjoint (D.faceImage f ∪ D.faceImage h) (interior (D.faceImage g)) :=
    Set.disjoint_union_left.mpr
      ⟨(Nonoverlapping.interior_disjoint_closed_face D nonoverlap (Ne.symm first)).symm,
        (Nonoverlapping.interior_disjoint_closed_face D nonoverlap (Ne.symm last)).symm⟩
  rw [← D.closure_interior_faceImage g]
  exact (disjoint.mono_left interior_subset).closure_right isOpen_interior

theorem Nonoverlapping.eq_faceMap_of_toPlane_eq_interior (nonoverlap : D.Nonoverlapping)
    (f : Face) (x : C.Cell f) (inside : x.val ∈ interior (C.triangle f).carrier)
    (y : C.Realization retain) (same : D.toPlane y = D.place f x.val) :
    y = C.faceMap retain f x := by
  obtain ⟨⟨g, z⟩, rfl⟩ := MetricGluing.point_surjective C.Cell (C.glue retain) y
  change D.place g z.val = D.place f x.val at same
  by_cases faces : g = f
  · subst g
    exact congrArg (C.faceMap retain f) (Subtype.ext ((D.place f).injective same))
  · have in_first : D.place f x.val ∈ interior (D.faceImage f) := by
      rw [faceImage, ← rigid_image_interior]
      exact ⟨x.val, inside, rfl⟩
    have in_last : D.place f x.val ∈ D.faceImage g := ⟨z.val, z.property, same⟩
    exact (Set.disjoint_left.mp
      (Nonoverlapping.interior_disjoint_closed_face D nonoverlap (Ne.symm faces))
      in_first in_last).elim

end Unfoldings.FacewiseDevelopment
