module

public import Unfoldings.Development
public import Unfoldings.Geometry.Halfplane
public import Mathlib.Tactic.Linarith

/-! The opposite-side condition rules out local overlap at a retained hinge. -/

@[expose] public section

namespace Unfoldings

namespace FacewiseDevelopment

variable {Face : Type*} [Fintype Face] {C : TriangleComplex Face} {retain : Set C.Seam}
  (D : FacewiseDevelopment C retain)

/-- The local opening condition implies genuine disjoint face interiors at every retained hinge.
This does not assert nonoverlap of nonadjacent faces. -/
theorem hinge_nonoverlap (s : C.Seam) (hs : s ∈ retain) :
    Disjoint (interior (D.faceImage (C.left s).face))
      (interior (D.faceImage (C.right s).face)) := by
  let L := C.triangle (C.left s).face
  let R := C.triangle (C.right s).face
  let left := (D.place (C.left s).face).toAffineEquiv.toAffineMap
  let right := (D.place (C.right s).face).toAffineEquiv.toAffineMap
  let a := left (L.vertex (C.left s).edge)
  let b := left (L.vertex (Triangle.next (C.left s).edge))
  let c := left (L.opposite (C.left s).edge)
  let d := right (R.opposite (C.right s).edge)
  let height := lineHeight a b
  let level := height a
  have opening : orient a b c * orient a b d < 0 := D.opposite s hs
  have nonzero : orient a b c ≠ 0 := by
    intro zero
    rw [zero, zero_mul] at opening
    exact (lt_irrefl 0 opening)
  have surjective : Function.Surjective height := lineHeight_surjective nonzero
  have at_b : height b = level := by
    dsimp [height, level]
    simp [lineHeight]
    ring
  have along_left (x : L.Edge (C.left s).edge) : height (left x) = level := by
    have convex : Convex ℝ {z : Plane | height (left z) = level} :=
      ((convex_singleton level).linear_preimage height.toLinearMap).affine_preimage left
    exact convex.segment_subset (show height a = level from rfl) at_b x.property
  have along_right (x : R.Edge (C.right s).edge) : height (right x) = level := by
    have joined := D.joined s hs ((C.identify s).symm x)
    simp only [IsometryEquiv.apply_symm_apply] at joined
    change left ((C.identify s).symm x) = right x at joined
    rw [← joined]
    exact along_left _
  have hc : orient a b c = height c - level := orient_eq_height a b c
  have hd : orient a b d = height d - level := orient_eq_height a b d
  rcases lt_or_gt_of_ne nonzero with negative | positive
  · have other : 0 < orient a b d := by nlinarith
    exact L.disjoint_interiors_of_vertex_separator R left right height surjective level
      (L.vertices_le_of_edge left (C.left s).edge height level along_left (by
        dsimp [c] at hc; linarith))
      (R.vertices_ge_of_edge right (C.right s).edge height level along_right (by
        dsimp [d] at hd; linarith))
  · have other : orient a b d < 0 := by nlinarith
    exact (R.disjoint_interiors_of_vertex_separator L right left height surjective level
      (R.vertices_le_of_edge right (C.right s).edge height level along_right (by
        dsimp [d] at hd; linarith))
      (L.vertices_ge_of_edge left (C.left s).edge height level along_left (by
        dsimp [c] at hc; linarith))).symm

end FacewiseDevelopment
end Unfoldings
