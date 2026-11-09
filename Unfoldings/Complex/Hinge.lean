module

public import Unfoldings.Complex.Neighborhood
public import Unfoldings.Geometry.HingePatch
public import Mathlib.Analysis.Normed.Affine.Convex

/-! Local hinge chords give intrinsic distance upper bounds in the full cut complex. -/

@[expose] public section

open scoped ENNReal

noncomputable section

namespace Unfoldings.TriangleComplex

universe u v

variable {Face : Type u} [Fintype Face] (C : TriangleComplex.{u, v} Face)

/-- The outward planar model of a single declared seam. -/
def seamHinge (s : C.Seam) : HingePlacement (C.triangle (C.left s).face)
    (C.triangle (C.right s).face) (C.left s).edge (C.right s).edge (C.identify s) :=
  hingePlacement _ _ _ _ (C.identify s)

/-- Chords in a covered hinge ball give paths no longer than the planar chord. -/
theorem edist_le_hinge_chord (retain : Set C.Seam) (s : C.Seam) (kept : s ∈ retain)
    {center : Plane} {r : ℝ}
    (cover : Metric.ball center r ⊆ (C.triangle (C.left s).face).carrier ∪
      (C.seamHinge s).place '' (C.triangle (C.right s).face).carrier)
    (x : C.Cell (C.left s).face) (y : C.Cell (C.right s).face)
    (near_left : x.val ∈ Metric.ball center r)
    (near_right : (C.seamHinge s).place y.val ∈ Metric.ball center r) :
    edist (C.faceMap retain (C.left s).face x) (C.faceMap retain (C.right s).face y) ≤
      edist x.val ((C.seamHinge s).place y.val) := by
  obtain ⟨z, between⟩ := (C.seamHinge s).exists_edge_on_chord cover x.property
    ⟨y.val, y.property, rfl⟩ near_left near_right
  let l := (C.triangle (C.left s).face).edgeMap (C.left s).edge z
  let q := (C.triangle (C.right s).face).edgeMap (C.right s).edge (C.identify s z)
  have seam : C.faceMap retain (C.left s).face l = C.faceMap retain (C.right s).face q :=
    C.seam_identified retain s kept z
  have left := (C.faceMap_lipschitz retain (C.left s).face).edist_le_mul x l
  have right := (C.faceMap_lipschitz retain (C.right s).face).edist_le_mul q y
  simp only [ENNReal.coe_one, one_mul] at left right
  have right_length : edist (C.identify s z).val y.val =
      edist z.val ((C.seamHinge s).place y.val) := by
    calc
      _ = edist ((C.seamHinge s).place (C.identify s z).val)
          ((C.seamHinge s).place y.val) := ((C.seamHinge s).place.isometry _ _).symm
      _ = _ := by rw [(C.seamHinge s).joined z]
  calc
    edist (C.faceMap retain (C.left s).face x) (C.faceMap retain (C.right s).face y) ≤
        edist (C.faceMap retain (C.left s).face x) (C.faceMap retain (C.left s).face l) +
          edist (C.faceMap retain (C.left s).face l) (C.faceMap retain (C.right s).face y) :=
      edist_triangle _ _ _
    _ = edist (C.faceMap retain (C.left s).face x) (C.faceMap retain (C.left s).face l) +
        edist (C.faceMap retain (C.right s).face q) (C.faceMap retain (C.right s).face y) := by
      rw [seam]
    _ ≤ edist x l + edist q y := add_le_add left right
    _ = edist x.val z.val + edist z.val ((C.seamHinge s).place y.val) := by
      change edist x.val z.val + edist (C.identify s z).val y.val = _
      rw [right_length]
    _ = edist x.val ((C.seamHinge s).place y.val) := by
      rw [edist_dist, edist_dist, edist_dist, ← ENNReal.ofReal_add dist_nonneg dist_nonneg,
        dist_add_dist_of_mem_segment between]

end Unfoldings.TriangleComplex
