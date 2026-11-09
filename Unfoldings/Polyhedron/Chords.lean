module

public import Unfoldings.Polyhedron.Convex
public import Unfoldings.Geometry.ConvexCover
public import Unfoldings.Path.Straight

/-!
# Exact intrinsic distances along spatial boundary chords

The inverse embedded surface map is nonexpanding on every original triangle.
A finite closed cover extends this bound to any convex subset of the actual
spatial boundary. Thus every straight boundary chord realizes intrinsic
distance, even if it crosses arbitrarily many subdivision edges.
-/

@[expose] public section

open scoped ENNReal NNReal

noncomputable section

namespace Unfoldings.SpatialFolding.ConvexBoundary

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {F : SpatialFolding C} (P : F.ConvexBoundary)

include P

/-- The actual embedded inverse, restricted to a specified spatial subset. -/
def liftSpatial (s : Set Space) (inside : s ⊆ F.surface) : s → C.Realization Set.univ :=
  fun x => (F.surfaceHomeomorph P.embedded).symm ⟨x.val, inside x.property⟩

@[simp] theorem toSpace_liftSpatial (s : Set Space) (inside : s ⊆ F.surface) (x : s) :
    F.toSpace Set.univ (P.liftSpatial s inside x) = x.val :=
  congrArg Subtype.val ((F.surfaceHomeomorph P.embedded).apply_symm_apply
    ⟨x.val, inside x.property⟩)

theorem liftSpatial_lipschitz (s : Set Space) (convex : Convex ℝ s) (inside : s ⊆ F.surface) :
    LipschitzWith 1 (P.liftSpatial s inside) := by
  let := P.metricSpace
  let pieces (f : Face) : Set s := Subtype.val ⁻¹' F.faceImage f
  have closed (f : Face) : IsClosed (pieces f) :=
    (F.compact_faceImage f).isClosed.preimage continuous_subtype_val
  have cover : ⋃ f, pieces f = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    obtain ⟨f, hf⟩ := Set.mem_iUnion.mp (inside x.property)
    exact Set.mem_iUnion.mpr ⟨f, hf⟩
  have bounded (f : Face) : LipschitzOnWith 1 (P.liftSpatial s inside) (pieces f) := by
    intro z hz w hw
    obtain ⟨left_point, hl, left_equal⟩ := hz
    obtain ⟨right_point, hr, right_equal⟩ := hw
    let x : C.Cell f := ⟨left_point, hl⟩
    let y : C.Cell f := ⟨right_point, hr⟩
    have left_coordinates : F.place f x.val = z.val := left_equal
    have right_coordinates : F.place f y.val = w.val := right_equal
    have left_preimage : P.liftSpatial s inside z = C.faceMap Set.univ f x := by
      apply P.embedded
      rw [P.toSpace_liftSpatial, F.toSpace_faceMap]
      exact left_coordinates.symm
    have right_preimage : P.liftSpatial s inside w = C.faceMap Set.univ f y := by
      apply P.embedded
      rw [P.toSpace_liftSpatial, F.toSpace_faceMap]
      exact right_coordinates.symm
    change edist (P.liftSpatial s inside z) (P.liftSpatial s inside w) ≤
      (1 : ℝ≥0∞) * edist z.val w.val
    rw [one_mul, left_preimage, right_preimage, ← left_coordinates, ← right_coordinates]
    exact ((F.faceMap_isometry Set.univ f x y).trans (F.face_isometry f x y).symm).le
  exact convex_subtype_lipschitzWith_of_finite_closed_cover s convex pieces closed cover
    (P.liftSpatial s inside) 1 bounded

theorem liftSpatial_isometry (s : Set Space) (convex : Convex ℝ s) (inside : s ⊆ F.surface) :
    Isometry (P.liftSpatial s inside) := by
  intro x y
  apply le_antisymm
  · simpa only [ENNReal.coe_one, one_mul] using
      (P.liftSpatial_lipschitz s convex inside).edist_le_mul x y
  · have bound := (F.toSpace_lipschitz Set.univ).edist_le_mul
      (P.liftSpatial s inside x) (P.liftSpatial s inside y)
    change edist x.val y.val ≤ _
    simpa only [P.toSpace_liftSpatial, ENNReal.coe_one, one_mul] using bound

/-- A straight chord lying in the actual boundary has exactly its Euclidean
length in the constructed intrinsic surface metric. -/
theorem edist_eq_spatial_chord (x y : C.Realization Set.univ)
    (boundary_chord : segment ℝ (F.toSpace Set.univ x) (F.toSpace Set.univ y) ⊆ F.surface) :
    edist x y = edist (F.toSpace Set.univ x) (F.toSpace Set.univ y) := by
  let s := segment ℝ (F.toSpace Set.univ x) (F.toSpace Set.univ y)
  let a : s := ⟨F.toSpace Set.univ x, left_mem_segment ℝ _ _⟩
  let b : s := ⟨F.toSpace Set.univ y, right_mem_segment ℝ _ _⟩
  have first : P.liftSpatial s boundary_chord a = x := by
    apply P.embedded
    exact P.toSpace_liftSpatial s boundary_chord a
  have last : P.liftSpatial s boundary_chord b = y := by
    apply P.embedded
    exact P.toSpace_liftSpatial s boundary_chord b
  have equal := (P.liftSpatial_isometry s (convex_segment _ _) boundary_chord).edist_eq a b
  rw [first, last] at equal
  exact equal

theorem geodesic_spatial_eq_lineMap {x y : C.Realization Set.univ} {p : Path x y}
    (boundary_chord : segment ℝ (F.toSpace Set.univ x) (F.toSpace Set.univ y) ⊆ F.surface)
    (geodesic : p.IsGeodesic) (t : unitInterval) :
    F.toSpace Set.univ (p t) =
      AffineMap.lineMap (F.toSpace Set.univ x) (F.toSpace Set.univ y) (t : ℝ) :=
  geodesic.map_eq_lineMap (F.toSpace Set.univ) (F.toSpace_lipschitz Set.univ)
    (P.edist_eq_spatial_chord x y boundary_chord).symm t

/-- Endpoints of a spatial boundary chord have a unique intrinsic geodesic,
including among routes that could leave the planar boundary region. -/
theorem geodesic_unique_of_spatial_chord {x y : C.Realization Set.univ}
    {p q : Path x y}
    (boundary_chord : segment ℝ (F.toSpace Set.univ x) (F.toSpace Set.univ y) ⊆ F.surface)
    (geodesic : p.IsGeodesic) (other : q.IsGeodesic) : p = q := by
  ext t
  apply P.embedded
  exact (P.geodesic_spatial_eq_lineMap boundary_chord geodesic t).trans
    (P.geodesic_spatial_eq_lineMap boundary_chord other t).symm

end Unfoldings.SpatialFolding.ConvexBoundary
