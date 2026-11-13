module

public import Unfoldings.Complex.GeometricPairings
public import Unfoldings.Complex.Exact
public import Unfoldings.Geometry.ConformingStar
public import Unfoldings.Geometry.TriangleAffineEquiv
public import Unfoldings.Geometry.TriangleAffine

/-! Whole-edge compatibility gives exact intrinsic fibers for a conforming convex projection. -/

@[expose] public section

noncomputable section

namespace Unfoldings.TriangleComplex

universe u v

variable {Face : Type u} [Fintype Face] (C : TriangleComplex.{u, v} Face)
  (A : Face → Plane ≃ᵃ[ℝ] Plane)

/-- The actual projected triangles, with the original corners and edge names. -/
def affineProjectedTriangle (f : Face) : Triangle :=
  (C.triangle f).affineImage (A f).toAffineMap (A f).injective

/-- A projected geometric point has a canonical physical copy in each containing triangle. -/
def projectedPointCopy (f : Face) (p : Plane)
    (member : p ∈ (C.affineProjectedTriangle A f).carrier) : C.Realization Set.univ :=
  C.faceMap Set.univ f ⟨(A f).symm p, by
    obtain ⟨x, hx, equal⟩ := ((C.triangle f).affineImage_carrier
      (A f).toAffineMap (A f).injective).subset member
    have coordinates : (A f).symm p = x := by
      rw [← equal]
      exact (A f).symm_apply_apply x
    exact coordinates.symm ▸ hx⟩

/-- The original seam's projected banks agree at the same physical point. -/
theorem projectedPointCopy_across_seam
    (joined : ∀ s x, A (C.left s).face x.val = A (C.right s).face (C.identify s x).val)
    (s : C.Seam) {p : Plane}
    (member : p ∈ (C.affineProjectedTriangle A (C.left s).face).edge (C.left s).edge) :
    C.projectedPointCopy A (C.left s).face p
      ((C.affineProjectedTriangle A _).edge_subset _ member) =
    C.projectedPointCopy A (C.right s).face p (by
      apply ((C.triangle (C.right s).face).affineImage_carrier
        (A (C.right s).face).toAffineMap (A (C.right s).face).injective).symm.subset
      obtain ⟨x, hx, equal⟩ := ((C.triangle _).affineImage_edge
        (A _).toAffineMap (A _).injective (C.left s).edge).subset member
      exact ⟨(C.identify s ⟨x, hx⟩).val,
        (C.triangle _).edge_subset _ (C.identify s ⟨x, hx⟩).property,
          (joined s ⟨x, hx⟩).symm.trans equal⟩) := by
  obtain ⟨x, hx, equal⟩ := ((C.triangle _).affineImage_edge
    (A _).toAffineMap (A _).injective (C.left s).edge).subset member
  have first : (A (C.left s).face).symm p = x := by rw [← equal]; exact (A _).symm_apply_apply x
  have last : (A (C.right s).face).symm p = (C.identify s ⟨x, hx⟩).val := by
    apply (A (C.right s).face).injective
    rw [(A (C.right s).face).apply_symm_apply]
    exact ((joined s ⟨x, hx⟩).symm.trans equal).symm
  have equal_points := C.seam_identified Set.univ s (Set.mem_univ _) ⟨x, hx⟩
  change C.faceMap Set.univ (C.left s).face ⟨x, _⟩ =
    C.faceMap Set.univ (C.right s).face ⟨(C.identify s ⟨x, hx⟩).val, _⟩ at equal_points
  simpa only [projectedPointCopy, first, last] using equal_points

/-- Every projected point has one intrinsic copy when all matching projected whole edges
are paired. This includes every vertex star, where several triangles can meet. -/
theorem projectedPointCopy_eq
    (joined : ∀ s x, A (C.left s).face x.val = A (C.right s).face (C.identify s x).val)
    (convex : Convex ℝ (⋃ f, (C.affineProjectedTriangle A f).carrier))
    (conforming : TriangleFamily.Conforming (C.affineProjectedTriangle A))
    (separated : Pairwise (fun f g => Disjoint
      (interior (C.affineProjectedTriangle A f).carrier)
      (interior (C.affineProjectedTriangle A g).carrier)))
    (complete : ∀ f g : Face, f ≠ g → ∀ e d : Fin 3,
      (C.affineProjectedTriangle A f).edge e = (C.affineProjectedTriangle A g).edge d →
        ∃ s, (C.left s = ⟨f, e⟩ ∧ C.right s = ⟨g, d⟩) ∨
          (C.left s = ⟨g, d⟩ ∧ C.right s = ⟨f, e⟩))
    (p : Plane) {f g : Face} (first : p ∈ (C.affineProjectedTriangle A f).carrier)
    (last : p ∈ (C.affineProjectedTriangle A g).carrier) :
    C.projectedPointCopy A f p first = C.projectedPointCopy A g p last := by
  let value (a : {f // p ∈ (C.affineProjectedTriangle A f).carrier}) :=
    C.projectedPointCopy A a.val p a.property
  apply TriangleFamily.incident_values_eq (C.affineProjectedTriangle A) convex rfl
    conforming separated p value _ ⟨f, first⟩ ⟨g, last⟩
  intro a b e d same member
  by_cases different : a.val = b.val
  · exact congrArg value (Subtype.ext different)
  obtain ⟨s, ⟨left, right⟩ | ⟨right, left⟩⟩ := complete a.val b.val different e d same
  · have at_left : p ∈ (C.affineProjectedTriangle A (C.left s).face).edge (C.left s).edge := by
      simpa only [left] using member
    simpa only [left, right, value] using C.projectedPointCopy_across_seam A joined s at_left
  · have at_left : p ∈ (C.affineProjectedTriangle A (C.left s).face).edge (C.left s).edge := by
      have at_b : p ∈ (C.affineProjectedTriangle A b.val).edge d := same ▸ member
      simpa only [right] using at_b
    simpa only [left, right, value] using (C.projectedPointCopy_across_seam A joined s at_left).symm

/-- Equality in a conforming projection is precisely actual finite seam identification. -/
theorem related_of_affine_projection_eq
    (joined : ∀ s x, A (C.left s).face x.val = A (C.right s).face (C.identify s x).val)
    (convex : Convex ℝ (⋃ f, (C.affineProjectedTriangle A f).carrier))
    (conforming : TriangleFamily.Conforming (C.affineProjectedTriangle A))
    (separated : Pairwise (fun f g => Disjoint
      (interior (C.affineProjectedTriangle A f).carrier)
      (interior (C.affineProjectedTriangle A g).carrier)))
    (complete : ∀ f g : Face, f ≠ g → ∀ e d : Fin 3,
      (C.affineProjectedTriangle A f).edge e = (C.affineProjectedTriangle A g).edge d →
        ∃ s, (C.left s = ⟨f, e⟩ ∧ C.right s = ⟨g, d⟩) ∨
          (C.left s = ⟨g, d⟩ ∧ C.right s = ⟨f, e⟩))
    (a b : C.Total) (same : A a.1 a.2.val = A b.1 b.2.val) :
    Relation.EqvGen (C.glue Set.univ) a b := by
  have member (a : C.Total) : A a.1 a.2.val ∈ (C.affineProjectedTriangle A a.1).carrier :=
    ((C.triangle a.1).affineImage_carrier (A a.1).toAffineMap
      (A a.1).injective).symm.subset ⟨a.2.val, a.2.property, rfl⟩
  have point (a : C.Total) : C.projectedPointCopy A a.1 (A a.1 a.2.val) (member a) =
      MetricGluing.point C.Cell (C.glue Set.univ) a := by
    change C.faceMap Set.univ a.1 ⟨(A a.1).symm (A a.1 a.2.val), _⟩ = C.faceMap Set.univ a.1 a.2
    apply congrArg (C.faceMap Set.univ a.1)
    exact Subtype.ext ((A a.1).symm_apply_apply _)
  have both := C.projectedPointCopy_eq A joined convex conforming separated complete
    (A a.1 a.2.val) (member a) (same.symm ▸ member b)
  apply (C.point_eq_iff Set.univ a b).mp
  rw [← point a, ← point b]
  simpa only [same] using both

end Unfoldings.TriangleComplex
