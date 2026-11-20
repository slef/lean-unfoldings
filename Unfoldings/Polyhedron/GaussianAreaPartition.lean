module

public import Unfoldings.Convex.FiniteNormalFan
public import Unfoldings.Polyhedron.Convex

/-! The solid angle is partitioned by all distinct original spatial corner sites. -/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialFolding

open scoped BigOperators

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  (F : SpatialFolding C)

open Classical in
/-- Distinct physical sites in the input triangulation, independent of
how many triangles contain each corner. -/
def hullSites : Finset Space :=
  Finset.univ.image (fun p : Face × Fin 3 => F.place p.1 ((C.triangle p.1).vertex p.2))

theorem vertexHull_eq_convexHull_sites :
    F.vertexHull = convexHull ℝ (F.hullSites : Set Space) := by
  unfold vertexHull hullSites
  rw [Finset.coe_image, Finset.coe_univ, Set.image_univ]

/-- The normal cone based at a spatial site of the actual polyhedron. -/
def gaussianCone (i : F.hullSites) : Set Space :=
  finiteHullNormalCone (fun j : F.hullSites => (j : Space)) i

theorem mem_gaussianCone_iff {i : F.hullSites} {n : Space} :
    n ∈ F.gaussianCone i ↔ ∀ x ∈ F.vertexHull, inner ℝ n x ≤ inner ℝ n (i : Space) := by
  rw [F.vertexHull_eq_convexHull_sites, gaussianCone, mem_finiteHullNormalCone_iff]
  have range : Set.range (fun j : F.hullSites => (j : Space)) = (F.hullSites : Set Space) :=
    Subtype.range_coe_subtype
  rw [range]

/-- The areas of the actual Gaussian cones exhaust the area of the unit sphere.
A lower-dimensional cone can be present and contributes zero area. -/
theorem sum_gaussianArea (P : F.ConvexBoundary) :
    (∑ i : F.hullSites, (solidAngleMeasure (F.gaussianCone i)).toReal) = 4 * Real.pi := by
  have hull_nonempty := P.interior_nonempty.mono interior_subset
  rw [F.vertexHull_eq_convexHull_sites, convexHull_nonempty_iff] at hull_nonempty
  obtain ⟨p, hp⟩ := hull_nonempty
  let : Nonempty F.hullSites := ⟨⟨p, hp⟩⟩
  exact sum_solidAngle_finiteHullNormalCone _ Subtype.val_injective

end Unfoldings.SpatialFolding
