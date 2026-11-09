module

public import Unfoldings.Polyhedron.Convex
public import Unfoldings.Complex.Vertices
public import Unfoldings.Geometry.RadialSlice

/-!
# Constructed transverse sections at spatial extreme vertices

Strict separation of the finite corner hull constructs a nonzero functional
and a positive level below every other corner. The resulting actual body
section is nonempty, compact and convex. Each other input corner projects to
that section along its original segment from the vertex.

The planar polygon description and its relation to the cyclic link are
subsequent theorems, not fields required of a vertex slice.
-/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialFolding

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  (F : SpatialFolding C)

theorem exists_vertexSlice (v : C.Vertex Set.univ)
    (extreme : F.toSpace Set.univ (C.vertexPoint Set.univ v) ∈ F.vertexHull.extremePoints ℝ) :
    ∃ (f : Space →L[ℝ] ℝ) (h : ℝ), f ≠ 0 ∧ 0 < h ∧
      (radialSlice F.vertexHull f (F.toSpace Set.univ (C.vertexPoint Set.univ v)) h).Nonempty ∧
      ∀ c : Face × Fin 3,
        F.place c.1 ((C.triangle c.1).vertex c.2) ≠
          F.toSpace Set.univ (C.vertexPoint Set.univ v) →
        h < f (F.place c.1 ((C.triangle c.1).vertex c.2) -
          F.toSpace Set.univ (C.vertexPoint Set.univ v)) ∧
        radialSlicePoint f (F.toSpace Set.univ (C.vertexPoint Set.univ v)) h
          (F.place c.1 ((C.triangle c.1).vertex c.2)) ∈
            radialSlice F.vertexHull f (F.toSpace Set.univ (C.vertexPoint Set.univ v)) h := by
  let corners (c : Face × Fin 3) := F.place c.1 ((C.triangle c.1).vertex c.2)
  let x := F.toSpace Set.univ (C.vertexPoint Set.univ v)
  obtain ⟨f, h, positive, projected⟩ := exists_radialSlice_of_finite_hull_extreme
    (Set.finite_range corners) extreme
  obtain ⟨⟨face, i⟩, representative⟩ := C.vertexOfCorner_surjective Set.univ v
  have apex : x = F.place face ((C.triangle face).vertex i) := by
    dsimp only [x]
    rw [← representative]
    rfl
  let c : Face × Fin 3 := (face, Triangle.next i)
  have different : corners c ≠ x := by
    rw [apex]
    intro equal
    exact (C.triangle face).edge_endpoints_ne i ((F.place face).injective equal).symm
  have generator := projected (corners c) ⟨c, rfl⟩ different
  have nonzero : f ≠ 0 := by
    intro zero
    have impossible := generator.1
    rw [zero] at impossible
    exact (not_lt_of_ge positive.le) impossible
  refine ⟨f, h, nonzero, positive, ⟨_, generator.2⟩, ?_⟩
  intro d hd
  exact projected (corners d) ⟨d, rfl⟩ hd

end Unfoldings.SpatialFolding
