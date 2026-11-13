module

public import Unfoldings.Roof.InjectiveEdgeUnfolding
public import Unfoldings.Development.SimpleBoundary

/-!
# The arbitrary-rim acute-roof theorem

A positive acute margin determines a positive tilt bound before the triangulated convex roof
is supplied. Cutting a boundary-rooted forest of original seams produces an intrinsic
closed disk with a globally injective development, locally isometric on its interior.
Its footprint has a simple polygonal frontier consisting of the actual developed banks.

This is an existence theorem; no numerical optimality or algorithmic running-time claim
is made by the noncomputable construction.
-/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexRoof C)

/-- An original-edge cut disk embedded in the plane by an actual facewise development.
Every field describes the constructed intrinsic surface and its actual development. -/
structure SimpleEdgeUnfolding (K : ConvexRoof C) where
  retain : Set C.Seam
  cutForest : (C.relativeCutGraph retain Set.univ).IsRootedForest (C.relativeCutRoots Set.univ)
  disk : C.Realization retain ≃ₜ Metric.closedBall (0 : Plane) 1
  development : FacewiseDevelopment C retain
  nonoverlapping : development.Nonoverlapping
  local_isometry : ∀ x, ‖(disk x).val‖ < 1 → ∃ r > 0,
    Isometry (fun y : Metric.eball x (ENNReal.ofReal r) => development.toPlane y.val)
  injective : Function.Injective development.toPlane

namespace SimpleEdgeUnfolding

variable {K} (U : K.SimpleEdgeUnfolding)

/-- The whole developed closed disk, including its boundary. -/
def footprint : Set Plane := Set.range U.development.toPlane

/-- The intrinsic cut surface is homeomorphic to its entire actual footprint. -/
def footprintHomeomorph : C.Realization U.retain ≃ₜ U.footprint :=
  (U.development.toPlane_lipschitz.continuous.isClosedEmbedding
    U.injective).isEmbedding.toHomeomorph

/-- The actual developed bank boundary is exactly the footprint frontier. -/
theorem frontier_eq_boundary :
    frontier U.footprint = U.development.toPlane '' C.bankBoundary U.retain :=
  U.development.frontier_range_eq_image_boundary K.folding U.disk U.injective

/-- The footprint boundary has no self-intersections or self-contacts. -/
theorem frontier_isJordanCurve : Schoenflies.IsJordanCurve (frontier U.footprint) :=
  (U.development.frontier_is_simple_polygon K.folding U.disk U.injective).1

/-- The simple boundary consists of the finitely many actual straight bank segments. -/
theorem frontier_eq_segments :
    frontier U.footprint =
      ⋃ bank : C.BoundaryBank U.retain,
        segment ℝ
          (U.development.toPlane
            (C.vertexPoint U.retain ((C.boundaryGraph U.retain).left bank).val))
          (U.development.toPlane
            (C.vertexPoint U.retain ((C.boundaryGraph U.retain).right bank).val)) :=
  (U.development.frontier_is_simple_polygon K.folding U.disk U.injective).2

/-- There are only finitely many bank segments in this polygonal boundary. -/
theorem finite_banks : Finite (C.BoundaryBank U.retain) := C.finite_boundaryBank U.retain

end SimpleEdgeUnfolding

/-- Arbitrary-rim acute-roof theorem: sufficiently shallow convex roofs with a fixed positive acute
margin have simple polygon edge unfoldings. The same positive tilt threshold works
for every mesh, including arbitrary numbers of flat subdivision vertices. -/
theorem arbitrary_rim_acute_roof_theorem {α : ℝ} (positive : 0 < α) :
    ∃ φ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      ∀ {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexRoof C),
        AcuteMargin (C := C) α → K.TiltBound φ → Nonempty K.SimpleEdgeUnfolding := by
  obtain ⟨φ, bounds, unfolds⟩ := exists_uniform_injective_edge_unfolding.{u, v} positive
  refine ⟨φ, bounds, ?_⟩
  intro Face _ C K acute tilt
  obtain ⟨retain, forest, disk, D, nonoverlap, local_isometry, injective⟩ := unfolds K acute tilt
  exact ⟨⟨retain, forest, disk, D, nonoverlap, local_isometry, injective⟩⟩

end Unfoldings.ConvexRoof
