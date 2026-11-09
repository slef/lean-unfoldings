module

public import Unfoldings.Polyhedron.VertexSliceInterior
public import Unfoldings.Geometry.FunctionalPlane
public import Mathlib.Analysis.Normed.Affine.AddTorsorBases

/-!
# Constructed planar vertex figures

A strict support functional, a small positive level, and an actual interior
center construct a Euclidean planar section of the body. The carrier is
compact, convex, contains zero in its interior, and is exactly the convex
hull of finitely many explicit radial corner generators.

The cyclic boundary order and its connection to the actual surface link
are proved separately; neither is included as assumed structure data.
-/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialFolding

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  (F : SpatialFolding C)

structure VertexFigure (v : C.Vertex Set.univ) where
  functional : Space →L[ℝ] ℝ
  nonzero : functional ≠ 0
  level : ℝ
  positive : 0 < level
  center : Space
  center_inside : center ∈ interior F.vertexHull
  center_level : functional (center - F.toSpace Set.univ (C.vertexPoint Set.univ v)) = level
  supported : ∀ c : Face × Fin 3,
    F.place c.1 ((C.triangle c.1).vertex c.2) ≠
      F.toSpace Set.univ (C.vertexPoint Set.univ v) →
    level < functional (F.place c.1 ((C.triangle c.1).vertex c.2) -
      F.toSpace Set.univ (C.vertexPoint Set.univ v))

namespace VertexFigure

variable {F} {v : C.Vertex Set.univ} (V : F.VertexFigure v)

def place : Plane →ᵃⁱ[ℝ] Space :=
  functionalPlanePlacement V.functional V.nonzero V.center

@[simp] theorem place_zero : V.place 0 = V.center :=
  functionalPlanePlacement_zero V.functional V.nonzero V.center

def carrier : Set Plane := V.place ⁻¹' F.vertexHull

def spatialGenerators : Set Space :=
  radialSlicePoint V.functional (F.toSpace Set.univ (C.vertexPoint Set.univ v)) V.level ''
    (Set.range (fun c : Face × Fin 3 => F.place c.1 ((C.triangle c.1).vertex c.2)) \
      {F.toSpace Set.univ (C.vertexPoint Set.univ v)})

def generators : Set Plane := V.place ⁻¹' V.spatialGenerators

theorem range_place : Set.range V.place =
    {z | V.functional (z - F.toSpace Set.univ (C.vertexPoint Set.univ v)) = V.level} :=
  range_functionalPlanePlacement V.functional V.nonzero
    (F.toSpace Set.univ (C.vertexPoint Set.univ v)) V.center V.level V.center_level

theorem image_carrier : V.place '' V.carrier =
    radialSlice F.vertexHull V.functional (F.toSpace Set.univ (C.vertexPoint Set.univ v))
      V.level := by
  ext z
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact ⟨hp, functionalPlanePlacement_level V.functional V.nonzero
      (F.toSpace Set.univ (C.vertexPoint Set.univ v)) V.center V.level V.center_level p⟩
  · rintro ⟨inside, level⟩
    obtain ⟨p, hp⟩ := V.range_place.ge level
    exact ⟨p, by change V.place p ∈ F.vertexHull; rw [hp]; exact inside, hp⟩

theorem spatialGenerators_subset_range : V.spatialGenerators ⊆ Set.range V.place := by
  rintro z ⟨y, ⟨⟨c, rfl⟩, different⟩, rfl⟩
  have ne : F.place c.1 ((C.triangle c.1).vertex c.2) ≠
      F.toSpace Set.univ (C.vertexPoint Set.univ v) := by
    simpa only [Set.mem_singleton_iff] using different
  rw [V.range_place]
  exact radialSlicePoint_level V.functional _ V.level _
    (V.positive.trans (V.supported c ne)).ne'

theorem image_generators : V.place '' V.generators = V.spatialGenerators :=
  Set.image_preimage_eq_of_subset V.spatialGenerators_subset_range

theorem finite_spatialGenerators : V.spatialGenerators.Finite := by
  have finite : (Set.range (fun c : Face × Fin 3 =>
      F.place c.1 ((C.triangle c.1).vertex c.2)) \
        {F.toSpace Set.univ (C.vertexPoint Set.univ v)}).Finite :=
    (Set.finite_range _).subset Set.sdiff_subset
  exact finite.image _

theorem finite_generators : V.generators.Finite :=
  Set.Finite.preimage V.place.injective.injOn V.finite_spatialGenerators

theorem carrier_eq_convexHull : V.carrier = convexHull ℝ V.generators := by
  apply Set.image_injective.mpr V.place.injective
  have image_hull : V.place '' convexHull ℝ V.generators =
      convexHull ℝ (V.place '' V.generators) := V.place.toAffineMap.image_convexHull _
  rw [V.image_carrier, image_hull, V.image_generators]
  apply radialSlice_convexHull_eq V.functional _ V.level
    (F.surface_subset_vertexHull ((F.range_toSpace Set.univ).le
      ⟨C.vertexPoint Set.univ v, rfl⟩)) V.positive
  rintro y ⟨c, rfl⟩ different
  exact (V.supported c different).le

theorem convex_carrier : Convex ℝ V.carrier :=
  F.convex_vertexHull.affine_preimage V.place.toAffineMap

theorem compact_carrier : IsCompact V.carrier := by
  rw [V.carrier_eq_convexHull]
  exact V.finite_generators.isCompact_convexHull ℝ

theorem zero_mem_interior : (0 : Plane) ∈ interior V.carrier := by
  have open_preimage : IsOpen (V.place ⁻¹' interior F.vertexHull) :=
    isOpen_interior.preimage V.place.continuous
  change (0 : Plane) ∈ interior (V.place ⁻¹' F.vertexHull)
  apply interior_mono (Set.preimage_mono interior_subset)
  rw [open_preimage.interior_eq]
  change V.place 0 ∈ interior F.vertexHull
  rw [V.place_zero]
  exact V.center_inside

theorem affineSpan_generators : affineSpan ℝ V.generators = ⊤ := by
  have full := V.convex_carrier.interior_nonempty_iff_affineSpan_eq_top.mp
    ⟨0, V.zero_mem_interior⟩
  rw [V.carrier_eq_convexHull, affineSpan_convexHull] at full
  exact full

theorem not_collinear_generators : ¬ Collinear ℝ V.generators := by
  intro collinear
  have bound := collinear.finrank_le_one
  have span := AffineSubspace.vectorSpan_eq_top_of_affineSpan_eq_top
    (k := ℝ) (V := Plane) (P := Plane) V.affineSpan_generators
  rw [span, finrank_top] at bound
  norm_num [Plane] at bound

/-- The constructed planar section has a genuine circular boundary. -/
def frontierCircleHomeomorph : frontier V.carrier ≃ₜ Metric.sphere (0 : Plane) 1 :=
  Classical.choice (V.convex_carrier.exists_homeomorph_frontier_sphere
    ⟨0, V.zero_mem_interior⟩ V.compact_carrier.isBounded)

end VertexFigure

namespace ConvexBoundary

variable {F} (P : F.ConvexBoundary)

include P

theorem exists_vertexFigure (v : C.Vertex Set.univ)
    (extreme : F.toSpace Set.univ (C.vertexPoint Set.univ v) ∈ F.vertexHull.extremePoints ℝ) :
    Nonempty (F.VertexFigure v) := by
  obtain ⟨f, h, nonzero, positive, _nonempty, projected⟩ := F.exists_vertexSlice v extreme
  obtain ⟨c, different⟩ := F.exists_corner_ne_vertex v
  have generator : F.place c.1 ((C.triangle c.1).vertex c.2) ∈ F.vertexHull :=
    subset_convexHull ℝ _ ⟨c, rfl⟩
  obtain ⟨q, in_section, in_interior⟩ :=
    exists_interior_radialSlice F.convex_vertexHull P.interior_nonempty f
      (F.toSpace Set.univ (C.vertexPoint Set.univ v)) h extreme.1 positive
      (F.place c.1 ((C.triangle c.1).vertex c.2)) generator (projected c different).1
  exact ⟨⟨f, nonzero, h, positive, q, in_interior, in_section.2,
    fun d hd => (projected d hd).1⟩⟩

def vertexFigure (v : C.Vertex Set.univ)
    (extreme : F.toSpace Set.univ (C.vertexPoint Set.univ v) ∈ F.vertexHull.extremePoints ℝ) :
    F.VertexFigure v :=
  Classical.choice (P.exists_vertexFigure v extreme)

end ConvexBoundary
end Unfoldings.SpatialFolding
