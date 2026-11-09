module

public import Unfoldings.Source.SourceBall
public import Unfoldings.Polyhedron.Convex
public import Unfoldings.Geometry.ConvexRigidity
public import Mathlib.Analysis.Convex.Topology

/-!
# Constructed initial rigid placements in the source face

For a source in an original face interior, the source chart and that face's
proved isometry give an actual isometric convex patch. Its rigid extension
agrees with every shortest-path source vector on the source-ball portion of
the face. This fixes the initial motion for finite seam-word developments.
-/

@[expose] public section

open scoped ENNReal

noncomputable section

namespace Unfoldings.SpatialFolding.ConvexBoundary

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {F : SpatialFolding C} (P : F.ConvexBoundary)

theorem exists_initial_face_placement :
    letI := P.metricSpace
    ∀ (f : Face) (x : C.Cell f), x.val ∈ interior (C.triangle f).carrier →
      ∀ R : SourceFrame (C.faceMap Set.univ f x),
        ∃ A : Plane ≃ᵃⁱ[ℝ] Plane, ∀ (y : C.Cell f), dist y.val x.val < R.radius →
          ∀ p : SourcePath (C.faceMap Set.univ f x), p.target = C.faceMap Set.univ f y →
            R.coordinate p.path p.geodesic = A y.val := by
  let := P.metricSpace
  intro f x inside R
  let s := (C.triangle f).carrier ∩ Metric.ball x.val R.radius
  have convex_s : Convex ℝ s := (C.triangle f).convex_carrier.inter (convex_ball _ _)
  have interior_s : (interior s).Nonempty := by
    refine ⟨x.val, ?_⟩
    rw [interior_inter, Metric.isOpen_ball.interior_eq]
    exact ⟨inside, Metric.mem_ball_self R.positive⟩
  let point (y : s) : C.Cell f := ⟨y.val, y.property.1⟩
  have near (y : s) : C.faceMap Set.univ f (point y) ∈
      Metric.eball (C.faceMap Set.univ f x) (ENNReal.ofReal R.radius) := by
    change edist (C.faceMap Set.univ f (point y)) (C.faceMap Set.univ f x) < _
    rw [(F.faceMap_isometry Set.univ f).edist_eq, edist_dist]
    exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg dist_nonneg).mpr y.property.2
  let lift (y : s) : Metric.eball (C.faceMap Set.univ f x) (ENNReal.ofReal R.radius) :=
    ⟨C.faceMap Set.univ f (point y), near y⟩
  have lift_isometry : Isometry lift := fun a b => F.faceMap_isometry Set.univ f (point a) (point b)
  obtain ⟨A, agrees⟩ := exists_rigid_extension_convex convex_s interior_s
    (R.chartCoordinates ∘ lift) (R.chartCoordinates_isometry.comp lift_isometry)
  refine ⟨A, ?_⟩
  intro y near_y p target
  let z : s := ⟨y.val, y.property, near_y⟩
  have near_target : p.target ∈ Metric.eball (C.faceMap Set.univ f x)
      (ENNReal.ofReal R.radius) := target.symm ▸ near z
  have coordinate := R.coordinate_eq_chart_displacement p.path p.geodesic near_target
  have same : (⟨p.target, near_target⟩ : Metric.eball (C.faceMap Set.univ f x)
      (ENNReal.ofReal R.radius)) = lift z := Subtype.ext target
  rw [same] at coordinate
  exact coordinate.trans (agrees z).symm

end Unfoldings.SpatialFolding.ConvexBoundary
