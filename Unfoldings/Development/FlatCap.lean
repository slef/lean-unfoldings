module

public import Unfoldings.Development.GermCones
public import Unfoldings.Cap.RimAngles
public import Unfoldings.Geometry.NorthFrame

/-! An actual convex planar placement is a flat cap with exactly its original corner angles. -/

@[expose] public section

noncomputable section

namespace Unfoldings.Cap

@[simp] theorem horizontal_horizontalLift (p : Plane) : horizontal (horizontalLift p) = p := by
  ext i
  fin_cases i <;> rfl

end Unfoldings.Cap

namespace Unfoldings.FacewiseDevelopment

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  (D : FacewiseDevelopment C Set.univ)

/-- The actual planar placements, regarded as horizontal spatial rigid placements. -/
def horizontalFolding : SpatialFolding C where
  place f := Cap.horizontalLiftIsometry.toAffineIsometry.comp (D.place f).toAffineIsometry
  joined s x := congrArg Cap.horizontalLift (D.joined s (Set.mem_univ _) x)

theorem horizontalFolding_toSpace (x : C.Realization Set.univ) :
    D.horizontalFolding.toSpace Set.univ x = Cap.horizontalLift (D.toPlane x) := by
  obtain ⟨⟨f, y⟩, rfl⟩ := MetricGluing.point_surjective C.Cell (C.glue Set.univ) x
  rfl

theorem horizontalFolding_projection (x : C.Realization Set.univ) :
    Cap.horizontal (D.horizontalFolding.toSpace Set.univ x) = D.toPlane x := by
  rw [D.horizontalFolding_toSpace, Cap.horizontal_horizontalLift]

theorem horizontalFolding_footprint :
    Cap.horizontal '' D.horizontalFolding.surface = Set.range D.toPlane := by
  rw [← D.horizontalFolding.range_toSpace Set.univ, ← Set.range_comp]
  exact congrArg Set.range (funext D.horizontalFolding_projection)

/-- Convexity and an actual injective placement make a genuine zero-height cap.
This will be applied to pieces inside one original face. -/
def flatCap (injective : Function.Injective D.toPlane)
    (convex : Convex ℝ (Set.range D.toPlane))
    (inside : (interior (Set.range D.toPlane)).Nonempty) : ConvexCap C where
  folding := D.horizontalFolding
  normal _ := Cap.northLift 0
  normal_unit _ := Cap.northLift_zero_unit
  normal_upward _ := by norm_num [Cap.northLift]
  normal_tangent f x := by
    change inner ℝ (Cap.northLift 0) (Cap.horizontalLift ((D.place f).linear x)) = 0
    simp [PiLp.inner_apply, Fin.sum_univ_three, Cap.northLift, Cap.horizontalLift]
  supporting f g x := by
    change inner ℝ (Cap.northLift 0)
      (Cap.horizontalLift (D.place g x.val) - Cap.horizontalLift (D.place f 0)) ≤ 0
    simp [PiLp.inner_apply, Fin.sum_univ_three, Cap.northLift, Cap.horizontalLift]
  projection_injective := by
    intro x y same
    apply injective
    exact (D.horizontalFolding_projection x).symm.trans
      (same.trans (D.horizontalFolding_projection y))
  convex_projection := by rwa [D.horizontalFolding_footprint]
  interior_projection := by rwa [D.horizontalFolding_footprint]
  rim_horizontal _ _ := rfl
  corners_above _ _ := le_rfl

variable (injective : Function.Injective D.toPlane) (convex : Convex ℝ (Set.range D.toPlane))
  (inside : (interior (Set.range D.toPlane)).Nonempty)

theorem flatCap_footprint : (D.flatCap injective convex inside).footprint = Set.range D.toPlane :=
  D.horizontalFolding_footprint

theorem flatCap_projectedTriangle_vertex (f : Face) (i : Fin 3) :
    ((D.flatCap injective convex inside).projectedTriangle f).vertex i =
      D.place f ((C.triangle f).vertex i) :=
  Cap.horizontal_horizontalLift _

/-- The actual fine corner angle is unchanged by its planar rigid placement. -/
theorem flatCap_projected_cornerAngle (f : Face) (i : Fin 3) :
    ((D.flatCap injective convex inside).projectedTriangle f).cornerAngle i =
      (C.triangle f).cornerAngle i := by
  unfold Triangle.cornerAngle
  simp only [D.flatCap_projectedTriangle_vertex]
  exact (D.place f).toAffineIsometry.angle_map _ _ _

theorem flatCap_projectedTotalAngle (retain : Set C.Seam) (w : C.Vertex retain) :
    (D.flatCap injective convex inside).projectedTotalAngle retain w = C.totalAngle retain w := by
  classical
  simp only [ConvexCap.projectedTotalAngle, D.flatCap_projected_cornerAngle,
    TriangleComplex.totalAngle]

theorem flatCap_projectedGermRay {w : C.Vertex Set.univ} (p : C.LinkGerm Set.univ w) :
    (D.flatCap injective convex inside).projectedGermRay p = D.germRay p := by
  change Cap.horizontal (Cap.horizontalLift (D.germFarPoint p.val)) -
    Cap.horizontal (D.horizontalFolding.toSpace Set.univ (C.vertexPoint Set.univ w)) = _
  rw [Cap.horizontal_horizontalLift, D.horizontalFolding_projection]
  rfl

include injective convex inside in
/-- Any actual convex embedded planar boundary fan has its exact geometric endpoint angle. -/
theorem totalAngle_eq_boundary_endpoint {w : C.Vertex Set.univ} {n : ℕ}
    (chain : (C.linkSystem Set.univ w).Chain n)
    (start : C.linkMate Set.univ w chain.first = chain.first) (covers : ∀ p, chain.Visited p) :
    C.totalAngle Set.univ w = InnerProductGeometry.angle (D.germRay chain.first)
      (D.germRay (C.linkTurn Set.univ w chain.last)) := by
  have endpoint := (D.flatCap injective convex inside).projected_boundary_angle_eq_endpoint
    chain start covers
  rwa [D.flatCap_projectedTotalAngle, D.flatCap_projectedGermRay,
    D.flatCap_projectedGermRay] at endpoint

end Unfoldings.FacewiseDevelopment
