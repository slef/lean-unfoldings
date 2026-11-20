module

public import Unfoldings.Polyhedron.UpperRoof
public import Unfoldings.Roof.AngularCurvature
public import Unfoldings.Roof.NormalCone
public import Mathlib.Analysis.Normed.Operator.Banach

/-! The upper roof sees exactly the upward supporting normals of the whole body. -/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialFolding.ConvexBoundary

open MeasureTheory
open scoped ENNReal

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {F : SpatialFolding C} (P : F.ConvexBoundary) (N : F.SupportingNormals)

local instance : Fintype N.UpperFace := by classical infer_instance

/-- Orthogonal projection of a spatial interior point is interior to the body footprint. -/
theorem horizontal_mem_interior_bodyFootprint {z : Space} (inside : z ∈ interior F.vertexHull) :
    Cap.horizontal z ∈ interior P.bodyFootprint := by
  have surjective : Function.Surjective Cap.horizontalCLM := by
    intro p
    refine ⟨Cap.horizontalLift p, ?_⟩
    ext i
    fin_cases i <;> rfl
  have op : IsOpen (Cap.horizontal '' interior F.vertexHull) :=
    Cap.horizontalCLM.isOpenMap surjective _ isOpen_interior
  exact (interior_maximal (Set.image_mono interior_subset) op) ⟨z, inside, rfl⟩

/-- A point of the upper boundary graph belongs to an original upward face,
including on the silhouette. -/
theorem upperPoint_mem_upperFolding_surface {p : Plane} (hp : p ∈ P.bodyFootprint) :
    P.upperPoint N p ∈ N.upperFolding.surface := by
  have cover := hp
  rw [← P.upperTriangles_cover_bodyFootprint N] at cover
  obtain ⟨f, hf⟩ := Set.mem_iUnion.mp cover
  obtain ⟨x, hx, hx_proj⟩ := ((C.triangle f.val).affineImage_carrier _ _).subset hf
  let z := F.place f.val x
  have proj : Cap.horizontal z = p := hx_proj
  have body : z ∈ F.vertexHull := F.faceImage_subset_vertexHull f.val ⟨x, hx, rfl⟩
  have z_height : z 2 = N.supportHeight f p := by
    rw [← proj]
    exact (N.on_support_iff f z).mp (N.on_plane f.val x)
  have roof_height : P.upperHeight N p = z 2 := by
    apply le_antisymm
    · exact (P.upperHeight_le N f p).trans_eq z_height.symm
    · have h := P.upperHeight_ge_body N body
      rwa [proj] at h
  have equal : P.upperPoint N p = z := by
    have horizontal := (P.horizontal_upperPoint N p).trans proj.symm
    have height := (P.height_upperPoint N p).trans roof_height
    ext i
    fin_cases i
    · exact congrArg (fun q : Plane => q 0) horizontal
    · exact congrArg (fun q : Plane => q 1) horizontal
    · exact height
  exact Set.mem_iUnion.mpr ⟨f, x, hx, equal.symm⟩

include P in
/-- A strictly upward linear functional achieves its body maximum on the upper roof. -/
theorem supports_body_iff_supports_upperFolding {n : Space} (up : 0 < n 2) (a : ℝ) :
    (∀ z ∈ F.vertexHull, inner ℝ n z ≤ a) ↔
      ∀ z ∈ N.upperFolding.surface, inner ℝ n z ≤ a := by
  constructor
  · intro h z hz
    obtain ⟨f, x, hx, rfl⟩ := Set.mem_iUnion.mp hz
    exact h _ (F.faceImage_subset_vertexHull f.val ⟨x, hx, rfl⟩)
  · intro h z hz
    let p := Cap.horizontal z
    let w := P.upperPoint N p
    have w_in : w ∈ N.upperFolding.surface :=
      P.upperPoint_mem_upperFolding_surface N ⟨z, hz, rfl⟩
    have proj : Cap.horizontal w = Cap.horizontal z := P.horizontal_upperPoint N p
    have vertically : z 2 ≤ w 2 := P.upperHeight_ge_body N hz
    have ws := h w w_in
    rw [Cap.horizontal_inner, proj] at ws
    rw [Cap.horizontal_inner]
    exact (add_le_add_right (mul_le_mul_of_nonneg_left vertically up.le) _).trans ws

/-- At an interior vertex, the normal polygon used by the curvature theorem
consists of all upward unit supporting directions of the full body. -/
theorem upperRoof_sphericalNormalPolygon_eq_body_supports
    (w : N.upperComplex.Vertex Set.univ) (internal : ¬ N.upperComplex.IsBoundaryVertex Set.univ w) :
    (P.upperRoof N).sphericalNormalPolygon w = {n : Space | ‖n‖ = 1 ∧ 0 < n 2 ∧
      ∀ z ∈ F.vertexHull,
        inner ℝ n z ≤ inner ℝ n (N.upperFolding.toSpace Set.univ
          (N.upperComplex.vertexPoint Set.univ w))} := by
  let R := P.upperRoof N
  have inside := (R.projectedVertex_mem_interior_iff w).mpr internal
  rw [R.sphericalNormalPolygon_eq_outwardNormalCone w inside]
  ext n
  simp only [ConvexRoof.outwardNormalCone, Set.mem_ofPred_eq, inner_sub_right, sub_nonpos]
  exact and_congr_right (fun _ => and_congr_right (fun up =>
    (P.supports_body_iff_supports_upperFolding N up _).symm))

end Unfoldings.SpatialFolding.ConvexBoundary
