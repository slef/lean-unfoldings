module

public import Unfoldings.Cap.ForestExistence
public import Unfoldings.Development.FlatDisk

/-!
# Develop the constructed original-edge cap cut disk

Every original interior vertex meets a selected cut edge, so every remaining
vertex copy is a boundary vertex. The cut disk therefore has a genuine locally
isometric development. This existence theorem allows overlap; the geometric
nonoverlap proof requires further estimates and a source-centered forest.
-/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap.MonotoneForest

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexCap C} {t : ℝ} (M : K.MonotoneForest t)

theorem all_vertices_boundary (w : C.Vertex M.retain) : C.IsBoundaryVertex M.retain w :=
  C.selectedCut_all_vertices_boundary M.selection M.roots_eq w

/-- The cut removes all interior vertex copies, so its interior flatness has no extra hypotheses. -/
theorem interior_flat (w : C.Vertex M.retain) (internal : ¬ C.IsBoundaryVertex M.retain w) :
    C.totalAngle M.retain w = 2 * Real.pi := (internal (M.all_vertices_boundary w)).elim

/-- Actual whole-ball local isometry on the whole open cut disk, with overlap permitted. -/
theorem exists_locally_isometric_development :
    ∃ E : FacewiseDevelopment C M.retain, ∀ x, ‖(M.cutDisk x).val‖ < 1 → ∃ r > 0,
      Isometry (fun y : Metric.eball x (ENNReal.ofReal r) => E.toPlane y.val) :=
  K.folding.exists_locally_isometric_development_of_flat_disk M.retain M.cutDisk M.interior_flat

def development : FacewiseDevelopment C M.retain :=
  M.exists_locally_isometric_development.choose

theorem development_localIsometry (x : C.Realization M.retain) (inside : ‖(M.cutDisk x).val‖ < 1) :
    ∃ r > 0, Isometry (fun y : Metric.eball x (ENNReal.ofReal r) => M.development.toPlane y.val) :=
  M.exists_locally_isometric_development.choose_spec x inside

/-- A fixed original face placement determines the complete developed cut disk uniquely. -/
theorem existsUnique_normalized_development (root : Face) (target : Plane ≃ᵃⁱ[ℝ] Plane) :
    ∃! E : FacewiseDevelopment C M.retain, E.place root = target ∧
      ∀ x, ‖(M.cutDisk x).val‖ < 1 → ∃ r > 0,
        Isometry (fun y : Metric.eball x (ENNReal.ofReal r) => E.toPlane y.val) :=
  K.folding.existsUnique_normalized_isometric_development_of_flat_disk M.retain M.cutDisk
    M.interior_flat root target

end Unfoldings.ConvexCap.MonotoneForest
