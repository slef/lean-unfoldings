module

public import Unfoldings.Roof.SectorForestGeometry
public import Unfoldings.Roof.Topology
public import Unfoldings.Complex.SelectedCuts
public import Unfoldings.Development.FlatDisk

/-! The source-centered original-edge forest yields a locally isometric developed cut disk. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof.SectorForest

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexRoof C} {t : ℝ} {origin : Plane} (M : K.SectorForest t origin)

def retain : Set C.Seam := C.selectedRetain M.selection

theorem rootedForest : (C.relativeCutGraph M.retain Set.univ).IsRootedForest
    (C.relativeCutRoots Set.univ) := C.selectedCut_rootedForest M.selection M.roots_eq

theorem original_edges : M.selection.graph ≤ C.seamGraph := M.selection.graph_le rfl

def cutDisk : C.Realization M.retain ≃ₜ Metric.closedBall (0 : Plane) 1 :=
  C.selectedCutDisk M.selection M.roots_eq K.folding K.diskHomeomorph

theorem all_vertices_boundary (w : C.Vertex M.retain) : C.IsBoundaryVertex M.retain w :=
  C.selectedCut_all_vertices_boundary M.selection M.roots_eq w

theorem interior_flat (w : C.Vertex M.retain) (internal : ¬ C.IsBoundaryVertex M.retain w) :
    C.totalAngle M.retain w = 2 * Real.pi := (internal (M.all_vertices_boundary w)).elim

/-- Overlap remains allowed here; global geometric separation is a further theorem. -/
theorem exists_locally_isometric_development :
    ∃ E : FacewiseDevelopment C M.retain, ∀ x, ‖(M.cutDisk x).val‖ < 1 → ∃ r > 0,
      Isometry (fun y : Metric.eball x (ENNReal.ofReal r) => E.toPlane y.val) :=
  K.folding.exists_locally_isometric_development_of_flat_disk M.retain M.cutDisk M.interior_flat

end Unfoldings.ConvexRoof.SectorForest
