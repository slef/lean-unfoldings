module

public import Unfoldings.Roof.PotentialCutForest
public import Unfoldings.Roof.Topology

/-! Potential-selected cuts form genuine intrinsic disks, flat away from cut curvature vertices. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof.PotentialCutForest

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexRoof C} {f : Plane → ℝ} {cuts : Set Plane} (R : K.PotentialCutForest f cuts)

def retain : Set C.Seam := C.selectedRetain R.selection

theorem rootedForest :
    (C.relativeCutGraph R.retain Set.univ).IsRootedForest (C.relativeCutRoots Set.univ) := by
  apply C.selectedCut_rootedForest_of_root_support R.selection
  · intro w boundary
    exact (Set.ext_iff.mp R.roots_eq w).mpr (Or.inl boundary)
  · intro w root incident
    rcases incident with boundary | ⟨s, b, endpoint⟩
    · exact boundary
    · obtain ⟨e, chosen⟩ := not_not.mp s.property.2
      have on_edge : K.projectedVertex w ∈
          (K.projectedTriangle (C.left s.val).face).edge (C.left s.val).edge := by
        change w = C.seamVertex s.val b at endpoint
        rw [endpoint]
        cases b
        · exact left_mem_segment ℝ _ _
        · exact right_mem_segment ℝ _ _
      have selected : (K.projectedTriangle (C.left s.val).face).edge (C.left s.val).edge ⊆ cuts :=
        chosen ▸ R.selected_subset e
      rcases (Set.ext_iff.mp R.roots_eq w).mp root with boundary | outside
      · exact boundary
      · exact (outside (selected on_edge)).elim

/-- The cut metric realization is an actual disk, not a complement of drawn segments. -/
def cutDisk : C.Realization R.retain ≃ₜ Metric.closedBall (0 : Plane) 1 :=
  K.folding.cutDiskHomeomorphOfRootedForest (Set.subset_univ _) K.diskHomeomorph R.rootedForest

theorem curvature_endpoints
    (covered : ∀ v : C.Vertex Set.univ, 0 < C.interiorAngularDefect Set.univ v →
      K.projectedVertex v ∈ cuts)
    (v : C.Vertex Set.univ) (curved : 0 < C.interiorAngularDefect Set.univ v) :
    ∃ s b, s ∉ R.retain ∧ v = C.seamVertex s b := by
  have internal : ¬ C.IsBoundaryVertex Set.univ v := by
    intro boundary
    have zero : C.interiorAngularDefect Set.univ v = 0 := by
      simp only [TriangleComplex.interiorAngularDefect, ite_eq_left boundary]
    exact curved.ne' zero
  have nonroot : v ∉ R.parents.roots := by
    intro root
    exact ((Set.ext_iff.mp R.roots_eq v).mp root).elim internal
      (fun outside => outside (covered v curved))
  let e : {v // v ∉ R.parents.roots} := ⟨v, nonroot⟩
  have cut : R.selection.edge e ∉ R.retain := fun kept => kept ⟨e, rfl⟩
  rcases R.selection.link e with ⟨first, _last⟩ | ⟨first, _last⟩
  · exact ⟨R.selection.edge e, false, cut, first⟩
  · exact ⟨R.selection.edge e, true, cut, first⟩

theorem interior_flat
    (covered : ∀ v : C.Vertex Set.univ, 0 < C.interiorAngularDefect Set.univ v →
      K.projectedVertex v ∈ cuts)
    (w : C.Vertex R.retain) (internal : ¬ C.IsBoundaryVertex R.retain w) :
    C.totalAngle R.retain w = 2 * Real.pi :=
  K.interior_flat_of_curvature_cut R.retain (R.curvature_endpoints covered) w internal

/-- The actual cut disk admits a rigid face development, locally isometric in its interior.
Nonoverlap remains a separate theorem. -/
theorem exists_isometric_development
    (covered : ∀ v : C.Vertex Set.univ, 0 < C.interiorAngularDefect Set.univ v →
      K.projectedVertex v ∈ cuts) :
    ∃ D : FacewiseDevelopment C R.retain, ∀ x, ‖(R.cutDisk x).val‖ < 1 → ∃ r > 0,
      Isometry (fun y : Metric.eball x (ENNReal.ofReal r) => D.toPlane y.val) :=
  K.exists_development_of_curvature_cut_disk R.retain R.cutDisk (R.curvature_endpoints covered)

end Unfoldings.ConvexRoof.PotentialCutForest
