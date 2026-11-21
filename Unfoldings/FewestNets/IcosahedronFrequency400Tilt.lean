module

public import Unfoldings.FewestNets.CheckedDevelopmentCellTilt
public import Unfoldings.FewestNets.FiniteMeshCorner400Bounds
public import Unfoldings.FewestNets.IcosahedronFrequency100Scalars
public import Unfoldings.FewestNets.IcosahedronRealizedCellTilt

/-! A checked frequency-400 record tilt bounds the entire actual cell. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FewestNets.Icosahedron

open MeshStar InnerProductGeometry

theorem angle_le_of_q400_developmentCellTilt {a : meshSites 400}
    (label : PerimeterIndex 400) (realized : perimeterIndexRealizes a label)
    {φ : ℚ} (nonnegative : 0 ≤ φ)
    (check : checkDevelopmentCellTilt 400 (perimeterIndexRecordKey label) φ = true)
    {N : Space} (inside : N ∈ sphericalVoronoiCell (fun b : meshSites 400 => (b : Space)) a) :
    angle (a : Space) N ≤ φ := by
  have hq : (0 : ℕ) < 400 := by decide
  have qbig : (100 : ℕ) ≤ 400 := by decide
  have φ_nonnegative : (0 : ℝ) ≤ φ := by exact_mod_cast nonnegative
  simp only [checkDevelopmentCellTilt, Bool.or_eq_true] at check
  rcases check with uniform | radius
  · have unit : ‖N‖ = 1 := by
      simpa only [Metric.mem_sphere, dist_zero_right] using inside.2
    rw [angle_comm]
    exact (angle_le_meshTilt_of_mem_normalCone hq unit a inside.1).trans
      (meshTilt_le_of_checkUniformRecordTilt hq uniform)
  · let h := certificateDenominator_pos
    rcases label with p | (p | p)
    · let key := (faceMeshKeys 400).get p.2.1
      have mem : key ∈ faceMeshKeys 400 := List.get_mem _ _
      obtain ⟨R⟩ := realized
      exact R.angle_le_of_gnomonicVertex_radius qbig hq
        (fun k => (q400_face_corner_bounds mem k).1) φ_nonnegative
        (fun k => MeshStar.Checked.gnomonicVertex_norm_le_tan_of_check h
          (checkFace h 400 key.1 key.2) radius k) inside
    · let key := (seamMeshKeys 400).get p.2.1
      have mem : key ∈ seamMeshKeys 400 := List.get_mem _ _
      obtain ⟨R⟩ := realized
      exact R.angle_le_of_gnomonicVertex_radius qbig hq
        (fun k => (q400_seam_corner_bounds mem k).1) φ_nonnegative
        (fun k => MeshStar.Checked.gnomonicVertex_norm_le_tan_of_check h
          (checkSeam h 400 key) radius k) inside
    · obtain ⟨R⟩ := realized
      exact R.angle_le_of_gnomonicVertex_radius qbig hq
        (fun k => (q400_pentagon_corner_bounds k).1) φ_nonnegative
        (fun k => MeshStar.Checked.gnomonicVertex_norm_le_tan_of_check h
          (checkPentagon h 400) radius k) inside

end Unfoldings.FewestNets.Icosahedron
