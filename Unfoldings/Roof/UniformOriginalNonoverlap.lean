module

public import Unfoldings.Roof.CompletionDomain

public import Unfoldings.Roof.CompletionFaceSeparation
public import Unfoldings.Roof.CompletionOriginalForestRetention
public import Unfoldings.Roof.CompletionOriginalLocalSeparation
public import Unfoldings.Roof.SectorDevelopment

/-! Uniformly small tilt makes original sector-forest developments nonoverlapping. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof

universe u v

theorem exists_uniform_original_sector_nonoverlap (t : ℝ) (positive : 0 < t) (small : t < 1) :
    ∃ φ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      ∀ {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexRoof C),
        K.TiltBound φ → ∀ {origin : Plane} (M : K.SectorForest t origin),
          ∀ E : FacewiseDevelopment C M.retain, E.Nonoverlapping := by
  classical
  obtain ⟨ε, εbounds, φ, φbounds, normal, separate⟩ :=
    exists_uniform_completion_face_separation.{u, v} t positive small
  refine ⟨φ, φbounds, ?_⟩
  intro Face _ C K tilt origin M E
  obtain ⟨r, rpositive, contained⟩ :=
    K.compact_footprint.isBounded.subset_ball_lt 0 origin
  let cutoff := 32 * r / ε
  have cutoff_positive : 0 < cutoff := div_pos (by positivity) εbounds.1
  have radius : ε * (cutoff / 16) = 2 * r := by
    dsimp only [cutoff]
    field_simp [ne_of_gt εbounds.1]
    ring
  have cover : K.footprint ⊆ Metric.ball origin (ε * (cutoff / 16)) := by
    rw [radius]
    exact contained.trans (Metric.ball_subset_ball (by linarith))
  obtain ⟨T⟩ := K.exists_completionMesh φbounds.1 φbounds.2
    (isCompact_closedBall origin cutoff) K.originalEdgeEquations K.originalEdgeEquations_ne_zero
  have deep : Metric.closedBall origin cutoff ⊆ interior
      (T.domain) :=
    fun _ member => T.covers (Or.inr member)
  let L := T.radialMesh M.inside
  let := @Fintype.ofFinite _ L.mesh.finite
  let R := (M.completionOutwardForest T positive small).val
  have height (i) : (3 : ℝ) / 4 ≤
      (T.supportPlanes i).normal 2 :=
    normal.trans (K.completionPlanes_tilt φbounds.1 φbounds.2 tilt T.tentHeight i)
  obtain ⟨D, _local_isometry⟩ := M.completionOutward_exists_development T positive small height
  have separation := separate K tilt M T cutoff cutoff_positive deep D
  have inclusion := M.completionOriginalRetain_subset_radial T R
  let : PreconnectedSpace (Metric.closedBall (0 : Plane) 1) :=
    Subtype.preconnectedSpace (convex_closedBall (0 : Plane) 1).isPreconnected
  let : PreconnectedSpace (C.Realization M.retain) :=
    M.cutDisk.symm.surjective.denseRange.preconnectedSpace M.cutDisk.symm.continuous
  exact L.originalPart.original_nonoverlap_of_local_roof_separation M.retain R.retain
    D inclusion (Metric.ball origin (ε * (cutoff / 16))) cover separation E

end Unfoldings.ConvexRoof
