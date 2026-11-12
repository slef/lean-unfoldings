module

public import Unfoldings.Cap.UniformExtendedFaceSeparation
public import Unfoldings.Cap.ExtendedOriginalRetain
public import Unfoldings.Cap.ClipOriginalLocalSeparation
public import Unfoldings.Cap.DeepRoofClips
public import Unfoldings.Cap.SectorDevelopment

/-! Uniformly small tilt makes original sector-forest developments nonoverlapping. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap

universe u v

theorem exists_uniform_original_sector_nonoverlap (t : ℝ) (positive : 0 < t) (small : t < 1) :
    ∃ φ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      ∀ {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexCap C),
        K.TiltBound φ → ∀ {origin : C.Vertex Set.univ} (M : K.SectorForest t origin),
          ¬ C.IsBoundaryVertex Set.univ origin →
          0 < K.roofHeight (K.projectedVertex origin) →
          ∀ E : FacewiseDevelopment C M.retain, E.Nonoverlapping := by
  classical
  obtain ⟨ε, εbounds, φ, φbounds, normal, separate⟩ :=
    exists_uniform_extended_face_separation.{u, v} t positive small
  refine ⟨φ, φbounds, ?_⟩
  intro Face _ C K tilt origin M internal source_height E
  let inside := (K.projectedVertex_mem_interior_iff origin).mpr internal
  obtain ⟨r, rpositive, contained⟩ :=
    K.compact_footprint.isBounded.subset_ball_lt 0 (K.projectedVertex origin)
  let cutoff := 32 * r / ε
  have cutoff_positive : 0 < cutoff := div_pos (by positivity) εbounds.1
  have radius : ε * (cutoff / 16) = 2 * r := by
    dsimp only [cutoff]
    field_simp [ne_of_gt εbounds.1]
    ring
  have cover : K.footprint ⊆ Metric.ball (K.projectedVertex origin) (ε * (cutoff / 16)) := by
    rw [radius]
    exact contained.trans (Metric.ball_subset_ball (by linarith))
  obtain ⟨Z, lower, deep⟩ :=
    K.exists_clip_interior_contains_closedBall (K.projectedVertex origin) cutoff
  let T := (K.clipSpatialTriangles (interior_subset inside) source_height lower.le).refined
  have conforming : TriangleFamily.Conforming T.projectedTriangle :=
    (K.clipSpatialTriangles (interior_subset inside) source_height lower.le).refined_conforming
  let F := T.cornerTails inside source_height lower
  let L := F.mesh T lower
  let := @Fintype.ofFinite _ L.partition.finite
  let R := (M.cornerExtendedOutwardForest positive small T internal source_height lower).val
  have height : ∀ f, (3 : ℝ) / 4 ≤ K.normal f 2 := fun f => normal.trans (tilt f)
  obtain ⟨D, _local_isometry⟩ := M.cornerExtendedOutward_exists_development positive small T
    internal source_height lower conforming height
  have separation := separate K tilt M internal source_height lower T conforming cutoff
    cutoff_positive deep D
  have inclusion := M.extendedOriginalRetain_subset_radial T F lower R
  let : PreconnectedSpace (Metric.closedBall (0 : Plane) 1) :=
    Subtype.preconnectedSpace (convex_closedBall (0 : Plane) 1).isPreconnected
  let : PreconnectedSpace (C.Realization M.retain) :=
    M.cutDisk.symm.surjective.denseRange.preconnectedSpace M.cutDisk.symm.continuous
  exact L.originalPart.original_nonoverlap_of_local_roof_separation lower M.retain R.retain
    D inclusion (Metric.ball (K.projectedVertex origin) (ε * (cutoff / 16))) cover separation E

end Unfoldings.ConvexCap
