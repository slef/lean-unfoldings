module

public import Unfoldings.Cap.UniformExtendedAllRadiusContact
public import Unfoldings.Cap.ClipOriginalPlacementAgreement
public import Unfoldings.Cap.ExtendedOriginalRetain
public import Unfoldings.Cap.ClipOriginalLocalSeparation
public import Unfoldings.Cap.DeepRoofClips
public import Unfoldings.Cap.SectorDevelopment

/-! Uniform control of actual original closed-face contacts outside finitely many radii. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap

universe u v

theorem exists_uniform_original_sector_all_radius_contact
    (t : ℝ) (positive : 0 < t) (small : t < 1) :
    ∃ φ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      ∀ {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexCap C),
        K.TiltBound φ → ∀ {origin : C.Vertex Set.univ} (M : K.SectorForest t origin),
          ¬ C.IsBoundaryVertex Set.univ origin →
          0 < K.roofHeight (K.projectedVertex origin) →
          ∀ E : FacewiseDevelopment C M.retain,
            ∀ f g (p q : Plane),
                p ∈ (K.projectedTriangle f).carrier →
                q ∈ (K.projectedTriangle g).carrier →
                E.projectedPlacement K f p = E.projectedPlacement K g q → p = q := by
  classical
  obtain ⟨ε, εbounds, φ, φbounds, normal, construct⟩ :=
    exists_uniform_extended_all_radius_closed_contact.{u, v} t positive small
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
  have inclusion := M.extendedOriginalRetain_subset_radial T F lower R
  let : PreconnectedSpace (Metric.closedBall (0 : Plane) 1) :=
    Subtype.preconnectedSpace (convex_closedBall (0 : Plane) 1).isPreconnected
  let : PreconnectedSpace (C.Realization M.retain) :=
    M.cutDisk.symm.surjective.denseRange.preconnectedSpace M.cutDisk.symm.continuous
  obtain ⟨A, agree⟩ := L.originalPart.exists_development_agreeing_original_placements lower
    M.retain R.retain D inclusion E
  have contacts := construct K tilt M internal source_height lower T
    conforming cutoff cutoff_positive deep A
  let := @Fintype.ofFinite _ L.originalPart.partition.finite
  intro f g p q first last same
  obtain ⟨center, different⟩ := exists_ne (E.projectedPlacement K f p)
  have positive_radius : 0 < ‖E.projectedPlacement K f p - center‖ :=
    norm_pos_iff.mpr (sub_ne_zero.mpr different.symm)
  exact L.originalPart.original_contact_of_local_roof_contact lower A E agree
    (Metric.ball (K.projectedVertex origin) (ε * (cutoff / 16))) cover center ∅
    (by
      dsimp only
      intro f g p q first last _ _ same
      exact contacts f g p q first last same)
    f g first last positive_radius (Set.notMem_empty _) same

end Unfoldings.ConvexCap
