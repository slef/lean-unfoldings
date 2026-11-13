module

public import Unfoldings.Roof.CompletionDomain

public import Unfoldings.Roof.CompletionAllRadiusContact
public import Unfoldings.Roof.CompletionOriginalPlacementAgreement
public import Unfoldings.Roof.CompletionOriginalForestRetention
public import Unfoldings.Roof.CompletionOriginalLocalSeparation
public import Unfoldings.Roof.SectorDevelopment

/-! Uniform control of actual original closed-face contacts at all radii. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof

universe u v

theorem exists_uniform_original_sector_all_radius_contact
    (t : ℝ) (positive : 0 < t) (small : t < 1) :
    ∃ φ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      ∀ {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexRoof C),
        K.TiltBound φ → ∀ {origin : Plane} (M : K.SectorForest t origin),
          ∀ E : FacewiseDevelopment C M.retain,
            ∀ f g (p q : Plane),
                p ∈ (K.projectedTriangle f).carrier →
                q ∈ (K.projectedTriangle g).carrier →
                E.roofPlacement K f p = E.roofPlacement K g q → p = q := by
  classical
  obtain ⟨ε, εbounds, φ, φbounds, normal, construct⟩ :=
    exists_uniform_completion_all_radius_closed_contact.{u, v} t positive small
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
  have inclusion := M.completionOriginalRetain_subset_radial T R
  let : PreconnectedSpace (Metric.closedBall (0 : Plane) 1) :=
    Subtype.preconnectedSpace (convex_closedBall (0 : Plane) 1).isPreconnected
  let : PreconnectedSpace (C.Realization M.retain) :=
    M.cutDisk.symm.surjective.denseRange.preconnectedSpace M.cutDisk.symm.continuous
  obtain ⟨A, agree⟩ := L.originalPart.exists_development_agreeing_original_placements
    M.retain R.retain D inclusion E
  have contacts := construct K tilt M T cutoff cutoff_positive deep A
  let := @Fintype.ofFinite _ L.originalPart.partition.finite
  intro f g p q first last same
  obtain ⟨center, different⟩ := exists_ne (E.roofPlacement K f p)
  have positive_radius : 0 < ‖E.roofPlacement K f p - center‖ :=
    norm_pos_iff.mpr (sub_ne_zero.mpr different.symm)
  exact L.originalPart.original_contact_of_local_roof_contact A E agree
    (Metric.ball origin (ε * (cutoff / 16))) cover center ∅
    (by
      dsimp only
      intro f g p q first last _ _ same
      exact contacts f g p q first last same)
    f g first last positive_radius (Set.notMem_empty _) same

end Unfoldings.ConvexRoof
