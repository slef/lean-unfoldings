module

public import Unfoldings.Cap.ExtendedSubtreeSectors
public import Unfoldings.Cap.ExtendedPathWedges
public import Unfoldings.Cap.CompletedFlatBanks
public import Unfoldings.Cap.CompletedParentBankNoncrossing
public import Unfoldings.Cap.CompletedSectorQuadrants

/-! Uniform actual paired-bank separation on the constructed roof extension. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap

universe u v

/-- Fix the sector parameter before both meshes. Any contact of an actual pair of parent banks
before its child endpoint is a matched-parameter contact on a redundant flat slit.
This compares the two banks of each seam; global comparison of different seams remains separate. -/
theorem exists_uniform_extended_parent_bank_separation
    (t : ℝ) (positive : 0 < t) (small : t < 1) :
    ∃ φ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      ∀ {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexCap C),
        K.TiltBound φ → ∀ {origin : C.Vertex Set.univ} (M : K.SectorForest t origin)
          (internal : ¬ C.IsBoundaryVertex Set.univ origin)
          (source_height : 0 < K.roofHeight (K.projectedVertex origin))
          {Z : ℝ} (lower : Z < 0) (T : K.ClipSpatialTriangles Z),
            TriangleFamily.Conforming T.projectedTriangle →
              let inside := (K.projectedVertex_mem_interior_iff origin).mpr internal
              let F := T.cornerTails inside source_height lower
              let L := F.mesh T lower
              letI := @Fintype.ofFinite _ L.partition.finite
              let R := (M.cornerExtendedOutwardForest positive small T
                internal source_height lower).val
              ∀ (D : FacewiseDevelopment L.partition.pairedComplex R.completedRetain)
                (e : {w : L.partition.pairedComplex.Vertex Set.univ //
                  w ∉ R.spanningCompletion.parents.roots}) {s r : ℝ},
                s < 1 → r < 1 → R.parentEntrancePoint D e s = R.parentExitPoint D e r →
                  s = r ∧ R.completedSubtreeCurvature e.val = 0 := by
  obtain ⟨φ, bounds, normal, control⟩ :=
    exists_uniform_completed_fiveSectorFrameData.{0, 0} t positive small
  refine ⟨φ, bounds, ?_⟩
  intro Face _ C K tilt origin M internal source_height Z lower T conforming
  let inside := (K.projectedVertex_mem_interior_iff origin).mpr internal
  let F := T.cornerTails inside source_height lower
  let L := F.mesh T lower
  let Q := L.partition.normalizedCap L.conforming lower
  let := @Fintype.ofFinite _ L.partition.finite
  let R := (M.cornerExtendedOutwardForest positive small T internal source_height lower).val
  have height : ∀ f, (3 : ℝ) / 4 ≤ K.normal f 2 := fun f => normal.trans (tilt f)
  have wedges := M.cornerExtendedOutward_curvedPathWedges positive small T internal source_height
    lower conforming height
  have roof_tilt : Q.TiltBound φ := L.partition.normalizedCap_tiltBound L.conforming lower tilt
  obtain ⟨budget, frames⟩ := control Q roof_tilt (K.projectedVertex origin)
    (M.extendedGeometricCuts F) R wedges
  refine fun D e s r s_before r_before same => ?_
  obtain ⟨B⟩ := frames D
  have flat : R.completedSubtreeCurvature e.val = 0 := by
    apply le_antisymm _ (R.completedSubtreeCurvature_nonneg e.val)
    by_contra positive_curvature
    have curved := lt_of_not_ge positive_curvature
    have member := R.mem_cuts_of_completedSubtreeCurvature_pos
      (M.extended_cut_curvature_covered T internal source_height lower conforming height)
      e.val curved
    obtain ⟨i, top, sectors⟩ := M.cornerExtendedOutward_subtree_sectors positive small T internal
      source_height lower conforming height e member
    exact B.parent_bank_interiors_ne i e top sectors s_before r_before budget curved same
  exact ⟨R.completed_flat_bank_intersection_parameter_eq D e flat same, flat⟩

end Unfoldings.ConvexCap
