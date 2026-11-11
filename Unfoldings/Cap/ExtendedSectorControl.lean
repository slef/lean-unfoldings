module

public import Unfoldings.Cap.ExtendedPathWedges
public import Unfoldings.Cap.CompletedSectorQuadrants

/-! Construct five common developed quadrant frames for the actual meshed roof extension. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap

universe u v

/-- Fix all numerical sector margins before the cap and both meshes. The original three sectors
and the two forward sectors then have one actual projection-calibrated quadrant system. -/
theorem exists_uniform_extended_sector_control (t : ℝ) (positive : 0 < t) (small : t < 1) :
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
              L.partition.pairedComplex.totalInteriorAngularDefect Set.univ < Real.pi ∧
                ∀ D : FacewiseDevelopment L.partition.pairedComplex R.completedRetain,
                  Nonempty (R.FiveSectorFrameData positive small D) := by
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
  exact control Q roof_tilt (K.projectedVertex origin) (M.extendedGeometricCuts F) R wedges

end Unfoldings.ConvexCap
