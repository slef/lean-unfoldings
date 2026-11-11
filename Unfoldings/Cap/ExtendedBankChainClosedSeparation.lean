module

public import Unfoldings.Cap.ExtendedBankChains
public import Unfoldings.Cap.CompletedBankClosedContact
public import Unfoldings.Cap.ExtendedPathWedges

/-! Uniform noncrossing of opposite complete branching banks in the actual roof development. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap

universe u v

/-- Closed opposite banks along an actual complete path can coincide only over the same
projected surface point, including all original and auxiliary branch vertices. The positive
threshold precedes both meshes; no bank separation or branch-contact hypothesis is supplied. -/
theorem exists_uniform_extended_bank_chain_closed_separation
    (t : ℝ) (positive : 0 < t) (small : t < 1) :
    ∃ φ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      ∀ {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexCap C),
        K.TiltBound φ → ∀ (origin : C.Vertex Set.univ) (M : K.SectorForest t origin)
          (internal : ¬ C.IsBoundaryVertex Set.univ origin)
          (source_height : 0 < K.roofHeight (K.projectedVertex origin))
          {Z : ℝ} (lower : Z < 0) (T : K.ClipSpatialTriangles Z),
            TriangleFamily.Conforming T.projectedTriangle →
              let inside := (K.projectedVertex_mem_interior_iff origin).mpr internal
              let F := T.cornerTails inside source_height lower
              let L := F.mesh T lower
              let Q := L.partition.normalizedCap L.conforming lower
              letI := @Fintype.ofFinite _ L.partition.finite
              let R := (M.cornerExtendedOutwardForest positive small T
                internal source_height lower).val
              ∀ D : FacewiseDevelopment L.partition.pairedComplex R.completedRetain,
                ∀ w : L.partition.pairedComplex.Vertex Set.univ,
                  Q.projectedVertex w ∈ M.extendedGeometricCuts F →
                  ∀ j k : Fin (R.spanningCompletion.parents.distanceToRoot w),
                    ∀ s r : unitInterval,
                      R.parentExitPoint D (R.completedBankChain w j) (1 - (s : ℝ)) =
                        R.parentEntrancePoint D (R.completedBankChain w k) (1 - (r : ℝ)) →
                      AffineMap.lineMap (Q.projectedVertex (R.completedBankChain w j).val)
                        (Q.projectedVertex (R.spanningCompletion.parents.parent
                          (R.completedBankChain w j).val)) (s : ℝ) =
                      AffineMap.lineMap (Q.projectedVertex (R.completedBankChain w k).val)
                        (Q.projectedVertex (R.spanningCompletion.parents.parent
                          (R.completedBankChain w k).val)) (r : ℝ) := by
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
  refine fun D w member => ?_
  obtain ⟨B⟩ := frames D
  obtain ⟨i, sectors⟩ := M.cornerExtendedOutward_bankChain_sectors positive small T internal
    source_height lower conforming height w member
  exact B.chain_contact_same_projected_point i (R.completedBankChain w)
    (R.completedBankChain_parent w)
    (fun j => (sectors j).2) (fun j => (sectors j).1) budget

end Unfoldings.ConvexCap
