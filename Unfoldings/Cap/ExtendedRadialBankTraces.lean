module

public import Unfoldings.Cap.ExtendedClosedRadialBankTraces

/-! Construct strictly radial actual bank traces with a tilt threshold preceding both meshes. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap

universe u v

/-- The actual bank-order calibration has strictly radial complete strip-bank traces.
Only cap geometry and the constructed forest are inputs; the threshold precedes both meshes. -/
theorem exists_uniform_extended_radial_bank_traces (t : ℝ) (positive : 0 < t) (small : t < 1)
    {ε : ℝ} (εpositive : 0 < ε) :
    ∃ φ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      ∀ {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexCap C),
        K.TiltBound φ → ∀ {origin : C.Vertex Set.univ} (M : K.SectorForest t origin),
          ∀ (internal : ¬ C.IsBoundaryVertex Set.univ origin)
            (source_height : 0 < K.roofHeight (K.projectedVertex origin))
            {Z : ℝ} (lower : Z < 0) (T : K.ClipSpatialTriangles Z),
              TriangleFamily.Conforming T.projectedTriangle →
                ∀ cutoff : ℝ, Metric.closedBall (K.projectedVertex origin) cutoff ⊆
                  interior (K.clipFootprint Z) →
                let inside := (K.projectedVertex_mem_interior_iff origin).mpr internal
                let F := T.cornerTails inside source_height lower
                let L := F.mesh T lower
                let Q := L.partition.normalizedCap L.conforming lower
                letI := @Fintype.ofFinite _ L.partition.finite
                let R := (M.cornerExtendedOutwardForest positive small T
                  internal source_height lower).val
                ∀ D : FacewiseDevelopment L.partition.pairedComplex R.retain,
                  ∃ bankFrame : R.FiveSectorFrameData positive small (R.completedDevelopment D),
                  let calibration := R.calibratedFrame (R.completedDevelopment D)
                    bankFrame.anchor bankFrame.reference
                  (∀ (frame : Plane ≃ₗᵢ[ℝ] ℂ) f z,
                    ‖(D.coordinatePlacement Q calibration frame f).linear z - z‖ ≤ ε * ‖z‖) ∧
                  ∀ i : FiveSector,
                    ∃ P : (fiveSectorFrame t positive small i).enclosingStrip.Subdivision,
                      ∀ S ∈ P.cells,
                        let frame := (fiveSectorFrame t positive small i).place
                        let domain := {z | z ∈ S.strictCarrier ∧ z.re + z.im ∈ Set.Icc 0 cutoff}
                        ∃ G : ℂ → ℂ, Continuous G ∧
                          Set.EqOn (D.centeredMap Q (K.projectedVertex origin)
                            calibration frame) G domain ∧
                          Set.InjOn (D.centeredMap Q (K.projectedVertex origin)
                            calibration frame) domain ∧
                          S.RadialBankTraces G
                            (D.centeredMap Q (K.projectedVertex origin) calibration frame 0)
                            cutoff ∧
                          R.MatchesParentBanks positive small i (R.completedDevelopment D)
                            calibration G S cutoff ∧
                          ∀ z ∈ S.strictCarrier, z.re + z.im ∈ Set.Icc 0 cutoff →
                            ‖(D.centeredMap Q (K.projectedVertex origin) calibration frame z -
                              D.centeredMap Q (K.projectedVertex origin) calibration frame 0) -
                              z‖ ≤ ε * (z.re + z.im) := by
  obtain ⟨φ, bounds, _, control⟩ :=
    exists_uniform_extended_closed_radial_bank_traces t positive small εpositive
  refine ⟨φ, bounds, ?_⟩
  intro Face _ C K tilt origin M internal source_height Z lower T conforming cutoff deep
  obtain ⟨_, banks⟩ := control K tilt M internal source_height lower T conforming cutoff deep
  refine fun D => ?_
  obtain ⟨bankFrame, linear, strips⟩ := banks D
  refine ⟨bankFrame, linear, fun i => ?_⟩
  obtain ⟨P, cells⟩ := strips i
  refine ⟨P, fun S cell => ?_⟩
  obtain ⟨G, continuous, equal, injective, _, radial, matched, error⟩ := cells S cell
  exact ⟨G, continuous, equal, injective, radial, matched, error⟩

end Unfoldings.ConvexCap
