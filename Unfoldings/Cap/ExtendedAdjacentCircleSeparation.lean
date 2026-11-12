module

public import Unfoldings.Cap.ExtendedAdjacentCircleGeometry

/-! Uniformly construct actual adjacent-strip circle separation before both meshes. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap

universe u v

/-- The same constructed subdivision and radial trace family have disjoint adjacent
source-circle slices, apart from one proved finite vertex-radius set. Tilt and numerical
thresholds precede both meshes. All shared-prefix and actual tail hypotheses are derived. -/
theorem exists_uniform_extended_adjacent_circle_separation_with_pinches
    (t : ℝ) (positive : 0 < t) (small : t < 1) :
    ∃ ε ∈ Set.Ioc (0 : ℝ) (1 / 8), ∃ φ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), (3 : ℝ) / 4 ≤ Real.cos φ ∧
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
                let covered := T.cornerTails_covers_rim inside source_height lower
                let L := F.mesh T lower
                let Q := L.partition.normalizedCap L.conforming lower
                letI := @Fintype.ofFinite _ L.partition.finite
                let R := (M.cornerExtendedOutwardForest positive small T
                  internal source_height lower).val
                L.partition.pairedComplex.totalInteriorAngularDefect Set.univ < Real.pi ∧
                ∀ D : FacewiseDevelopment L.partition.pairedComplex R.retain,
                  ∃ bankFrame : R.FiveSectorFrameData positive small (R.completedDevelopment D),
                  let calibration := R.calibratedFrame (R.completedDevelopment D)
                    bankFrame.anchor bankFrame.reference
                  (∀ (frame : Plane ≃ₗᵢ[ℝ] ℂ) f z,
                    ‖(D.coordinatePlacement Q calibration frame f).linear z - z‖ ≤ ε * ‖z‖) ∧
                  ∀ i : FiveSector,
                    ∃ P : (fiveSectorFrame t positive small i).enclosingStrip.Subdivision,
                      (∀ G ∈ P.separators,
                        ∃ leaf : M.GeometricSectorLeaf F covered positive small lower i,
                          leaf.point.re + leaf.point.im ≤ cutoff ∧
                            MonotoneStrip.CompletesTail leaf.point leaf.tailGraph.graph cutoff G) ∧
                      (∀ leaf : M.GeometricSectorLeaf F covered positive small lower i,
                        leaf.point.re + leaf.point.im ≤ cutoff →
                          ∃ G ∈ P.separators,
                            MonotoneStrip.CompletesTail leaf.point leaf.tailGraph.graph cutoff G) ∧
                      (∀ S ∈ P.cells, S.lower.StrictCoordinatesOn (Set.Icc 0 cutoff) ∧
                        S.upper.StrictCoordinatesOn (Set.Icc 0 cutoff)) ∧
                      (∀ S ∈ P.cells, S.ApproachedPinchesIn
                        (Set.range (fun w : {w : L.partition.pairedComplex.Vertex Set.univ //
                          Q.projectedVertex w ∈ M.extendedGeometricCuts F} =>
                          (fiveSectorFrame t positive small i).place
                            (Q.projectedVertex w.val - K.projectedVertex origin))) 0 cutoff) ∧
                      ∃ traces : ∀ cell : {S : MonotoneStrip // S ∈ P.cells},
                        R.RadialStripTraceData positive small D calibration i cell.val ε cutoff,
                        ∀ first last : {S : MonotoneStrip // S ∈ P.cells},
                          first.val.upper = last.val.lower → first.val.upper ∈ P.separators →
                          ∀ radius ∈ Set.Ioo (0 : ℝ) (cutoff / 4),
                            radius ∉ D.fiveSectorVertexRadii Q (K.projectedVertex origin)
                              calibration positive small →
                            Disjoint
                              ((traces first).value '' first.val.openSlab 0 cutoff ∩
                                {z | ‖z - (traces first).center‖ = radius})
                              ((traces last).value '' last.val.openSlab 0 cutoff ∩
                                {z | ‖z - (traces last).center‖ = radius}) := by
  obtain ⟨ε, error_bounds, φ, bounds, normal, construct⟩ :=
    exists_uniform_extended_adjacent_circle_geometry.{u, v} t positive small
  refine ⟨ε, error_bounds, φ, bounds, normal, ?_⟩
  intro Face _ C K tilt origin M internal source_height Z lower T conforming cutoff deep
  let inside := (K.projectedVertex_mem_interior_iff origin).mpr internal
  let F := T.cornerTails inside source_height lower
  let L := F.mesh T lower
  let := @Fintype.ofFinite _ L.partition.finite
  obtain ⟨budget, frames⟩ :=
    construct K tilt M internal source_height lower T conforming cutoff deep
  refine ⟨budget, fun D => ?_⟩
  obtain ⟨B, error, _, sectors⟩ := frames D
  refine ⟨B, error, fun i => ?_⟩
  obtain ⟨P, provenance, represented, coordinates, pinches, traces, adjacent, _⟩ := sectors i
  exact ⟨P, provenance, represented, coordinates, pinches, traces, adjacent⟩

/-- Retain neighboring circle separation without the extra terminal-pinch output. -/
theorem exists_uniform_extended_adjacent_circle_separation
    (t : ℝ) (positive : 0 < t) (small : t < 1) :
    ∃ ε ∈ Set.Ioc (0 : ℝ) (1 / 8), ∃ φ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), (3 : ℝ) / 4 ≤ Real.cos φ ∧
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
                let covered := T.cornerTails_covers_rim inside source_height lower
                let L := F.mesh T lower
                let Q := L.partition.normalizedCap L.conforming lower
                letI := @Fintype.ofFinite _ L.partition.finite
                let R := (M.cornerExtendedOutwardForest positive small T
                  internal source_height lower).val
                L.partition.pairedComplex.totalInteriorAngularDefect Set.univ < Real.pi ∧
                ∀ D : FacewiseDevelopment L.partition.pairedComplex R.retain,
                  ∃ bankFrame : R.FiveSectorFrameData positive small (R.completedDevelopment D),
                  let calibration := R.calibratedFrame (R.completedDevelopment D)
                    bankFrame.anchor bankFrame.reference
                  (∀ (frame : Plane ≃ₗᵢ[ℝ] ℂ) f z,
                    ‖(D.coordinatePlacement Q calibration frame f).linear z - z‖ ≤ ε * ‖z‖) ∧
                  ∀ i : FiveSector,
                    ∃ P : (fiveSectorFrame t positive small i).enclosingStrip.Subdivision,
                      (∀ G ∈ P.separators,
                        ∃ leaf : M.GeometricSectorLeaf F covered positive small lower i,
                          leaf.point.re + leaf.point.im ≤ cutoff ∧
                            MonotoneStrip.CompletesTail leaf.point leaf.tailGraph.graph cutoff G) ∧
                      (∀ leaf : M.GeometricSectorLeaf F covered positive small lower i,
                        leaf.point.re + leaf.point.im ≤ cutoff →
                          ∃ G ∈ P.separators,
                            MonotoneStrip.CompletesTail leaf.point leaf.tailGraph.graph cutoff G) ∧
                      (∀ S ∈ P.cells, S.lower.StrictCoordinatesOn (Set.Icc 0 cutoff) ∧
                        S.upper.StrictCoordinatesOn (Set.Icc 0 cutoff)) ∧
                      ∃ traces : ∀ cell : {S : MonotoneStrip // S ∈ P.cells},
                        R.RadialStripTraceData positive small D calibration i cell.val ε cutoff,
                        ∀ first last : {S : MonotoneStrip // S ∈ P.cells},
                          first.val.upper = last.val.lower → first.val.upper ∈ P.separators →
                          ∀ radius ∈ Set.Ioo (0 : ℝ) (cutoff / 4),
                            radius ∉ D.fiveSectorVertexRadii Q (K.projectedVertex origin)
                              calibration positive small →
                            Disjoint
                              ((traces first).value '' first.val.openSlab 0 cutoff ∩
                                {z | ‖z - (traces first).center‖ = radius})
                              ((traces last).value '' last.val.openSlab 0 cutoff ∩
                                {z | ‖z - (traces last).center‖ = radius}) := by
  obtain ⟨ε, error_bounds, φ, bounds, normal, construct⟩ :=
    exists_uniform_extended_adjacent_circle_separation_with_pinches.{u, v} t positive small
  refine ⟨ε, error_bounds, φ, bounds, normal, ?_⟩
  intro Face _ C K tilt origin M internal source_height Z lower T conforming cutoff deep
  let inside := (K.projectedVertex_mem_interior_iff origin).mpr internal
  let F := T.cornerTails inside source_height lower
  let L := F.mesh T lower
  let := @Fintype.ofFinite _ L.partition.finite
  obtain ⟨budget, frames⟩ :=
    construct K tilt M internal source_height lower T conforming cutoff deep
  refine ⟨budget, fun D => ?_⟩
  obtain ⟨B, error, sectors⟩ := frames D
  refine ⟨B, error, fun i => ?_⟩
  obtain ⟨P, provenance, represented, coordinates, _, traces⟩ := sectors i
  exact ⟨P, provenance, represented, coordinates, traces⟩

end Unfoldings.ConvexCap
