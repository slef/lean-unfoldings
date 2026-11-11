module

public import Unfoldings.Cap.CompletedCalibratedThreshold
public import Unfoldings.Cap.ExtendedPathWedges

/-! Uniform actual developed direction control for the constructed finite roof extension. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap

universe u v

/-- The threshold precedes the original cap, source forest, clipping height, and every auxiliary
face and vertex. Actual curvature-carrying path wedges are constructed, and the auxiliary mesh
is not required to be acute. This is direction control, not a global nonoverlap theorem. -/
theorem exists_uniform_extended_direction_control {ε : ℝ} (positive : 0 < ε) :
    ∃ φ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      ∀ {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexCap C),
        K.TiltBound φ → ∀ {t : ℝ} {origin : C.Vertex Set.univ} (M : K.SectorForest t origin),
          ∀ (tpos : 0 < t) (tsmall : t < 1) (internal : ¬ C.IsBoundaryVertex Set.univ origin)
            (source_height : 0 < K.roofHeight (K.projectedVertex origin))
            {Z : ℝ} (lower : Z < 0) (T : K.ClipSpatialTriangles Z),
              TriangleFamily.Conforming T.projectedTriangle →
                let inside := (K.projectedVertex_mem_interior_iff origin).mpr internal
                let F := T.cornerTails inside source_height lower
                let L := F.mesh T lower
                let Q := L.partition.normalizedCap L.conforming lower
                letI := @Fintype.ofFinite _ L.partition.finite
                let R := (M.cornerExtendedOutwardForest tpos tsmall T
                  internal source_height lower).val
                ∀ D : FacewiseDevelopment L.partition.pairedComplex R.completedRetain,
                  ∃ A : Plane ≃ₗᵢ[ℝ] ℂ, ∀ f (direction : Plane), direction ≠ 0 →
                    InnerProductGeometry.angle (A (D.developedDirection Q f direction))
                      (Complex.orthonormalBasisOneI.repr.symm direction) < ε := by
  obtain ⟨φ, bounds, normal, control⟩ :=
    exists_uniform_completed_direction_control.{0, 0} positive
  refine ⟨φ, bounds, ?_⟩
  intro Face _ C K tilt t origin M tpos tsmall internal source_height Z lower T conforming
  let inside := (K.projectedVertex_mem_interior_iff origin).mpr internal
  let F := T.cornerTails inside source_height lower
  let L := F.mesh T lower
  let Q := L.partition.normalizedCap L.conforming lower
  let := @Fintype.ofFinite _ L.partition.finite
  let R := (M.cornerExtendedOutwardForest tpos tsmall T internal source_height lower).val
  have height : ∀ f, (3 : ℝ) / 4 ≤ K.normal f 2 := fun f => normal.trans (tilt f)
  have wedges := M.cornerExtendedOutward_curvedPathWedges tpos tsmall T internal source_height
    lower conforming height
  have roof_tilt : Q.TiltBound φ := L.partition.normalizedCap_tiltBound L.conforming lower tilt
  exact control Q roof_tilt (K.projectedVertex origin) (M.extendedGeometricCuts F) R wedges

end Unfoldings.ConvexCap
