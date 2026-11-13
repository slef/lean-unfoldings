module

public import Unfoldings.Roof.CompletionPathWedges
public import Unfoldings.Cap.CompletedSectorQuadrants

/-! One mesh-independent tilt budget controls actual directions throughout the completed roof. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof

universe u v

/-- Choose the tolerance before either mesh. The original acute forest supplies the curved-path
wedges; arbitrary auxiliary and flat subdivision triangles consume no extra angle hypothesis. -/
theorem exists_uniform_completion_fiveSectorFrameData
    (t : ℝ) (positive : 0 < t) (small : t < 1) :
    ∃ φ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), (3 : ℝ) / 4 ≤ Real.cos φ ∧
      ∀ {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexRoof C),
        K.TiltBound φ → ∀ {origin : Plane} (M : K.SectorForest t origin)
          {region : Set Plane} {J : Type u} {extra : J → Plane →ᵃ[ℝ] ℝ}
          (E : K.CompletionMesh φ region extra),
          let L := E.radialMesh M.inside
          letI := @Fintype.ofFinite _ L.mesh.finite
          let R := (M.completionOutwardForest E positive small).val
          L.mesh.toTriangulation.pairedComplex.totalInteriorAngularDefect Set.univ < Real.pi ∧
            ∀ D : FacewiseDevelopment L.mesh.toTriangulation.pairedComplex R.completedRetain,
              Nonempty (R.FiveSectorFrameData positive small D) := by
  obtain ⟨φ, bounds, normal, construct⟩ :=
    ConvexCap.exists_uniform_completed_fiveSectorFrameData.{0, 0} t positive small
  refine ⟨φ, bounds, normal, ?_⟩
  intro Face _ C K tilt origin M region J extra E
  let L := E.radialMesh M.inside
  let := @Fintype.ofFinite _ L.mesh.finite
  let R := (M.completionOutwardForest E positive small).val
  have height (i) : (3 : ℝ) / 4 ≤
      (K.completionPlanes E.tentHeight (Real.sin φ / 2) i).normal 2 :=
    normal.trans (K.completionPlanes_tilt bounds.1 bounds.2 tilt E.tentHeight i)
  exact construct L.cap (CompletionMesh.cap_tilt bounds.1 bounds.2 tilt) origin
    (M.extendedGeometricCuts (E.cornerTails M.inside)) R
    (M.completionOutward_curvedPathWedges E positive small height)

end Unfoldings.ConvexRoof
