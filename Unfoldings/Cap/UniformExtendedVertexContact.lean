module

public import Unfoldings.Cap.UniformExtendedClosedContact
public import Unfoldings.Cap.ClosedFaceVertexContact

/-! Uniform physical identification of all nonvertex contacts, with no radius exclusions. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap

universe u v

theorem exists_uniform_extended_vertex_contact_reduction
    (t : ℝ) (positive : 0 < t) (small : t < 1) :
    ∃ ε ∈ Set.Ioc (0 : ℝ) (1 / 8), ∃ φ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), (3 : ℝ) / 4 ≤ Real.cos φ ∧
      ∀ {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexCap C),
        K.TiltBound φ → ∀ {origin : C.Vertex Set.univ} (M : K.SectorForest t origin),
          ∀ (internal : ¬ C.IsBoundaryVertex Set.univ origin)
            (source_height : 0 < K.roofHeight (K.projectedVertex origin))
            {Z : ℝ} (lower : Z < 0) (T : K.ClipSpatialTriangles Z),
              TriangleFamily.Conforming T.projectedTriangle →
                ∀ cutoff : ℝ, 0 < cutoff → Metric.closedBall (K.projectedVertex origin) cutoff ⊆
                  interior (K.clipFootprint Z) →
                let inside := (K.projectedVertex_mem_interior_iff origin).mpr internal
                let F := T.cornerTails inside source_height lower
                let L := F.mesh T lower
                let Q := L.partition.normalizedCap L.conforming lower
                letI := @Fintype.ofFinite _ L.partition.finite
                let R := (M.cornerExtendedOutwardForest positive small T
                  internal source_height lower).val
                ∀ D : FacewiseDevelopment L.partition.pairedComplex R.retain,
                  ∀ f g (p q : Plane),
                    p ∈ (Q.projectedTriangle f).carrier ∩
                      Metric.ball (K.projectedVertex origin) (ε * (cutoff / 16)) →
                    q ∈ (Q.projectedTriangle g).carrier ∩
                      Metric.ball (K.projectedVertex origin) (ε * (cutoff / 16)) →
                    D.projectedPlacement Q f p = D.projectedPlacement Q g q →
                      p = q ∨ (Q.projectedTriangle f).IsVertex p ∨
                        (Q.projectedTriangle g).IsVertex q := by
  classical
  obtain ⟨ε, εbounds, φ, φbounds, normal, construct⟩ :=
    exists_uniform_extended_closed_contact.{u, v} t positive small
  refine ⟨ε, εbounds, φ, φbounds, normal, ?_⟩
  intro Face _ C K tilt origin M internal source_height Z lower T conforming cutoff
    cutoff_positive deep
  let inside := (K.projectedVertex_mem_interior_iff origin).mpr internal
  let F := T.cornerTails inside source_height lower
  let L := F.mesh T lower
  let Q := L.partition.normalizedCap L.conforming lower
  let := @Fintype.ofFinite _ L.partition.finite
  let R := (M.cornerExtendedOutwardForest positive small T internal source_height lower).val
  change ∀ D : FacewiseDevelopment L.partition.pairedComplex R.retain,
    ∀ f g (p q : Plane),
      p ∈ (Q.projectedTriangle f).carrier ∩
        Metric.ball (K.projectedVertex origin) (ε * (cutoff / 16)) →
      q ∈ (Q.projectedTriangle g).carrier ∩
        Metric.ball (K.projectedVertex origin) (ε * (cutoff / 16)) →
      D.projectedPlacement Q f p = D.projectedPlacement Q g q →
        p = q ∨ (Q.projectedTriangle f).IsVertex p ∨ (Q.projectedTriangle g).IsVertex q
  intro D f g p q first last same
  by_cases equal : p = q
  · exact Or.inl equal
  obtain ⟨exception, finite, contacts⟩ := construct K tilt M internal source_height lower T
    conforming cutoff cutoff_positive deep D
  exact Or.inr (D.isVertex_or_isVertex_of_foreign_projected_contact Q Metric.isOpen_ball
    (convex_ball _ _) (D.projectedMap Q (K.projectedVertex origin)) finite contacts
    f g first last equal same)

end Unfoldings.ConvexCap
