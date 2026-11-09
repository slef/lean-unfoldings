module

public import Unfoldings.Source.FiniteMotions

/-!
# A finite rigid face-piece cover of the whole completed source disk

Each candidate rigid motion and original face gives a compact graph in the
product of the plane and the original surface. The actual retained graph is
covered by finitely many such graphs. Closedness and density extend this
cover to every completion point, retaining the endpoint projection and all
distinct shortest-path copies. The pieces are not yet asserted polygonal.
-/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialFolding.ConvexBoundary

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {F : SpatialFolding C} (P : F.ConvexBoundary)

theorem exists_finite_completed_face_pieces :
    letI := P.metricSpace
    ∀ {source : C.Realization Set.univ} (R : SourceFrame source),
      ∃ M : Set (Plane ≃ᵃⁱ[ℝ] Plane), M.Finite ∧ ∀ z : R.domain,
        ∃ A ∈ M, ∃ f : Face, ∃ y : C.Cell f,
          z.val = A y.val ∧ R.projection (P.sourcePathCoordinate_injective R) z =
            C.faceMap Set.univ f y := by
  let := P.metricSpace
  intro source R
  obtain ⟨M, finite, covers⟩ := P.exists_finite_actual_source_motions R
  let graph (A : Plane ≃ᵃⁱ[ℝ] Plane) (f : Face) :
      Set (Plane × C.Realization Set.univ) :=
    Set.range (fun y : C.Cell f => (A y.val, C.faceMap Set.univ f y))
  have closed_graph (A : Plane ≃ᵃⁱ[ℝ] Plane) (f : Face) : IsClosed (graph A f) :=
    (isCompact_range ((A.continuous.comp continuous_subtype_val).prodMk
      (C.faceMap_lipschitz Set.univ f).continuous)).isClosed
  let G := ⋃ A ∈ M, ⋃ f : Face, graph A f
  have closed_G : IsClosed G := finite.isClosed_biUnion
    (fun A _ => isClosed_iUnion_of_finite (closed_graph A))
  let map (z : R.domain) := (z.val, R.projection (P.sourcePathCoordinate_injective R) z)
  have continuous_map : Continuous map := continuous_subtype_val.prodMk
    (R.continuous_projection (P.sourcePathCoordinate_injective R))
  have interior_covered (w : interior R.domain) :
      map (Set.inclusion interior_subset w) ∈ G := by
    let z : R.domain := ⟨w.val, interior_subset w.property⟩
    let H := P.sourceDomainHomeomorph R
    let p := H.symm z
    have vector : R.coordinate p.path p.geodesic = w.val :=
      congrArg Subtype.val (H.apply_symm_apply z)
    have outside : p.target ∉ sourceCutLocus source :=
      (P.source_vector_mem_interior_iff_off_cut R p).mp (vector.symm ▸ w.property)
    obtain ⟨⟨f, y⟩, target⟩ := MetricGluing.point_surjective C.Cell (C.glue Set.univ) p.target
    have y_outside : C.faceMap Set.univ f y ∉ sourceCutLocus source := by
      change MetricGluing.point C.Cell (C.glue Set.univ) ⟨f, y⟩ ∉ sourceCutLocus source
      rw [target]
      exact outside
    let A := P.sourceTaggedMotion R ⟨f, y⟩ y_outside
    have coordinate := R.coordinate_of_sourcePath_off_cut (P.sourcePath_target_surjective source)
      p outside
    have same : (⟨p.target, outside⟩ : ↥((sourceCutLocus source)ᶜ)) =
        ⟨C.faceMap Set.univ f y, y_outside⟩ := Subtype.ext target.symm
    rw [same] at coordinate
    have motion : R.coordinatesOffCutLocus (P.sourcePath_target_surjective source)
        ⟨C.faceMap Set.univ f y, y_outside⟩ = A y.val :=
      P.sourceFaceCoordinates_eq_motion R f ⟨y, y_outside⟩
    have developed : w.val = A y.val := vector.symm.trans (coordinate.symm.trans motion)
    apply Set.mem_iUnion.mpr
    refine ⟨A, Set.mem_iUnion.mpr ⟨covers ⟨f, y⟩ y_outside, ?_⟩⟩
    exact Set.mem_iUnion.mpr ⟨f, y, Prod.ext developed.symm target⟩
  have dense : DenseRange
      (Set.inclusion (show interior R.domain ⊆ R.domain from interior_subset)) := by
    apply (denseRange_inclusion_iff (show interior R.domain ⊆ R.domain from interior_subset)).mpr
    rw [P.sourceDomain_closure_interior R]
  have all_covered (z : R.domain) : map z ∈ G :=
    dense.induction_on z (closed_G.preimage continuous_map) interior_covered
  refine ⟨M, finite, ?_⟩
  intro z
  obtain ⟨A, in_A⟩ := Set.mem_iUnion.mp (all_covered z)
  obtain ⟨member, in_face⟩ := Set.mem_iUnion.mp in_A
  obtain ⟨f, in_graph⟩ := Set.mem_iUnion.mp in_face
  obtain ⟨y, equal⟩ := in_graph
  exact ⟨A, member, f, y, (congrArg Prod.fst equal).symm, (congrArg Prod.snd equal).symm⟩

end Unfoldings.SpatialFolding.ConvexBoundary
