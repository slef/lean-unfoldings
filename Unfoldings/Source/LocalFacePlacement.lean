module

public import Unfoldings.Source.ActualCut
public import Unfoldings.Source.FacePlacement

/-!
# Actual local rigid face placements at every retained point

Restrict a constructed source-isometry neighborhood to a face and extend
that convex patch rigidly. The patch has interior even when centered on a
face edge or a flat subdivision vertex. Its rigid motion agrees with all
actual shortest-path vectors to nearby points of that face.
-/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialFolding.ConvexBoundary

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {F : SpatialFolding C} (P : F.ConvexBoundary)

theorem exists_local_face_placement :
    letI := P.metricSpace
    ∀ {source : C.Realization Set.univ} (R : SourceFrame source) (f : Face) (x : C.Cell f),
      C.faceMap Set.univ f x ∉ sourceCutLocus source →
        ∃ r > 0, ∃ A : Plane ≃ᵃⁱ[ℝ] Plane, ∀ y : C.Cell f, dist y.val x.val < r →
          C.faceMap Set.univ f y ∉ sourceCutLocus source ∧
          ∀ p : SourcePath source, p.target = C.faceMap Set.univ f y →
            R.coordinate p.path p.geodesic = A y.val := by
  let := P.metricSpace
  intro source R f x outside
  let exists_paths := P.sourcePath_target_surjective source
  obtain ⟨S, open_S, at_x, isometry⟩ := P.source_coordinates_local_isometry R ⟨_, outside⟩
  have open_image : IsOpen (Subtype.val '' S) :=
    (isClosed_sourceCutLocus source).isOpen_compl.isOpenMap_subtype_val S open_S
  have face_open := open_image.preimage (C.faceMap_lipschitz Set.univ f).continuous
  have member : x ∈ (C.faceMap Set.univ f) ⁻¹' (Subtype.val '' S) :=
    ⟨⟨C.faceMap Set.univ f x, outside⟩, at_x, rfl⟩
  obtain ⟨r, positive, included⟩ := Metric.isOpen_iff.mp face_open x member
  let s := (C.triangle f).carrier ∩ Metric.ball x.val r
  let point (z : s) : C.Cell f := ⟨z.val, z.property.1⟩
  have covered (z : s) : ∃ q : S, q.val.val = C.faceMap Set.univ f (point z) := by
    have near_point : point z ∈ Metric.ball x r := z.property.2
    have image_member : C.faceMap Set.univ f (point z) ∈ Subtype.val '' S :=
      included near_point
    obtain ⟨q, in_S, equal⟩ := image_member
    exact ⟨⟨q, in_S⟩, equal⟩
  choose lift image using covered
  have lift_isometry : Isometry lift := by
    intro a b
    change edist (lift a).val.val (lift b).val.val = edist a.val b.val
    rw [image, image]
    exact F.faceMap_isometry Set.univ f (point a) (point b)
  have convex_s : Convex ℝ s := (C.triangle f).convex_carrier.inter (convex_ball _ _)
  have closure_interior : closure (interior (C.triangle f).carrier) = (C.triangle f).carrier :=
    ((C.triangle f).convex_carrier.closure_interior_eq_closure_of_nonempty_interior
      (C.triangle f).interior_nonempty).trans (C.triangle f).compact_carrier.isClosed.closure_eq
  have near_interior : x.val ∈ closure (interior (C.triangle f).carrier) :=
    closure_interior.symm ▸ x.property
  obtain ⟨z, in_interior, close⟩ := Metric.mem_closure_iff.mp near_interior r positive
  have interior_s : (interior s).Nonempty := by
    refine ⟨z, ?_⟩
    rw [interior_inter, Metric.isOpen_ball.interior_eq]
    exact ⟨in_interior, by simpa only [Metric.mem_ball, dist_comm] using close⟩
  obtain ⟨A, agrees⟩ := exists_rigid_extension_convex convex_s interior_s
    ((fun q : S => R.coordinatesOffCutLocus exists_paths q.val) ∘ lift)
    (isometry.comp lift_isometry)
  refine ⟨r, positive, A, ?_⟩
  intro y near_y
  let z : s := ⟨y.val, y.property, near_y⟩
  have off_cut : C.faceMap Set.univ f y ∉ sourceCutLocus source :=
    (image z) ▸ (lift z).val.property
  refine ⟨off_cut, ?_⟩
  intro p target
  have off_target : p.target ∉ sourceCutLocus source := target.symm ▸ off_cut
  have equal : (⟨p.target, off_target⟩ : ↥((sourceCutLocus source)ᶜ)) = (lift z).val :=
    Subtype.ext (target.trans (image z).symm)
  have coordinate := R.coordinate_of_sourcePath_off_cut exists_paths p off_target
  rw [equal] at coordinate
  exact coordinate.symm.trans (agrees z).symm

end Unfoldings.SpatialFolding.ConvexBoundary
