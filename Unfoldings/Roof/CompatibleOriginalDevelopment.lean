module

public import Unfoldings.Roof.CompatibleOriginalSeamLift
public import Unfoldings.Roof.FaceRestriction
public import Unfoldings.Development.RestoreSeams
public import Unfoldings.Geometry.ConvexInteriorRigidity

/-! The whole roof layout induces rigid nonoverlapping placements of original faces. -/

@[expose] public section

noncomputable section

open scoped ENNReal

namespace Unfoldings.ConvexRoof

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexRoof C)
  {slopes : Set Plane} (compact : IsCompact slopes) (nonempty : slopes.Nonempty)
  {boundary : (frontier slopes).Nonempty} {a β : ℝ}
  (R : K.CompatiblePotentialRouting {f | K.normalSlope f ∈ slopes}
    (K.clippedExtension slopes compact nonempty) boundary a β)
  (no_boundary : ∀ f, K.normalSlope f ∉ frontier slopes)

variable (M : (K.clippedExtension slopes compact nonempty).FiniteSlopeModel)
  (W : R.WholeCutModel M)

local instance originalDevelopmentIndexFintype : Fintype W.Index := W.finiteIndex

include no_boundary

open Classical in
set_option maxHeartbeats 1600000 in
-- Elaborate original and restricted face and edge coordinates together.
/-- An off-cut locally isometric layout that retains the original spatial labels
gives a nonoverlapping development of the selected input faces with the original retained seams. -/
theorem exists_original_development_of_compatible_roof_layout
    (U : Set Face) (selected : U ⊆ {f | K.normalSlope f ∈ slopes})
    (layout : W.Cut → Plane) (continuous_layout : Continuous layout)
    (faithful : ∀ x y, layout x = layout y →
      (W.partition.restoreCut R.carrier x).val = (W.partition.restoreCut R.carrier y).val)
    (local_layout : ∀ x : W.Cut, Cap.horizontal (W.partition.restoreCut R.carrier x).val ∉
      R.carrier → ∃ r > 0, Isometry (fun y : Metric.eball x (ENNReal.ofReal r) => layout y.val)) :
    ∃ D : FacewiseDevelopment (C.restrictFaces U)
      (C.restrictRetain U (C.selectedRetain R.original.selection)), D.Nonoverlapping := by
  classical
  let F := K.folding.restrictFaces U
  have copies (f : U) := K.exists_compatible_original_face_lift compact nonempty R no_boundary M W
    f.val (selected f.property)
  choose lift ig agrees using copies
  have motions (f : U) : ∃ A : Plane ≃ᵃⁱ[ℝ] Plane,
      ∀ x : C.Cell f.val, layout (lift f x) = A x.val := by
    apply exists_rigid_motion_of_interior_local_isometry (C.triangle f.val).convex_carrier
      (C.triangle f.val).interior_nonempty (layout ∘ lift f)
      (continuous_layout.comp (ig f).continuous)
    intro x
    let q : C.Cell f.val := ⟨x.val, interior_subset x.property⟩
    have outside : Cap.horizontal (W.partition.restoreCut R.carrier (lift f q)).val ∉
        R.carrier := by
      rw [agrees f q]
      apply K.compatibleCarrier_avoids_original_face_interior compact nonempty R no_boundary
        f.val (selected f.property)
      have hc : (K.projectFaceHomeomorph f.val) '' (C.triangle f.val).carrier =
          (K.projectedTriangle f.val).carrier :=
        ((C.triangle f.val).affineImage_carrier _ (K.projectFace_injective f.val)).symm
      rw [← hc, ← Homeomorph.image_interior]
      exact ⟨x.val, x.property, rfl⟩
    obtain ⟨r, pos, local_iso⟩ := local_layout (lift f q) outside
    let j (y : Metric.ball x r) : Metric.eball (lift f q) (ENNReal.ofReal r) :=
      ⟨lift f ⟨y.val.val, interior_subset y.val.property⟩, by
        change edist (lift f _) (lift f q) < ENNReal.ofReal r
        rw [(ig f).edist_eq]
        change edist y.val x < ENNReal.ofReal r
        rw [edist_dist]
        exact ENNReal.ofReal_lt_ofReal_iff_of_nonneg dist_nonneg |>.mpr y.property⟩
    refine ⟨r, pos, ?_⟩
    intro y z
    have equality := local_iso.edist_eq (j y) (j z)
    change edist (layout (lift f ⟨y.val.val, interior_subset y.val.property⟩))
      (layout (lift f ⟨z.val.val, interior_subset z.val.property⟩)) =
        edist (lift f ⟨y.val.val, interior_subset y.val.property⟩)
          (lift f ⟨z.val.val, interior_subset z.val.property⟩) at equality
    exact equality.trans ((ig f).edist_eq _ _)
  choose place actual using motions
  have disjoint (f g : U) (different : f ≠ g) :
      Disjoint (interior (place f '' (C.triangle f.val).carrier))
        (interior (place g '' (C.triangle g.val).carrier)) := by
    change Disjoint (interior ((place f).toHomeomorph '' (C.triangle f.val).carrier))
      (interior ((place g).toHomeomorph '' (C.triangle g.val).carrier))
    rw [← Homeomorph.image_interior, ← Homeomorph.image_interior]
    apply Set.disjoint_left.mpr
    rintro p ⟨x, hx, at_p⟩ ⟨y, hy, also⟩
    let a : C.Cell f.val := ⟨x, interior_subset hx⟩
    let b : C.Cell g.val := ⟨y, interior_subset hy⟩
    have labels := faithful (lift f a) (lift g b)
      ((actual f a).trans (at_p.trans (also.symm.trans (actual g b).symm)))
    rw [agrees, agrees] at labels
    have cut_eq : C.faceMap Set.univ f.val a = C.faceMap Set.univ g.val b :=
      K.projection_injective (congrArg Cap.horizontal labels)
    have same := C.eq_of_related_interior hx ((C.faceMap_eq_iff Set.univ f.val g.val a b).mp cut_eq)
    exact different (Subtype.ext (congrArg Sigma.fst same))
  have joined (s : (C.restrictFaces U).Seam)
      (kept : s ∈ C.restrictRetain U (C.selectedRetain R.original.selection))
      (x : ((C.restrictFaces U).triangle ((C.restrictFaces U).left s).face).Edge
        ((C.restrictFaces U).left s).edge) :
      place ((C.restrictFaces U).left s).face x.val =
        place ((C.restrictFaces U).right s).face ((C.restrictFaces U).identify s x).val := by
    let f := (C.restrictFaces U).left s |>.face
    let g := (C.restrictFaces U).right s |>.face
    have glued := K.compatible_original_face_lifts_join compact nonempty R no_boundary M W
      s.val kept (selected f.property) (lift f) (lift g) (ig f).continuous (ig g).continuous
      (agrees f) (agrees g) x
    exact (actual f _).symm.trans ((congrArg layout glued).trans (actual g _))
  let retain := C.restrictRetain U (C.selectedRetain R.original.selection)
  let dev : FacewiseDevelopment (C.restrictFaces U) retain :=
    { place := place
      joined := joined
      opposite := fun s kept =>
        ((C.restrictFaces U).triangle ((C.restrictFaces U).left s).face).placed_opposite_of_disjoint
          ((C.restrictFaces U).triangle ((C.restrictFaces U).right s).face)
          ((C.restrictFaces U).left s).edge ((C.restrictFaces U).right s).edge
          ((C.restrictFaces U).identify s) (place _) (place _) (joined s kept)
          (disjoint _ _ (F.incident_faces_ne s)) }
  exact ⟨dev, disjoint⟩

end Unfoldings.ConvexRoof
