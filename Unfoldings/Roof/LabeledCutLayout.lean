module

public import Unfoldings.Roof.FaceRestriction
public import Unfoldings.Complex.SubdivisionInteriors
public import Unfoldings.Development.RestoreSeams
public import Unfoldings.Geometry.ConvexInteriorRigidity
public import Unfoldings.Geometry.EdgeExt

/-! A complete cut layout transfers to literal placements of all original input faces. -/

@[expose] public section

noncomputable section

open scoped ENNReal

namespace Unfoldings.ConvexRoof

universe u v w

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  (K : ConvexRoof C) {X : Type w} [EMetricSpace X]

open Classical in
set_option maxHeartbeats 1700000 in
-- Elaborate the local charts and the two levels of face labels in the same proof.
/-- Labeled physical lifts and a continuous locally isometric layout off the
cuts induce a rigid nonoverlapping placement with exactly the requested seams. -/
theorem exists_development_of_labeled_cut_layout (U : Set Face)
    (retain : Set (C.restrictFaces U).Seam) (restore : X → Space) (cuts : Set Plane)
    (layout : X → Plane) (continuous_layout : Continuous layout)
    (faithful : ∀ x y, layout x = layout y → restore x = restore y)
    (unique : ∀ x y, restore x = restore y → Cap.horizontal (restore x) ∉ cuts → x = y)
    (local_layout : ∀ x, Cap.horizontal (restore x) ∉ cuts →
      ∃ r > 0, Isometry (fun y : Metric.eball x (ENNReal.ofReal r) => layout y.val))
    (copies : ∀ f : U, ∃ lift : C.Cell f.val → X, Isometry lift ∧
      ∀ x, restore (lift x) = K.folding.place f.val x.val)
    (interiors : ∀ f : U, ∀ x ∈ interior (C.triangle f.val).carrier,
      Cap.horizontal (K.folding.place f.val x) ∉ cuts)
    (seams : ∀ s ∈ retain, ∀ x : (C.triangle (C.left s.val).face).Edge (C.left s.val).edge,
      ¬ (C.triangle (C.left s.val).face).IsVertex x →
        Cap.horizontal (K.folding.place (C.left s.val).face x.val) ∉ cuts) :
    ∃ D : FacewiseDevelopment (C.restrictFaces U) retain, D.Nonoverlapping := by
  classical
  let F := K.folding.restrictFaces U
  choose lift ig agrees using copies
  have motions (f : U) : ∃ A : Plane ≃ᵃⁱ[ℝ] Plane,
      ∀ x : C.Cell f.val, layout (lift f x) = A x.val := by
    apply exists_rigid_motion_of_interior_local_isometry (C.triangle f.val).convex_carrier
      (C.triangle f.val).interior_nonempty (layout ∘ lift f)
      (continuous_layout.comp (ig f).continuous)
    intro x
    let q : C.Cell f.val := ⟨x.val, interior_subset x.property⟩
    have outside : Cap.horizontal (restore (lift f q)) ∉ cuts := by
      rw [agrees]
      exact interiors f x.val x.property
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
  have joined (s : (C.restrictFaces U).Seam) (kept : s ∈ retain)
      (x : ((C.restrictFaces U).triangle ((C.restrictFaces U).left s).face).Edge
        ((C.restrictFaces U).left s).edge) :
      place ((C.restrictFaces U).left s).face x.val =
        place ((C.restrictFaces U).right s).face ((C.restrictFaces U).identify s x).val := by
    let f := (C.restrictFaces U).left s |>.face
    let g := (C.restrictFaces U).right s |>.face
    let l := (C.triangle f.val).edgeMap (C.left s.val).edge
    let r := (C.triangle g.val).edgeMap (C.right s.val).edge
    have continuous_l : Continuous l := (show Isometry l from fun _ _ => rfl).continuous
    have continuous_r : Continuous r := (show Isometry r from fun _ _ => rfl).continuous
    have copies_join := (C.triangle f.val).edge_eq_of_nonvertex (C.left s.val).edge
      (lift f ∘ l) (lift g ∘ r ∘ C.identify s.val)
      ((ig f).continuous.comp continuous_l)
      ((ig g).continuous.comp (continuous_r.comp (C.identify s.val).continuous))
      (by
        intro y regular
        have equal := (agrees f (l y)).trans ((K.folding.joined s.val y).trans
          (agrees g (r (C.identify s.val y))).symm)
        have outside : Cap.horizontal (restore (lift f (l y))) ∉ cuts := by
          rw [agrees]
          exact seams s kept y regular
        exact unique _ _ equal outside)
    have glued := congrFun copies_join x
    exact (actual f _).symm.trans ((congrArg layout glued).trans (actual g _))
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
