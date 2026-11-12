module

public import Unfoldings.Cap.LocalClosedFaceSeparation
public import Unfoldings.Development.RegularInteriorContact

/-! Local roof separation excludes foreign contacts at regular locally isometric points. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FacewiseDevelopment

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {retain : Set C.Seam} (D : FacewiseDevelopment C retain) (K : ConvexCap C)

/-- Local separation suffices to identify an intrinsic copy at a face-interior contact. -/
theorem eq_faceMap_of_local_interior_contact {U : Set Plane} (opened : IsOpen U)
    (separate : Pairwise (fun f g => Disjoint
      (D.projectedPlacement K f '' (interior (K.projectedTriangle f).carrier ∩ U))
      (D.projectedPlacement K g '' (interior (K.projectedTriangle g).carrier ∩ U))))
    (f : Face) (z : C.Cell f) (inside : z.val ∈ interior (C.triangle f).carrier)
    (in_region : K.projectFace f z.val ∈ U)
    (y : C.Realization retain)
    (y_region : Cap.horizontal (K.folding.toSpace retain y) ∈ U)
    (same : D.toPlane y = D.place f z.val) : y = C.faceMap retain f z := by
  obtain ⟨⟨g, a⟩, rfl⟩ := MetricGluing.point_surjective C.Cell (C.glue retain) y
  change D.place g a.val = D.place f z.val at same
  have projected_inside : K.projectFace f z.val ∈ interior (K.projectedTriangle f).carrier := by
    have carrier : (K.projectedTriangle f).carrier =
        K.projectFaceHomeomorph f '' (C.triangle f).carrier :=
      (C.triangle f).affineImage_carrier _ _
    rw [carrier, ← Homeomorph.image_interior]
    exact ⟨z.val, inside, rfl⟩
  have projected_member : K.projectFace g a.val ∈ (K.projectedTriangle g).carrier := by
    rw [ConvexCap.projectedTriangle, Triangle.affineImage_carrier]
    exact ⟨a.val, a.property, rfl⟩
  have contact := D.projected_points_eq_of_interior_contact K opened separate
    ⟨projected_inside, in_region⟩ ⟨projected_member, y_region⟩
    (by simpa only [D.projectedPlacement_apply] using same.symm)
  obtain ⟨rfl, physical⟩ := contact
  have coordinates : z = a := Subtype.ext (K.projectFace_injective f physical)
  exact congrArg (C.faceMap retain f) coordinates.symm

/-- The auxiliary roof only needs separation in an open region containing both copies. -/
theorem eq_of_local_contact_at_regular_local_isometry
    [PreconnectedSpace (C.Realization retain)] {U : Set Plane} (opened : IsOpen U)
    (separate : Pairwise (fun f g => Disjoint
      (D.projectedPlacement K f '' (interior (K.projectedTriangle f).carrier ∩ U))
      (D.projectedPlacement K g '' (interior (K.projectedTriangle g).carrier ∩ U))))
    (x : C.Realization retain) (regular : C.IsRegularPoint retain x)
    (x_region : Cap.horizontal (K.folding.toSpace retain x) ∈ U)
    (local_isometry : ∃ r > 0,
      Isometry (fun y : Metric.eball x (ENNReal.ofReal r) => D.toPlane y.val))
    (y : C.Realization retain)
    (y_region : Cap.horizontal (K.folding.toSpace retain y) ∈ U)
    (same : D.toPlane y = D.toPlane x) : x = y := by
  let : MetricSpace (C.Realization retain) := EMetricSpace.toMetricSpace
    (fun a b => edist_ne_top_of_preconnected a b)
  let projection := fun a : C.Realization retain => Cap.horizontal (K.folding.toSpace retain a)
  have projection_continuous : Continuous projection :=
    Cap.horizontalCLM.continuous.comp (K.folding.toSpace_lipschitz retain).continuous
  have region_open : IsOpen (projection ⁻¹' U) := opened.preimage projection_continuous
  have local_ball : ∃ r > 0, Isometry (fun y : Metric.ball x r => D.toPlane y.val) := by
    obtain ⟨r, positive, isometry⟩ := local_isometry
    let lift (y : Metric.ball x r) : Metric.eball x (ENNReal.ofReal r) := ⟨y.val, by
      change edist y.val x < ENNReal.ofReal r
      rw [edist_dist]
      exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg dist_nonneg).mpr y.property⟩
    refine ⟨r, positive, ?_⟩
    intro p q
    have equal := isometry (lift p) (lift q)
    exact equal
  obtain ⟨⟨g, z⟩, rfl⟩ := MetricGluing.point_surjective C.Cell (C.glue retain) y
  change K.projectFace g z.val ∈ U at y_region
  change D.place g z.val = D.toPlane x at same
  have face_open : IsOpen ((K.projectFace g) ⁻¹' U) :=
    opened.preimage (K.projectFace g).continuous_of_finiteDimensional
  obtain ⟨δ, δpositive, δinside⟩ := Metric.isOpen_iff.mp face_open z.val y_region
  apply eq_of_forall_dist_le
  intro ε positive
  let V := Metric.ball x (ε / 2) ∩ projection ⁻¹' U
  have Vopen : IsOpen V := Metric.isOpen_ball.inter region_open
  have center : x ∈ V := ⟨Metric.mem_ball_self (half_pos positive), x_region⟩
  obtain ⟨r, rpositive, in_region, image⟩ :=
    regular.local_isometry_ball_image D.toPlane local_ball Vopen center
  obtain ⟨q, qinside, close, _different⟩ := (C.triangle g).exists_near_interior_ne z.property
    (lt_min rpositive (lt_min δpositive (half_pos positive)))
  let a : C.Cell g := ⟨q, interior_subset qinside⟩
  have q_region : K.projectFace g q ∈ U :=
    δinside (show q ∈ Metric.ball z.val δ from close.trans_le
      ((min_le_right _ _).trans (min_le_left _ _)))
  have image_close : D.place g q ∈ Metric.ball (D.toPlane x) r := by
    rw [Metric.mem_ball, ← same, (D.place g).isometry.dist_eq]
    exact close.trans_le (min_le_left _ _)
  obtain ⟨w, near, at_w⟩ := image.symm.subset image_close
  have actual : w = C.faceMap retain g a := D.eq_faceMap_of_local_interior_contact K opened
    separate g a qinside q_region w (in_region near).2 at_w
  have first_close : dist x (C.faceMap retain g a) < ε / 2 := by
    have near' := (in_region near).1
    rw [actual] at near'
    simpa only [Metric.mem_ball, dist_comm] using near'
  have last_close : dist (C.faceMap retain g a) (C.faceMap retain g z) < ε / 2 := by
    rw [(D.faceMap_isometry g).dist_eq]
    exact close.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have estimate := dist_triangle x (C.faceMap retain g a) (C.faceMap retain g z)
  change dist x (C.faceMap retain g z) ≤ ε
  linarith

end Unfoldings.FacewiseDevelopment
