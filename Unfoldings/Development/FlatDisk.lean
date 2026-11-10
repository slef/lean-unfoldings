module

public import Unfoldings.Development.FlatDiskInterior
public import Unfoldings.Development.Normalization
public import Unfoldings.Geometry.ConvexLocalRigidity
public import Unfoldings.Geometry.EdgeExt
public import Unfoldings.Complex.IntrinsicBoundary
public import Unfoldings.Complex.RelativeSeamGeometry
public import Unfoldings.Complex.SubdivisionInteriors

/-! A flat triangulated metric disk admits an outward facewise development, with overlap allowed. -/

@[expose] public section

open scoped ENNReal

noncomputable section

namespace Unfoldings.SpatialFolding

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (F : SpatialFolding C)

include F in
/-- Intrinsic regularity in the open disk suffices; boundary angles are unrestricted. -/
theorem exists_locally_isometric_development_of_regular_disk (retain : Set C.Seam)
    (disk : C.Realization retain ≃ₜ Metric.closedBall (0 : Plane) 1)
    (regular : ∀ x, ‖(disk x).val‖ < 1 → C.IsRegularPoint retain x) :
    ∃ E : FacewiseDevelopment C retain, ∀ x, ‖(disk x).val‖ < 1 → ∃ r > 0,
      Isometry (fun y : Metric.eball x (ENNReal.ofReal r) => E.toPlane y.val) := by
  let : ConnectedSpace (Metric.closedBall (0 : Plane) 1) :=
    isConnected_iff_connectedSpace.mp
      ((convex_closedBall (0 : Plane) 1).isConnected ⟨0, Metric.mem_closedBall_self zero_le_one⟩)
  let : ConnectedSpace (C.Realization retain) :=
    disk.symm.surjective.connectedSpace disk.symm.continuous
  let connected := C.duallyConnected_of_preconnected retain
  let := C.metricSpace retain connected
  let U := diskInterior disk
  have open_U : IsOpen U := isOpen_diskInterior disk
  obtain ⟨coordinates, local_isometry⟩ := exists_diskInterior_development disk regular
  have face_inside (f : Face) (x : C.Cell f) (inside : x.val ∈ interior (C.triangle f).carrier) :
      C.faceMap retain f x ∈ U :=
    (C.isRegularPoint_face retain f x inside).disk_image_norm_lt_one disk
  have motions (f : Face) : ∃ A : Plane ≃ᵃⁱ[ℝ] Plane, ∀ x : C.Cell f,
      ∀ member : C.faceMap retain f x ∈ U, coordinates ⟨C.faceMap retain f x, member⟩ = A x.val :=
    exists_rigid_motion_on_cell (C.triangle f).convex_carrier (C.triangle f).interior_nonempty
      (C.faceMap retain f) (F.faceMap_isometry retain f) U open_U coordinates local_isometry
      (face_inside f)
  choose place agrees using motions
  have seam_inside (s : C.Seam) (kept : s ∈ retain)
      (x : (C.triangle (C.left s).face).Edge (C.left s).edge)
      (nonvertex : ¬ (C.triangle (C.left s).face).IsVertex x) :
      C.faceMap retain (C.left s).face
        ((C.triangle (C.left s).face).edgeMap (C.left s).edge x) ∈ U := by
    have regular := C.isRegularPoint_hinge retain s kept (F.incident_faces_ne s) x nonvertex
    exact regular.disk_image_norm_lt_one disk
  have joined (s : C.Seam) (kept : s ∈ retain)
      (x : (C.triangle (C.left s).face).Edge (C.left s).edge) :
      place (C.left s).face x.val = place (C.right s).face (C.identify s x).val := by
    have equal := (C.triangle (C.left s).face).edge_eq_of_nonvertex (C.left s).edge
      (fun x => place (C.left s).face x.val)
      (fun x => place (C.right s).face (C.identify s x).val)
      ((place _).continuous.comp continuous_subtype_val)
      ((place _).continuous.comp (continuous_subtype_val.comp (C.identify s).continuous)) (by
        intro x nonvertex
        have left := seam_inside s kept x nonvertex
        have identified := C.seam_identified retain s kept x
        have right : C.faceMap retain (C.right s).face
            ((C.triangle (C.right s).face).edgeMap (C.right s).edge (C.identify s x)) ∈ U :=
          identified ▸ left
        exact (agrees _ _ left).symm.trans
          ((congrArg coordinates (Subtype.ext identified)).trans (agrees _ _ right)))
    exact congrFun equal x
  have separated (s : C.Seam) (kept : s ∈ retain) :
      Disjoint (interior (place (C.left s).face '' (C.triangle (C.left s).face).carrier))
        (interior (place (C.right s).face '' (C.triangle (C.right s).face).carrier)) := by
    apply Set.disjoint_left.mpr
    intro p first last
    obtain ⟨x, nonvertex⟩ := (C.triangle (C.left s).face).exists_edge_nonvertex (C.left s).edge
    let l := (C.triangle (C.left s).face).edgeMap (C.left s).edge x
    let r := (C.triangle (C.right s).face).edgeMap (C.right s).edge (C.identify s x)
    have identified : C.faceMap retain (C.left s).face l = C.faceMap retain (C.right s).face r :=
      C.seam_identified retain s kept x
    have left_in := seam_inside s kept x nonvertex
    let q : U := ⟨C.faceMap retain (C.left s).face l, left_in⟩
    obtain ⟨radius, positive, isometry⟩ := local_isometry q
    let L := place (C.left s).face
    let R := place (C.right s).face
    let A := L '' (C.triangle (C.left s).face).carrier
    let B := R '' (C.triangle (C.right s).face).carrier
    have convex : Convex ℝ (A ∩ B) :=
      ((C.triangle (C.left s).face).convex_carrier.affine_image L.toAffineMap).inter
        ((C.triangle (C.right s).face).convex_carrier.affine_image R.toAffineMap)
    have full : (interior (A ∩ B)).Nonempty := ⟨p, by rw [interior_inter]; exact ⟨first, last⟩⟩
    have center : L x.val ∈ A ∩ B :=
      ⟨⟨x.val, l.property, rfl⟩, ⟨(C.identify s x).val, r.property, (joined s kept x).symm⟩⟩
    have closure : L x.val ∈ closure (interior (A ∩ B)) := by
      rw [convex.closure_interior_eq_closure_of_nonempty_interior full]
      exact subset_closure center
    obtain ⟨z, inside, close⟩ := Metric.mem_closure_iff.mp closure radius positive
    rw [interior_inter, ← rigid_image_interior L, ← rigid_image_interior R] at inside
    obtain ⟨⟨a, ha, az⟩, ⟨b, hb, bz⟩⟩ := inside
    let a' : C.Cell (C.left s).face := ⟨a, interior_subset ha⟩
    let b' : C.Cell (C.right s).face := ⟨b, interior_subset hb⟩
    have ain := face_inside _ a' ha
    have bin := face_inside _ b' hb
    let qa : Metric.ball q radius := ⟨⟨C.faceMap retain (C.left s).face a', ain⟩, by
      change dist (C.faceMap retain (C.left s).face a')
        (C.faceMap retain (C.left s).face l) < radius
      rw [(F.faceMap_isometry retain _).dist_eq]
      change dist a x.val < radius
      rw [← L.isometry.dist_eq a x.val, az]
      exact (dist_comm _ _).trans_lt close⟩
    let qb : Metric.ball q radius := ⟨⟨C.faceMap retain (C.right s).face b', bin⟩, by
      change dist (C.faceMap retain (C.right s).face b')
        (C.faceMap retain (C.left s).face l) < radius
      rw [identified, (F.faceMap_isometry retain _).dist_eq]
      change dist b (C.identify s x).val < radius
      rw [← R.isometry.dist_eq b (C.identify s x).val, bz, ← joined s kept x]
      exact (dist_comm _ _).trans_lt close⟩
    have equal_coords : coordinates qa.val = coordinates qb.val :=
      (agrees _ a' ain).trans ((az.trans bz.symm).trans (agrees _ b' bin).symm)
    have equal_ball : qa = qb := isometry.injective equal_coords
    have equal_points : C.faceMap retain (C.left s).face a' =
        C.faceMap retain (C.right s).face b' :=
      congrArg (fun y : Metric.ball q radius => y.val.val) equal_ball
    have related : Relation.EqvGen (C.glue retain) ⟨(C.left s).face, a'⟩
        ⟨(C.right s).face, b'⟩ := (C.faceMap_eq_iff retain _ _ a' b').mp equal_points
    have tags : (⟨(C.left s).face, a'⟩ : C.Total) = ⟨(C.right s).face, b'⟩ :=
      C.eq_of_related_interior ha related
    exact F.incident_faces_ne s (congrArg Sigma.fst tags)
  let E : FacewiseDevelopment C retain :=
    { place := place
      joined := joined
      opposite := fun s kept => (C.triangle (C.left s).face).placed_opposite_of_disjoint
        (C.triangle (C.right s).face) (C.left s).edge (C.right s).edge (C.identify s)
        (place (C.left s).face) (place (C.right s).face) (joined s kept) (separated s kept) }
  have coordinate_equal (x : U) : E.toPlane x.val = coordinates x := by
    obtain ⟨⟨f, p⟩, image⟩ := MetricGluing.point_surjective C.Cell (C.glue retain) x.val
    change C.faceMap retain f p = x.val at image
    have member : C.faceMap retain f p ∈ U := image.symm ▸ x.property
    calc
      E.toPlane x.val = E.toPlane (C.faceMap retain f p) := congrArg E.toPlane image.symm
      _ = place f p.val := rfl
      _ = coordinates ⟨C.faceMap retain f p, member⟩ := (agrees f p member).symm
      _ = coordinates x := congrArg coordinates (Subtype.ext image)
  refine ⟨E, ?_⟩
  intro x inside
  obtain ⟨r, positive, nearby_isometry⟩ := local_isometry ⟨x, inside⟩
  obtain ⟨a, apos, included⟩ := Metric.isOpen_iff.mp open_U x inside
  let radius := min r a
  have radius_pos : 0 < radius := lt_min positive apos
  let lift (y : Metric.ball x radius) : Metric.ball (⟨x, inside⟩ : U) r :=
    ⟨⟨y.val, included ((Metric.ball_subset_ball (min_le_right _ _)) y.property)⟩,
      (Metric.mem_ball.mp y.property).trans_le (min_le_left _ _)⟩
  have lift_isometry : Isometry lift := fun _ _ => rfl
  refine ⟨radius, radius_pos, ?_⟩
  rw [Metric.eball_ofReal]
  have equal : (fun y : Metric.ball x radius => E.toPlane y.val) =
      (fun y : Metric.ball x radius => coordinates (lift y).val) :=
    funext fun y => coordinate_equal (lift y).val
  rw [equal]
  exact nearby_isometry.comp lift_isometry

include F in
/-- Forget the local-isometry certificate when only rigid face placements are needed. -/
theorem exists_development_of_regular_disk (retain : Set C.Seam)
    (disk : C.Realization retain ≃ₜ Metric.closedBall (0 : Plane) 1)
    (regular : ∀ x, ‖(disk x).val‖ < 1 → C.IsRegularPoint retain x) :
    Nonempty (FacewiseDevelopment C retain) := by
  obtain ⟨E, _local⟩ := F.exists_locally_isometric_development_of_regular_disk retain disk regular
  exact ⟨E⟩

include F in
/-- Flat interior vertices make every point of the open disk intrinsically regular. -/
theorem isRegularPoint_of_flat_disk (retain : Set C.Seam)
    (disk : C.Realization retain ≃ₜ Metric.closedBall (0 : Plane) 1)
    (flat : ∀ vertex : C.Vertex retain, ¬ C.IsBoundaryVertex retain vertex →
      C.totalAngle retain vertex = 2 * Real.pi)
    (x : C.Realization retain) (inside : ‖(disk x).val‖ < 1) : C.IsRegularPoint retain x := by
  have outside : x ∉ C.bankBoundary retain := by
    intro boundary
    have norm := (F.bankBoundary_iff_disk_norm_eq_one retain disk x).mp boundary
    exact inside.ne norm
  by_cases vertex : x ∈ Set.range (C.vertexPoint retain)
  · obtain ⟨vertex, rfl⟩ := vertex
    have interior : ¬ C.IsBoundaryVertex retain vertex := fun boundary =>
      outside ((C.vertexPoint_mem_bankBoundary_iff retain vertex).mpr boundary)
    exact F.isRegularPoint_flat_vertex retain vertex interior (flat vertex interior)
  · exact F.isRegularPoint_of_not_bankBoundary_of_not_vertex retain x outside vertex

include F in
/-- Total angle `2π` at interior vertices gives a development with no interior branching. -/
theorem exists_locally_isometric_development_of_flat_disk (retain : Set C.Seam)
    (disk : C.Realization retain ≃ₜ Metric.closedBall (0 : Plane) 1)
    (flat : ∀ vertex : C.Vertex retain, ¬ C.IsBoundaryVertex retain vertex →
      C.totalAngle retain vertex = 2 * Real.pi) :
    ∃ E : FacewiseDevelopment C retain, ∀ x, ‖(disk x).val‖ < 1 → ∃ r > 0,
      Isometry (fun y : Metric.eball x (ENNReal.ofReal r) => E.toPlane y.val) :=
  F.exists_locally_isometric_development_of_regular_disk retain disk
    (F.isRegularPoint_of_flat_disk retain disk flat)

include F in
/-- Total angle `2π` at each interior vertex gives the required metric regularity. -/
theorem exists_development_of_flat_disk (retain : Set C.Seam)
    (disk : C.Realization retain ≃ₜ Metric.closedBall (0 : Plane) 1)
    (flat : ∀ vertex : C.Vertex retain, ¬ C.IsBoundaryVertex retain vertex →
      C.totalAngle retain vertex = 2 * Real.pi) : Nonempty (FacewiseDevelopment C retain) :=
  F.exists_development_of_regular_disk retain disk (F.isRegularPoint_of_flat_disk retain disk flat)

include F in
/-- A prescribed root face determines exactly one outward development of a flat metric disk. -/
theorem existsUnique_normalized_development_of_flat_disk (retain : Set C.Seam)
    (disk : C.Realization retain ≃ₜ Metric.closedBall (0 : Plane) 1)
    (flat : ∀ vertex : C.Vertex retain, ¬ C.IsBoundaryVertex retain vertex →
      C.totalAngle retain vertex = 2 * Real.pi)
    (root : Face) (target : Plane ≃ᵃⁱ[ℝ] Plane) :
    ∃! E : FacewiseDevelopment C retain, E.place root = target := by
  obtain ⟨E⟩ := F.exists_development_of_flat_disk retain disk flat
  let : ConnectedSpace (Metric.closedBall (0 : Plane) 1) :=
    isConnected_iff_connectedSpace.mp
      ((convex_closedBall (0 : Plane) 1).isConnected ⟨0, Metric.mem_closedBall_self zero_le_one⟩)
  let : ConnectedSpace (C.Realization retain) :=
    disk.symm.surjective.connectedSpace disk.symm.continuous
  refine ⟨E.normalize root target, E.normalize_root root target, ?_⟩
  intro other normalized
  exact other.eq_of_root (E.normalize root target) (C.duallyConnected_of_preconnected retain) root
    (normalized.trans (E.normalize_root root target).symm)


include F in
/-- Normalization preserves the actual local isometry, as well as uniqueness of all face motions. -/
theorem existsUnique_normalized_isometric_development_of_flat_disk (retain : Set C.Seam)
    (disk : C.Realization retain ≃ₜ Metric.closedBall (0 : Plane) 1)
    (flat : ∀ vertex : C.Vertex retain, ¬ C.IsBoundaryVertex retain vertex →
      C.totalAngle retain vertex = 2 * Real.pi)
    (root : Face) (target : Plane ≃ᵃⁱ[ℝ] Plane) :
    ∃! E : FacewiseDevelopment C retain, E.place root = target ∧
      ∀ x, ‖(disk x).val‖ < 1 → ∃ r > 0,
        Isometry (fun y : Metric.eball x (ENNReal.ofReal r) => E.toPlane y.val) := by
  obtain ⟨E, local_isometry⟩ := F.exists_locally_isometric_development_of_flat_disk retain disk flat
  obtain ⟨unique, normalized, uniqueness⟩ :=
    F.existsUnique_normalized_development_of_flat_disk retain disk flat root target
  have agrees : E.normalize root target = unique :=
    uniqueness (E.normalize root target) (E.normalize_root root target)
  refine ⟨unique, ⟨normalized, ?_⟩, fun other h => uniqueness other h.1⟩
  intro x inside
  obtain ⟨r, positive, isometric⟩ := local_isometry x inside
  refine ⟨r, positive, ?_⟩
  rw [← agrees]
  exact E.isometry_postcompose ((E.place root).symm.trans target) isometric

end Unfoldings.SpatialFolding
