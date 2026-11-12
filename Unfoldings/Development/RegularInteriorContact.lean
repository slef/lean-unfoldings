module

public import Unfoldings.Development.ClosedFaceSeparation
public import Unfoldings.Complex.Regular
public import Unfoldings.Metric.LocalIsometryBallImage
public import Unfoldings.Metric.Connected
public import Unfoldings.Geometry.TriangleNeighborhood

/-! Nonoverlap and actual local isometry exclude every foreign copy at a regular point. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FacewiseDevelopment

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {retain : Set C.Seam} (D : FacewiseDevelopment C retain)

theorem Nonoverlapping.eq_of_toPlane_eq_at_regular_local_isometry
    [PreconnectedSpace (C.Realization retain)] (nonoverlap : D.Nonoverlapping)
    (x : C.Realization retain) (regular : C.IsRegularPoint retain x)
    (local_isometry : ∃ r > 0,
      Isometry (fun y : Metric.eball x (ENNReal.ofReal r) => D.toPlane y.val))
    (y : C.Realization retain) (same : D.toPlane y = D.toPlane x) : x = y := by
  let : MetricSpace (C.Realization retain) := EMetricSpace.toMetricSpace
    (fun a b => edist_ne_top_of_preconnected a b)
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
  change D.place g z.val = D.toPlane x at same
  apply eq_of_forall_dist_le
  intro ε positive
  obtain ⟨r, rpositive, in_region, image⟩ :=
    regular.local_isometry_ball_image D.toPlane local_ball Metric.isOpen_ball
      (Metric.mem_ball_self (half_pos positive))
  obtain ⟨q, qinside, close, _different⟩ := (C.triangle g).exists_near_interior_ne z.property
    (lt_min rpositive (half_pos positive))
  let a : C.Cell g := ⟨q, interior_subset qinside⟩
  have image_close : D.place g q ∈ Metric.ball (D.toPlane x) r := by
    rw [Metric.mem_ball, ← same, (D.place g).isometry.dist_eq]
    exact close.trans_le (min_le_left _ _)
  obtain ⟨w, near, at_w⟩ := image.symm.subset image_close
  have actual : w = C.faceMap retain g a :=
    Nonoverlapping.eq_faceMap_of_toPlane_eq_interior D nonoverlap g a qinside w at_w
  have first_close : dist x (C.faceMap retain g a) < ε / 2 := by
    have near' := in_region near
    rw [actual] at near'
    simpa only [Metric.mem_ball, dist_comm] using near'
  have last_close : dist (C.faceMap retain g a) (C.faceMap retain g z) < ε / 2 := by
    rw [(D.faceMap_isometry g).dist_eq]
    exact close.trans_le (min_le_right _ _)
  have estimate := dist_triangle x (C.faceMap retain g a) (C.faceMap retain g z)
  change dist x (C.faceMap retain g z) ≤ ε
  linarith

end Unfoldings.FacewiseDevelopment
