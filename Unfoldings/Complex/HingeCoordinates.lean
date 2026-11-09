module

public import Unfoldings.Complex.Hinge
public import Unfoldings.Metric.LocalSeams

/-! Local planar coordinates around retained seams with distinct incident faces. -/

@[expose] public section

open scoped ENNReal

noncomputable section

namespace Unfoldings.TriangleComplex

universe u v

variable {Face : Type u} [Fintype Face] (C : TriangleComplex.{u, v} Face)

theorem incident_seam_eq (retain : Set C.Seam) (s : C.Seam) (kept : s ∈ retain)
    (x : (C.triangle (C.left s).face).Edge (C.left s).edge)
    (regular : ¬ (C.triangle (C.left s).face).IsVertex x) (t : (C.closedSeams retain).Seam)
    (incident : (C.closedSeams retain).Incident (C.edgePoint (C.left s) x) t) : t.val = s := by
  obtain ⟨q, related, z, rfl⟩ := incident
  change Relation.EqvGen (C.closedSeams retain).relation
    (C.edgePoint (C.left s) x) ⟨_, (C.closedSeams retain).toLeft t z⟩ at related
  rw [C.closedSeams_relation] at related
  have regular' : ¬ C.IsVertex (C.edgePoint (C.left s) x) := regular
  have related' : Relation.EqvGen (C.glue retain) (C.edgePoint (C.left s) x)
      (C.edgePoint (C.left t.val) z) := by
    exact related
  have crossing : C.Crosses retain (C.edgePoint (C.left s) x)
      (C.edgePoint (C.right s) (C.identify s x)) := ⟨s, kept, false, x, rfl, rfl⟩
  rcases (C.eqvGen_iff_eq_or_neighbor regular' crossing).mp related' with equal | equal
  · have edges := C.onEdge_unique regular' (C.edgePoint_onEdge (C.left s) x)
      (equal ▸ C.edgePoint_onEdge (C.left t.val) z)
    exact (C.unique s t.val (Or.inl edges)).symm
  · have other_regular : ¬ C.IsVertex (C.edgePoint (C.right s) (C.identify s x)) :=
      fun h => regular ((C.crosses_preserves_vertex crossing).mpr h)
    have edges := C.onEdge_unique other_regular
      (C.edgePoint_onEdge (C.right s) (C.identify s x))
      (equal ▸ C.edgePoint_onEdge (C.left t.val) z)
    exact (C.unique s t.val (Or.inr (Or.inr (Or.inl edges)))).symm

/-- A rigid frame in every face, using the outward hinge frame in its right face. -/
def hingeFrame (s : C.Seam) (f : Face) : Plane ≃ᵃⁱ[ℝ] Plane := by
  classical
  exact if f = (C.right s).face then (C.seamHinge s).place
    else AffineIsometryEquiv.refl ℝ Plane

@[simp] theorem hingeFrame_right (s : C.Seam) :
    C.hingeFrame s (C.right s).face = (C.seamHinge s).place := by simp [hingeFrame]

theorem hingeFrame_left (s : C.Seam) (different : (C.left s).face ≠ (C.right s).face) :
    C.hingeFrame s (C.left s).face = AffineIsometryEquiv.refl ℝ Plane := by
  simp [hingeFrame, different]

/-- Tagged coordinates; these are only asserted to descend locally, not globally. -/
def hingeCoordinates (s : C.Seam) (a : C.Total) : Plane := C.hingeFrame s a.1 a.2.val

theorem hingeCoordinates_isometry (s : C.Seam) (f : Face) :
    Isometry (fun x : C.Cell f => C.hingeCoordinates s ⟨f, x⟩) :=
  (C.hingeFrame s f).isometry.comp isometry_subtype_coe

theorem hingeCoordinates_left (s : C.Seam)
    (different : (C.left s).face ≠ (C.right s).face) (x : C.Cell (C.left s).face) :
    C.hingeCoordinates s ⟨(C.left s).face, x⟩ = x.val := by
  simp [hingeCoordinates, C.hingeFrame_left s different]

theorem hingeCoordinates_right (s : C.Seam) (x : C.Cell (C.right s).face) :
    C.hingeCoordinates s ⟨(C.right s).face, x⟩ = (C.seamHinge s).place x.val := by
  simp [hingeCoordinates]

theorem hingeCoordinates_class (retain : Set C.Seam) (s : C.Seam) (kept : s ∈ retain)
    (different : (C.left s).face ≠ (C.right s).face)
    (x : (C.triangle (C.left s).face).Edge (C.left s).edge)
    (regular : ¬ (C.triangle (C.left s).face).IsVertex x) {a : C.Total}
    (related : Relation.EqvGen (C.glue retain) (C.edgePoint (C.left s) x) a) :
    C.hingeCoordinates s a = x.val := by
  have crossing : C.Crosses retain (C.edgePoint (C.left s) x)
      (C.edgePoint (C.right s) (C.identify s x)) := ⟨s, kept, false, x, rfl, rfl⟩
  have regular' : ¬ C.IsVertex (C.edgePoint (C.left s) x) := regular
  rcases (C.eqvGen_iff_eq_or_neighbor regular' crossing).mp related with rfl | rfl
  · exact C.hingeCoordinates_left s different _
  · exact (C.hingeCoordinates_right s _).trans ((C.seamHinge s).joined x)

theorem exists_radius_hinge_step (retain : Set C.Seam) (s : C.Seam) (kept : s ∈ retain)
    (different : (C.left s).face ≠ (C.right s).face)
    (x : (C.triangle (C.left s).face).Edge (C.left s).edge)
    (regular : ¬ (C.triangle (C.left s).face).IsVertex x) : ∃ r > 0, ∀ a b,
      edist (MetricGluing.point C.Cell (C.glue retain) (C.edgePoint (C.left s) x))
        (MetricGluing.point C.Cell (C.glue retain) a) < ENNReal.ofReal r →
      edist (MetricGluing.point C.Cell (C.glue retain) (C.edgePoint (C.left s) x))
        (MetricGluing.point C.Cell (C.glue retain) b) < ENNReal.ofReal r →
      edist (C.hingeCoordinates s a) (C.hingeCoordinates s b) ≤
        MetricGluing.stepCost C.Cell (C.glue retain) a b := by
  have finite : ∀ i, (MetricGluing.classIn C.Cell (C.closedSeams retain).relation
      (C.edgePoint (C.left s) x) i).Finite := by
    simpa only [C.closedSeams_relation] using C.finite_classIn retain (C.edgePoint (C.left s) x)
  have compatible : ∀ t, (C.closedSeams retain).Incident (C.edgePoint (C.left s) x) t → ∀ z,
      C.hingeCoordinates s ⟨_, (C.closedSeams retain).toLeft t z⟩ =
        C.hingeCoordinates s ⟨_, (C.closedSeams retain).toRight t z⟩ := by
    intro t incident z
    have same := C.incident_seam_eq retain s kept x regular t incident
    obtain ⟨t, ht⟩ := t
    dsimp only at same
    subst t
    change C.hingeCoordinates s
        ⟨(C.left s).face, (C.triangle (C.left s).face).edgeMap (C.left s).edge z⟩ =
      C.hingeCoordinates s
        ⟨(C.right s).face, (C.triangle (C.right s).face).edgeMap (C.right s).edge
          (C.identify s z)⟩
    rw [C.hingeCoordinates_left s different, C.hingeCoordinates_right]
    exact ((C.seamHinge s).joined z).symm
  have result :=
    (C.closedSeams retain).exists_radius_local_step (C.edgePoint (C.left s) x) finite
      (fun f y => C.hingeCoordinates s ⟨f, y⟩)
      (fun f => (C.hingeCoordinates_isometry s f).lipschitzWith) compatible
  rw [C.closedSeams_relation] at result
  exact result

/-- The straight radial segment in either incident face bounds distance from the seam point. -/
theorem edist_center_le_hingeCoordinates (retain : Set C.Seam) (s : C.Seam) (kept : s ∈ retain)
    (different : (C.left s).face ≠ (C.right s).face)
    (x : (C.triangle (C.left s).face).Edge (C.left s).edge) (a : C.Total)
    (faces : a.1 = (C.left s).face ∨ a.1 = (C.right s).face) :
    edist (MetricGluing.point C.Cell (C.glue retain) (C.edgePoint (C.left s) x))
      (MetricGluing.point C.Cell (C.glue retain) a) ≤ edist x.val (C.hingeCoordinates s a) := by
  obtain ⟨f, a⟩ := a
  rcases faces with rfl | rfl
  · rw [C.hingeCoordinates_left s different]
    exact MetricGluing.edist_of_le C.Cell (C.glue retain) _ _ _
  · rw [C.hingeCoordinates_right]
    change edist (C.faceMap retain (C.left s).face
      ((C.triangle (C.left s).face).edgeMap (C.left s).edge x))
      (C.faceMap retain (C.right s).face a) ≤ _
    rw [C.seam_identified retain s kept x, ← (C.seamHinge s).joined x,
      (C.seamHinge s).place.isometry _ _]
    exact MetricGluing.edist_of_le C.Cell (C.glue retain) _ _ _

/-- A covered planar ball has lifts in the original incident cells. -/
theorem exists_hinge_lift (s : C.Seam)
    (different : (C.left s).face ≠ (C.right s).face) {center z : Plane} {r : ℝ}
    (cover : Metric.ball center r ⊆ (C.triangle (C.left s).face).carrier ∪
      (C.seamHinge s).place '' (C.triangle (C.right s).face).carrier)
    (near : z ∈ Metric.ball center r) : ∃ a : C.Total,
      (a.1 = (C.left s).face ∨ a.1 = (C.right s).face) ∧ C.hingeCoordinates s a = z := by
  rcases cover near with left | right
  · exact ⟨⟨_, ⟨z, left⟩⟩, Or.inl rfl, C.hingeCoordinates_left s different _⟩
  · obtain ⟨w, hw, rfl⟩ := right
    exact ⟨⟨_, ⟨w, hw⟩⟩, Or.inr rfl, C.hingeCoordinates_right s _⟩

/-- Intrinsic closeness forces closeness in the local planar frame. -/
theorem hingeCoordinates_mem_ball (retain : Set C.Seam) (s : C.Seam) (kept : s ∈ retain)
    (different : (C.left s).face ≠ (C.right s).face)
    (x : (C.triangle (C.left s).face).Edge (C.left s).edge)
    (regular : ¬ (C.triangle (C.left s).face).IsVertex x) {ε r : ℝ}
    (positive : 0 < ε) (small : r ≤ ε)
    (transport : MetricGluing.ClassTransport C.Cell (C.glue retain)
      (C.edgePoint (C.left s) x) ε) (a : C.Total)
    (near : edist (MetricGluing.point C.Cell (C.glue retain) (C.edgePoint (C.left s) x))
      (MetricGluing.point C.Cell (C.glue retain) a) < ENNReal.ofReal r) :
    C.hingeCoordinates s a ∈ Metric.ball x.val r := by
  obtain ⟨q, related, close⟩ := MetricGluing.exists_classPoint_of_edist_lt C.Cell
    (C.glue retain) (C.edgePoint (C.left s) x) positive small
    (C.finite_classIn retain _) transport a near
  apply Metric.mem_ball.mpr
  calc
    dist (C.hingeCoordinates s a) x.val =
        dist (C.hingeCoordinates s a) (C.hingeCoordinates s ⟨a.1, q⟩) := by
      rw [C.hingeCoordinates_class retain s kept different x regular related]
    _ = dist a.2 q := (C.hingeCoordinates_isometry s a.1).dist_eq a.2 q
    _ < r := close

/-- Planar chords in a covered hinge ball bound distances in the full complex. -/
theorem edist_le_hinge_coordinates (retain : Set C.Seam) (s : C.Seam) (kept : s ∈ retain)
    (different : (C.left s).face ≠ (C.right s).face) {center : Plane} {r : ℝ}
    (cover : Metric.ball center r ⊆ (C.triangle (C.left s).face).carrier ∪
      (C.seamHinge s).place '' (C.triangle (C.right s).face).carrier)
    (a b : C.Total) (faces_a : a.1 = (C.left s).face ∨ a.1 = (C.right s).face)
    (faces_b : b.1 = (C.left s).face ∨ b.1 = (C.right s).face)
    (near_a : C.hingeCoordinates s a ∈ Metric.ball center r)
    (near_b : C.hingeCoordinates s b ∈ Metric.ball center r) :
    edist (MetricGluing.point C.Cell (C.glue retain) a)
      (MetricGluing.point C.Cell (C.glue retain) b) ≤
        edist (C.hingeCoordinates s a) (C.hingeCoordinates s b) := by
  have same_face (f : Face) (a b : C.Cell f) :
      edist (C.faceMap retain f a) (C.faceMap retain f b) ≤
        edist (C.hingeCoordinates s ⟨f, a⟩) (C.hingeCoordinates s ⟨f, b⟩) := by
    rw [(C.hingeCoordinates_isometry s f) a b]
    simpa only [ENNReal.coe_one, one_mul] using (C.faceMap_lipschitz retain f).edist_le_mul a b
  obtain ⟨f, a⟩ := a
  obtain ⟨g, b⟩ := b
  rcases faces_a with rfl | rfl <;> rcases faces_b with rfl | rfl
  · exact same_face _ a b
  · rw [C.hingeCoordinates_left s different] at near_a ⊢
    rw [C.hingeCoordinates_right] at near_b ⊢
    exact C.edist_le_hinge_chord retain s kept cover a b near_a near_b
  · rw [C.hingeCoordinates_right] at near_a ⊢
    rw [C.hingeCoordinates_left s different] at near_b ⊢
    rw [edist_comm (MetricGluing.point _ _ _) _, edist_comm ((C.seamHinge s).place _) _]
    exact C.edist_le_hinge_chord retain s kept cover b a near_b near_a
  · exact same_face _ a b

end Unfoldings.TriangleComplex
