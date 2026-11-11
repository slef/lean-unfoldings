module

public import Unfoldings.Cap.ClipPairings
public import Unfoldings.Geometry.ConformingStar

/-! The whole-edge paired roof clip has precisely the actual spatial point fibers. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap.ClipSpatialTriangles

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexCap C} {Z : ℝ} (T : K.ClipSpatialTriangles Z)

local instance : Fintype T.Index := @Fintype.ofFinite _ T.finite

/-- The actual intrinsic copy of a projected point in one physical clip triangle. -/
def pointCopy (i : T.Index) (p : Plane) (member : p ∈ (T.projectedTriangle i).carrier) :
    T.pairedComplex.Realization Set.univ :=
  T.pairedComplex.faceMap Set.univ i
    ⟨(K.projectFaceEquiv (T.face i)).symm p,
      (T.triangle_carrier i).symm.subset ⟨p, member, rfl⟩⟩

theorem pointCopy_congr (i : T.Index) {p q : Plane} (equal : p = q)
    (first : p ∈ (T.projectedTriangle i).carrier) (last : q ∈ (T.projectedTriangle i).carrier) :
    T.pointCopy i p first = T.pointCopy i q last := by
  subst q
  rfl

theorem pointCopy_toSpace (i : T.Index) (p : Plane)
    (member : p ∈ (T.projectedTriangle i).carrier) :
    T.pairedFolding.toSpace Set.univ (T.pointCopy i p member) = K.roofPoint p := by
  rw [pointCopy, SpatialFolding.toSpace_faceMap]
  change T.placement i ((K.projectFaceEquiv (T.face i)).symm p) = _
  rw [T.placement_eq_roofPoint i ((T.triangle_carrier i).symm.subset ⟨p, member, rfl⟩)]
  exact congrArg K.roofPoint ((K.projectFaceEquiv (T.face i)).apply_symm_apply p)

theorem pairedComplex_complete {a b : EdgeRef T.Index} (different : a.face ≠ b.face)
    (same : TriangleFamily.edgeCarrier T.projectedTriangle a =
      TriangleFamily.edgeCarrier T.projectedTriangle b) :
    ∃ s : T.pairedComplex.Seam,
      (T.pairedComplex.left s = a ∧ T.pairedComplex.right s = b) ∨
      (T.pairedComplex.left s = b ∧ T.pairedComplex.right s = a) := by
  exact TriangleFamily.pairedComplex_complete T.projectedTriangle T.separated different same

/-- On each constructed seam the two intrinsic copies of the projected point agree. -/
theorem pointCopy_eq_across_seam (s : T.pairedComplex.Seam) {p : Plane}
    (member : p ∈ (T.projectedTriangle (T.pairedComplex.left s).face).edge
      (T.pairedComplex.left s).edge) :
    T.pointCopy (T.pairedComplex.left s).face p
        ((T.projectedTriangle _).edge_subset _ member) =
      T.pointCopy (T.pairedComplex.right s).face p
        ((T.projectedTriangle _).edge_subset _
          ((T.paired_seam_projected_edge s).subset member)) := by
  let a := T.pairedComplex.left s
  let b := T.pairedComplex.right s
  let x := (T.edgeProjection a.face a.edge).symm ⟨p, member⟩
  have first_value : x.val = (K.projectFaceEquiv (T.face a.face)).symm p := rfl
  have projected : K.projectFace (T.face b.face) (T.pairedComplex.identify s x).val = p := by
    have first_projected : K.projectFace (T.face a.face) x.val = p := by
      rw [first_value]
      exact (K.projectFaceEquiv (T.face a.face)).apply_symm_apply p
    exact (T.paired_seam_projection s x).trans first_projected
  have last_value : (T.pairedComplex.identify s x).val =
      (K.projectFaceEquiv (T.face b.face)).symm p := by
    apply (K.projectFaceEquiv (T.face b.face)).injective
    exact projected.trans ((K.projectFaceEquiv (T.face b.face)).apply_symm_apply p).symm
  have equal := T.pairedComplex.seam_identified Set.univ s (Set.mem_univ s) x
  change T.pairedComplex.faceMap Set.univ a.face ⟨x.val, _⟩ =
    T.pairedComplex.faceMap Set.univ b.face ⟨(T.pairedComplex.identify s x).val, _⟩ at equal
  simpa only [pointCopy, first_value, last_value] using equal

/-- Any equal projected whole edge identifies all its physical intrinsic point copies. -/
theorem pointCopy_eq_of_shared_edge {i j : T.Index} (e f : Fin 3)
    (same : (T.projectedTriangle i).edge e = (T.projectedTriangle j).edge f)
    {p : Plane} (member : p ∈ (T.projectedTriangle i).edge e) :
    T.pointCopy i p ((T.projectedTriangle i).edge_subset e member) =
      T.pointCopy j p ((T.projectedTriangle j).edge_subset f (same ▸ member)) := by
  by_cases same_face : i = j
  · subst j
    rfl
  · obtain ⟨s, ⟨first, last⟩ | ⟨first, last⟩⟩ :=
      T.pairedComplex_complete (a := ⟨i, e⟩) (b := ⟨j, f⟩) same_face same
    · have at_left : p ∈ (T.projectedTriangle (T.pairedComplex.left s).face).edge
          (T.pairedComplex.left s).edge := by simpa only [first] using member
      simpa only [first, last] using T.pointCopy_eq_across_seam s at_left
    · have at_left : p ∈ (T.projectedTriangle (T.pairedComplex.left s).face).edge
          (T.pairedComplex.left s).edge := by simpa only [first] using (same ▸ member)
      simpa only [first, last] using (T.pointCopy_eq_across_seam s at_left).symm

theorem projected_member (i : T.Index) {x : Plane} (member : x ∈ (T.triangle i).carrier) :
    K.projectFace (T.face i) x ∈ (T.projectedTriangle i).carrier := by
  obtain ⟨p, member, equal⟩ := (T.triangle_carrier i).subset member
  rw [← equal]
  change (K.projectFaceEquiv (T.face i)) ((K.projectFaceEquiv (T.face i)).symm p) ∈ _
  rw [(K.projectFaceEquiv (T.face i)).apply_symm_apply]
  exact member

theorem pointCopy_of_localPoint (i : T.Index) (x : (T.triangle i).Cell) :
    T.pointCopy i (K.projectFace (T.face i) x.val) (T.projected_member i x.property) =
      T.pairedComplex.faceMap Set.univ i x := by
  apply congrArg (T.pairedComplex.faceMap Set.univ i)
  exact Subtype.ext ((K.projectFaceEquiv (T.face i)).symm_apply_apply x.val)

/-- Actual edge compatibility propagates through every vertex star of a conforming clip. -/
theorem pointCopy_eq (conforming : TriangleFamily.Conforming T.projectedTriangle)
    (p : Plane) {i j : T.Index} (first : p ∈ (T.projectedTriangle i).carrier)
    (last : p ∈ (T.projectedTriangle j).carrier) :
    T.pointCopy i p first = T.pointCopy j p last := by
  let value (a : {i // p ∈ (T.projectedTriangle i).carrier}) := T.pointCopy a.val p a.property
  exact TriangleFamily.incident_values_eq T.projectedTriangle (K.convex_clipFootprint Z)
    T.cover.symm conforming T.separated p value
    (fun _ _ e f same member => T.pointCopy_eq_of_shared_edge e f same member)
    ⟨i, first⟩ ⟨j, last⟩

/-- The paired metric realization has exactly the geometric fibers of the actual roof. -/
theorem pairedFolding_embedded (conforming : TriangleFamily.Conforming T.projectedTriangle) :
    T.pairedFolding.IsEmbedded := by
  intro x y equal
  obtain ⟨⟨i, a⟩, rfl⟩ :=
    MetricGluing.point_surjective T.pairedComplex.Cell (T.pairedComplex.glue Set.univ) x
  obtain ⟨⟨j, b⟩, rfl⟩ :=
    MetricGluing.point_surjective T.pairedComplex.Cell (T.pairedComplex.glue Set.univ) y
  have projected : K.projectFace (T.face i) a.val = K.projectFace (T.face j) b.val :=
    congrArg Cap.horizontal equal
  have first := T.projected_member i a.property
  have last : K.projectFace (T.face i) a.val ∈ (T.projectedTriangle j).carrier :=
    projected.symm ▸ T.projected_member j b.property
  calc
    T.pairedComplex.faceMap Set.univ i a =
        T.pointCopy i (K.projectFace (T.face i) a.val) first :=
      (T.pointCopy_of_localPoint i a).symm
    _ = T.pointCopy j (K.projectFace (T.face i) a.val) last :=
      T.pointCopy_eq conforming _ first last
    _ = T.pointCopy j (K.projectFace (T.face j) b.val) (T.projected_member j b.property) :=
      T.pointCopy_congr j projected _ _
    _ = T.pairedComplex.faceMap Set.univ j b := T.pointCopy_of_localPoint j b

/-- Common refinement gives an embedded physical clip without adding geometric hypotheses. -/
theorem refined_pairedFolding_embedded : T.refined.pairedFolding.IsEmbedded :=
  T.refined.pairedFolding_embedded T.refined_conforming

end Unfoldings.ConvexCap.ClipSpatialTriangles
