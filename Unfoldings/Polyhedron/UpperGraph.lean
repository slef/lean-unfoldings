module

public import Unfoldings.Polyhedron.UpperPlanes

/-! The complete upper graph of a convex polyhedron, from its original upward face planes. -/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialFolding.ConvexBoundary

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {F : SpatialFolding C} (P : F.ConvexBoundary) (N : F.SupportingNormals)

def upperHeight (p : Plane) : ℝ :=
  N.upperFaces.inf' (P.upperFaces_nonempty N) (fun f => N.supportHeight f p)

theorem upperHeight_le (f : N.UpperFace) (p : Plane) :
    P.upperHeight N p ≤ N.supportHeight f.val p :=
  Finset.inf'_le _ ((N.mem_upperFaces f.val).mpr f.property)

theorem exists_upperHeight_eq (p : Plane) :
    ∃ f : N.UpperFace, P.upperHeight N p = N.supportHeight f.val p := by
  obtain ⟨f, member, equal⟩ := Finset.exists_mem_eq_inf' (P.upperFaces_nonempty N)
    (fun f => N.supportHeight f p)
  exact ⟨⟨f, (N.mem_upperFaces f).mp member⟩, equal⟩

theorem continuous_upperHeight : Continuous (P.upperHeight N) :=
  Continuous.finset_inf'_apply (P.upperFaces_nonempty N)
    (fun f _ => (N.supportHeight f).continuous_of_finiteDimensional)

/-- The body's full horizontal projection, rather than a supplied roof-domain certificate. -/
def bodyFootprint (_P : F.ConvexBoundary) : Set Plane := Cap.horizontal '' F.vertexHull

def upperPoint (p : Plane) : Space := Cap.horizontalAtHeight p (P.upperHeight N p)

@[simp] theorem horizontal_upperPoint (p : Plane) : Cap.horizontal (P.upperPoint N p) = p :=
  Cap.horizontal_horizontalAtHeight _ _

@[simp] theorem height_upperPoint (p : Plane) : P.upperPoint N p 2 = P.upperHeight N p := rfl

theorem upperHeight_ge_body {z : Space} (member : z ∈ F.vertexHull) :
    z 2 ≤ P.upperHeight N (Cap.horizontal z) := by
  obtain ⟨f, equal⟩ := P.exists_upperHeight_eq N (Cap.horizontal z)
  rw [equal]
  exact (N.supporting_iff f z).mp (N.supporting f.val z member)

/-- Solving the upward inequalities gives a genuine body point: every downward or vertical
support remains satisfied when raising an already feasible point. -/
theorem upperPoint_mem_body {p : Plane} (member : p ∈ P.bodyFootprint) :
    P.upperPoint N p ∈ F.vertexHull := by
  obtain ⟨z, member, rfl⟩ := member
  rw [P.vertexHull_eq_face_halfspaces N]
  intro f
  by_cases upward : 0 < N.normal f 2
  · exact (N.supporting_iff ⟨f, upward⟩ _).mpr (by
      rw [P.horizontal_upperPoint, P.height_upperPoint]
      exact P.upperHeight_le N ⟨f, upward⟩ _)
  · have nonpositive : N.normal f 2 ≤ 0 := le_of_not_gt upward
    have height := P.upperHeight_ge_body N member
    have old := N.supporting f z member
    have first := Cap.horizontal_inner (N.normal f) z
    have last := Cap.horizontal_inner (N.normal f) (P.upperPoint N (Cap.horizontal z))
    rw [P.horizontal_upperPoint, P.height_upperPoint] at last
    rw [inner_sub_right] at old ⊢
    have lowering := mul_nonpos_of_nonpos_of_nonneg nonpositive (sub_nonneg.mpr height)
    nlinarith

/-- The constructed graph is on the actual boundary and attains the upper end of each fiber. -/
theorem upperPoint_mem_frontier {p : Plane} (member : p ∈ P.bodyFootprint) :
    P.upperPoint N p ∈ frontier F.vertexHull := by
  have feasible := P.upperPoint_mem_body N member
  refine ⟨F.compact_vertexHull.isClosed.closure_eq.symm ▸ feasible, ?_⟩
  intro inside
  obtain ⟨f, equal⟩ := P.exists_upperHeight_eq N p
  have zero : inner ℝ (N.normal f.val) (P.upperPoint N p - F.place f.val 0) = 0 :=
    (N.on_support_iff f _).mpr (by
      rw [P.horizontal_upperPoint, P.height_upperPoint]
      exact equal)
  exact (N.supporting_strict f inside).ne zero

include P in
theorem convex_bodyFootprint : Convex ℝ P.bodyFootprint :=
  F.convex_vertexHull.linear_image Cap.horizontal

include P in
theorem compact_bodyFootprint : IsCompact P.bodyFootprint :=
  F.compact_vertexHull.image Cap.horizontalCLM.continuous

include P in
theorem interior_bodyFootprint : (interior P.bodyFootprint).Nonempty := by
  obtain ⟨c, inside⟩ := P.interior_nonempty
  obtain ⟨r, positive, contained⟩ := Metric.isOpen_iff.mp isOpen_interior c inside
  refine ⟨Cap.horizontal c, mem_interior_iff_mem_nhds.mpr ?_⟩
  apply Metric.mem_nhds_iff.mpr
  refine ⟨r, positive, ?_⟩
  intro p near
  let z := Cap.horizontalLift (p - Cap.horizontal c) + c
  have distance : dist z c = dist p (Cap.horizontal c) := by
    rw [dist_eq_norm, dist_eq_norm]
    change ‖Cap.horizontalLift (p - Cap.horizontal c) + c - c‖ = _
    rw [add_sub_cancel_right, Cap.horizontalLift_norm]
  have feasible : z ∈ F.vertexHull := interior_subset (contained (by
    rw [Metric.mem_ball, distance]
    exact near))
  refine ⟨z, feasible, ?_⟩
  change Cap.horizontal (Cap.horizontalLift (p - Cap.horizontal c) + c) = p
  rw [map_add]
  have lifted (v : Plane) : Cap.horizontal (Cap.horizontalLift v) = v := by
    ext i
    fin_cases i <;> rfl
  rw [lifted, sub_add_cancel]

end Unfoldings.SpatialFolding.ConvexBoundary
