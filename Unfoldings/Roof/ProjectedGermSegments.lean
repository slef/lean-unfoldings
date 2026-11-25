module

public import Unfoldings.Roof.ProjectedBankOrientation
public import Unfoldings.Roof.ProjectedConformity
public import Unfoldings.Roof.OpenSeamInterior
public import Unfoldings.Geometry.AffineSupportBoundary
public import Unfoldings.Geometry.RayAvoidance
public import Unfoldings.Geometry.SpatialEnvelopeOpenSeams

/-! Projected bank germs follow complete original edges with strictly signed incident interior. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexRoof C)

def projectedGermStart (p : C.Germ) : Plane := (K.projectedTriangle p.1.1).vertex p.1.2

def projectedGermFinish (p : C.Germ) : Plane :=
  (K.projectedTriangle p.1.1).vertex (C.germFarCorner p).2

theorem projectedGermStart_mate (p : C.Germ) :
    K.projectedGermStart (C.mateGerm Set.univ p) = K.projectedGermStart p := by
  let w := C.vertexOfCorner Set.univ p.1
  let x : C.LinkGerm Set.univ w := ⟨p, rfl⟩
  exact (K.projectedGerm_apex (C.linkMate Set.univ w x)).trans (K.projectedGerm_apex x).symm

theorem projectedGermFinish_mate (p : C.Germ) :
    K.projectedGermFinish (C.mateGerm Set.univ p) = K.projectedGermFinish p :=
  congrArg Cap.horizontal (K.folding.germFarPoint_mate Set.univ p)

/-- The directed projected germ names an actual original edge in either traversal. -/
theorem projectedGerm_segment_eq (p : C.Germ) :
    segment ℝ (K.projectedGermStart p) (K.projectedGermFinish p) =
      (K.projectedTriangle p.1.1).edge (C.germEdge p).edge := by
  obtain ⟨⟨f, i⟩, side⟩ := p
  cases side
  · rfl
  · fin_cases i <;> exact segment_symm ℝ _ _

theorem projectedGerm_segment_disjoint_interior (p : C.Germ) (f : Face) :
    Disjoint (interior (K.projectedTriangle f).carrier)
      (segment ℝ (K.projectedGermStart p) (K.projectedGermFinish p)) := by
  rw [K.projectedGerm_segment_eq]
  apply Set.disjoint_left.mpr
  intro z inside on_edge
  by_cases same : f = p.1.1
  · exact (K.projectedTriangle f).not_mem_interior_of_mem_edge (C.germEdge p).edge
      (same.symm ▸ on_edge) inside
  rcases K.projectedTriangles_conforming f p.1.1 same z
    ⟨interior_subset inside, (K.projectedTriangle p.1.1).edge_subset _ on_edge⟩ with
    vertices | ⟨j, _, _, edge⟩
  · obtain ⟨j, equal⟩ := vertices.1
    exact (K.projectedTriangle f).not_mem_interior_of_mem_edge j
      (equal ▸ left_mem_segment ℝ _ _) inside
  · exact (K.projectedTriangle f).not_mem_interior_of_mem_edge j edge inside

/-- The open segment of a projected germ is the open part of its original edge. -/
theorem projectedGerm_openSegment_eq (p : C.Germ) : openSegment ℝ (K.projectedGermStart p) (K.projectedGermFinish p) =
      openSegment ℝ ((K.projectedTriangle p.1.1).vertex (C.germEdge p).edge)
        ((K.projectedTriangle p.1.1).vertex (Triangle.next (C.germEdge p).edge)) := by
  obtain ⟨⟨f, j⟩, side⟩ := p
  cases side
  · rfl
  · fin_cases j <;> exact openSegment_symm ℝ _ _

/-- The interior of a genuine projected seam lies in the interior of the roof. -/
theorem projectedOpenGermSegment_subset_interior (p : C.Germ)
    (internal : ¬ C.IsBoundaryEdge Set.univ (C.germEdge p)) :
    openSegment ℝ (K.projectedGermStart p) (K.projectedGermFinish p) ⊆ interior K.footprint := by
  have on_left (s : C.Seam) (flag : Bool) :
      openSegment ℝ (K.projectedGermStart (C.germOfEndpoint (C.left s) flag))
        (K.projectedGermFinish (C.germOfEndpoint (C.left s) flag)) ⊆ interior K.footprint := by
    intro z hz
    rw [K.projectedGerm_openSegment_eq, C.germEdge_germOfEndpoint] at hz
    let left := C.left s
    change z ∈ openSegment ℝ ((K.projectedTriangle left.face).vertex left.edge)
      ((K.projectedTriangle left.face).vertex (Triangle.next left.edge)) at hz
    have proj : Cap.horizontal '' K.folding.openSeamImage s =
        openSegment ℝ ((K.projectedTriangle left.face).vertex left.edge)
          ((K.projectedTriangle left.face).vertex (Triangle.next left.edge)) :=
      image_openSegment ℝ Cap.horizontal.toAffineMap _ _
    obtain ⟨x, member, rfl⟩ := proj.symm.subset hz
    exact K.horizontal_openSeamImage_mem_interior s member
  obtain ⟨q, crossing⟩ := (C.exists_germCrosses_iff Set.univ p).mpr internal
  have across := C.mateGerm_of_crossing crossing
  obtain ⟨s, _, side, flag, source, target⟩ := crossing
  cases side
  · exact source.symm ▸ on_left s flag
  · rw [← K.projectedGermStart_mate p, ← K.projectedGermFinish_mate p, across, target]
    exact on_left s (C.acrossEndpoint s true flag)

/-- No original vertex lies strictly inside any original projected edge. -/
theorem projectedVertex_not_mem_openGermSegment (p : C.Germ) (w : C.Vertex Set.univ) :
    K.projectedVertex w ∉ openSegment ℝ (K.projectedGermStart p) (K.projectedGermFinish p) := by
  intro member
  have on_edge := openSegment_subset_segment ℝ _ _ member
  rw [K.projectedGerm_segment_eq] at on_edge
  obtain ⟨i, vertex⟩ := K.projected_corner_of_vertex_mem w p.1.1
    ((K.projectedTriangle p.1.1).edge_subset _ on_edge)
  rw [K.projectedGerm_openSegment_eq] at member
  exact (K.projectedTriangle p.1.1).not_isVertex_of_mem_openSegment _ member ⟨i, vertex⟩

/-- At every interior point of its incident triangle, a directed edge's area
has the same strict sign as the original third corner. -/
theorem projectedGerm_interior_orientation_mul_pos (p : C.Germ) {x : Plane}
    (inside : x ∈ interior (K.projectedTriangle p.1.1).carrier) :
    0 < K.projectedGermOrientation p *
      orient (K.projectedGermStart p) (K.projectedGermFinish p) x := by
  let O := K.projectedGermOrientation p
  let a := K.projectedGermStart p
  let b := K.projectedGermFinish p
  let h : Plane →ᵃ[ℝ] ℝ := O • orientMap a b
  have eval (z : Plane) : h z = O * orient a b z := by
    simp only [h, AffineMap.coe_smul, Pi.smul_apply, smul_eq_mul, orientMap_apply]
  have lower : (K.projectedTriangle p.1.1).carrier ⊆ {z | 0 ≤ h z} := by
    apply convexHull_min ?_ ((convex_Ici (0 : ℝ)).affine_preimage h)
    rintro z ⟨j, rfl⟩
    change 0 ≤ h ((K.projectedTriangle p.1.1).vertex j)
    rw [eval]
    obtain ⟨⟨f, i⟩, side⟩ := p
    cases side
    all_goals rcases Triangle.corner_cases i j with rfl | rfl | rfl
    all_goals
      simp only [a, b, O, projectedGermStart, projectedGermFinish, projectedGermOrientation,
        TriangleComplex.germFarCorner, TriangleComplex.turnGerm, Bool.not_true, Bool.not_false, Bool.false_eq_true,
        ite_true, ite_false, projectedTriangle, Triangle.affineImage_vertex,
        orient_self_left, orient_self_right, mul_zero, le_refl]
    all_goals exact mul_self_nonneg (_ : ℝ)
  have proper : h ≠ 0 := by
    let y := (K.projectedTriangle p.1.1).vertex (C.germFarCorner (C.turnGerm p)).2
    intro zero
    have value := DFunLike.congr_fun zero y
    change h y = 0 at value
    rw [eval] at value
    change O * O = 0 at value
    exact (mul_ne_zero (K.projectedGermOrientation_ne_zero p) (K.projectedGermOrientation_ne_zero p)) value
  have nonzero : h x ≠ 0 := fun zero =>
    not_mem_interior_of_affine_lower_bound h proper (fun _ hz => lower hz) zero inside
  exact (eval x) ▸ lt_of_le_of_ne (lower (interior_subset inside)) nonzero.symm

end Unfoldings.ConvexRoof
