module

public import Unfoldings.Roof.CommonPotentialStep
public import Unfoldings.Convex.HistoryCone

/-! Choose an original edge nearest the bisector of an adaptive history cone. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof

open InnerProductGeometry

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexRoof C)

open Classical in
/-- An interior selected vertex has an original seam within half the upper
corner-angle bound of any prescribed nonzero heading. -/
theorem exists_original_seam_near_heading (U : Set Face) {β : ℝ}
    (angles : ∀ f ∈ U, ∀ i, (K.projectedTriangle f).cornerAngle i ≤ 2 * β)
    (v : C.Vertex Set.univ) (inside : K.projectedVertex v ∈ interior (K.restrictedCarrier U))
    (axis : Plane) (genuine : axis ≠ 0) :
    ∃ (w : C.Vertex Set.univ) (s : C.Seam), C.seamGraph.IsLink s v w ∧ w ≠ v ∧
      angle axis (K.projectedVertex w - K.projectedVertex v) ≤ β ∧
      K.projectedVertex w ∈ K.restrictedCarrier U := by
  obtain ⟨f, i, vertex, forward⟩ := exists_mesh_direction_edge
    (fun f : U => K.projectedTriangle f.val) (K.restrictedCarrier U)
    Set.Subset.rfl (K.projectedVertex v) inside
    (fun f present => K.projected_corner_of_vertex_mem v f.val present)
    (fun f i => angles f.val f.property i) axis genuine
  have original : C.vertexOfCorner Set.univ (f.val, i) = v :=
    K.projectedVertex_injective vertex
  have nonboundary : ¬ C.IsBoundaryVertex Set.univ (C.vertexOfCorner Set.univ (f.val, i)) := by
    rw [original]
    exact (K.projectedVertex_mem_interior_iff v).mp
      (interior_mono (K.restrictedCarrier_subset_footprint U) inside)
  have edges := C.exists_seamGraph_link_at_interior_corner f.val i nonboundary
  have finish (j : Fin 3) (s : C.Seam) (different : j ≠ i)
      (link : C.seamGraph.IsLink s v (C.vertexOfCorner Set.univ (f.val, j)))
      (close : angle axis ((K.projectedTriangle f.val).vertex j - K.projectedVertex v) ≤ β) :
      ∃ (w : C.Vertex Set.univ) (s : C.Seam), C.seamGraph.IsLink s v w ∧ w ≠ v ∧
        angle axis (K.projectedVertex w - K.projectedVertex v) ≤ β ∧
        K.projectedVertex w ∈ K.restrictedCarrier U := by
    let w := C.vertexOfCorner Set.univ (f.val, j)
    have endpoint : K.projectedVertex w = (K.projectedTriangle f.val).vertex j :=
      K.projectedVertex_ofCorner f.val j
    refine ⟨w, s, link, ?_, endpoint.symm ▸ close, ?_⟩
    · intro same
      exact different ((K.projectedTriangle f.val).affineIndependent_vertices.injective
        (endpoint.symm.trans ((congrArg K.projectedVertex same).trans vertex.symm)))
    · exact Set.mem_iUnion.mpr ⟨f, endpoint.symm ▸ (K.projectedTriangle f.val).vertex_mem j⟩
  rcases forward with first | last
  · obtain ⟨s, link⟩ := edges.1
    rw [original] at link
    exact finish (Triangle.next i) s (by fin_cases i <;> decide) link first
  · obtain ⟨s, link⟩ := edges.2
    rw [original] at link
    exact finish (Triangle.next (Triangle.next i)) s (by fin_cases i <;> decide) link last

open Classical in
/-- The adaptive original edge advances the progress-body invariant on every
partial link and has the paper's margin with every incoming history. The cone
aperture is supplied as an angle characterization. -/
theorem exists_adaptivePotential_seam_step (U : Set Face) (E : SlopeEnvelope)
    (L : Set Plane) {r θ width : ℝ} (positive : 0 < r)
    (disk : Metric.closedBall (0 : Plane) r ⊆ L)
    (nonneg : 0 ≤ θ) (wide : θ ≤ width) (acute : (width + θ) / 2 < Real.pi / 2)
    (angles : ∀ f ∈ U, ∀ i, (K.projectedTriangle f).cornerAngle i ≤ θ)
    (v : C.Vertex Set.univ) (inside : K.projectedVertex v ∈ interior (K.restrictedCarrier U))
    {p axis : Plane} (active : E.Active (K.projectedVertex v) p) (axis_ne : axis ≠ 0)
    (cone : ∀ z : Plane, z ≠ 0 →
      (z ∈ SlopeEnvelope.historyCone L p ↔ angle axis z ≤ width / 2)) :
    ∃ (w : C.Vertex Set.univ) (s : C.Seam),
      C.seamGraph.IsLink s v w ∧ w ≠ v ∧ K.projectedVertex w ∈ K.restrictedCarrier U ∧
      let x := K.projectedVertex v
      let d := K.projectedVertex w - x
      (r * ‖d‖ ≤ E.height (K.projectedVertex w) - E.height x) ∧
      (∀ a b : ℝ, 0 ≤ a → a ≤ b → E.HistoryProgress L (x + a • d) (x + b • d)) ∧
      ∀ q : Plane, E.HistoryProgress L q x → ∀ t : ℝ, 0 ≤ t →
        Real.cos ((width + θ) / 2) * (‖x + t • d - q‖ * ‖d‖) ≤
          inner ℝ (x + t • d - q) d := by
  obtain ⟨w, s, link, different, close, member⟩ :=
    K.exists_original_seam_near_heading U (β := θ / 2)
      (fun f hf j => (angles f hf j).trans_eq (by ring)) v inside axis axis_ne
  let x := K.projectedVertex v
  let d := K.projectedVertex w - x
  have d_ne : d ≠ 0 := sub_ne_zero.mpr (K.projectedVertex_injective.ne different)
  obtain ⟨in_cone, margin⟩ :=
    SlopeEnvelope.historyCone_heading d_ne nonneg wide acute cone close
  have along (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) :
      E.HistoryProgress L (x + a • d) (x + b • d) :=
    E.historyProgress_ray active in_cone ha hab
  have endpoint : E.HistoryProgress L x (K.projectedVertex w) := by
    have h := along 0 1 le_rfl zero_le_one
    have end_eq : x + (1 : ℝ) • d = K.projectedVertex w := by
      rw [one_smul]
      dsimp [d]
      abel
    simpa only [end_eq, zero_smul, add_zero] using h
  refine ⟨w, s, link, different, member, SlopeEnvelope.HistoryProgress.norm_le E endpoint positive
    disk, along, ?_⟩
  intro q history t t_nonneg
  have first := margin (x - q) (SlopeEnvelope.HistoryProgress.mem_historyCone E history active)
  have nonnegative : 0 ≤ Real.cos ((width + θ) / 2) :=
    Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], acute.le⟩
  have later := inner_radial_margin_add_smul (x - q) d nonnegative (Real.cos_le_one _)
    t_nonneg first
  rw [show x + t • d - q = x - q + t • d by abel]
  exact later

end Unfoldings.ConvexRoof
