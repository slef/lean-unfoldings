module

public import Unfoldings.Roof.CompatiblePotentialHistories
public import Unfoldings.Convex.ExteriorDirectionAngle
public import Unfoldings.Geometry.AnnularRadialMargin

/-! Quantitative radial margins for every incoming history in the attached forest. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof.CompatiblePotentialRouting

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} {K : ConvexRoof C}
  {U : Set Face} {G : SlopeEnvelope} {boundary : (frontier G.slopes).Nonempty} {a β : ℝ}
  (R : K.CompatiblePotentialRouting U G boundary a β)

theorem parent_active_angle (positive : 0 < a) {b : ℝ} (bpos : 0 < b) (ratio : a ≤ b)
    (inner_disk : Metric.ball (0 : Plane) a ⊆ G.slopes)
    (upper : ∀ p ∈ G.slopes, ‖p‖ ≤ b) {v : C.Vertex Set.univ} (nonroot : v ∉ R.parents.roots) :
    ∃ p, (G.boundaryEnvelope boundary).Active (K.projectedVertex v) p ∧
      (InnerProductGeometry.angle p
        (K.projectedVertex (R.parents.parent v) - K.projectedVertex v) ≤ β ∨
      InnerProductGeometry.angle p
        (K.projectedVertex (R.parents.parent v) - K.projectedVertex v) ≤ Real.arccos (a / b)) := by
  by_cases root : v ∈ R.original.parents.roots
  · let r : {v // v ∈ R.original.parents.roots} := ⟨v, root⟩
    have not_terminal : r ∉ R.exterior.parents.roots := fun terminal => nonroot ⟨root, terminal⟩
    have contact := (R.exterior.next_spec not_terminal).1
    have active := G.active_boundary boundary (R.exterior.active r)
      (R.exterior.slope_mem_frontier r)
    rw [R.exterior_points] at active
    refine ⟨R.exterior.slope r, active, Or.inr ?_⟩
    have close := R.exterior.contact_angle_bound positive bpos ratio inner_disk upper contact
    simp only [R.exterior_points] at close
    have parent_eq := R.original.parents.attach_parent_root R.exterior.parents R.shared_height r
    change R.parents.parent v = (R.exterior.parents.parent r).val at parent_eq
    rw [parent_eq]
    exact close
  · obtain ⟨p, active, close, _progress, _endpoint⟩ := R.original.step v root
    exact ⟨p, active, Or.inl (by rwa [R.original_parent root])⟩

/-- The paper's explicit minimum margin works for every history at each finite merger.
The exterior direction bound is obtained from the actual slope annulus. -/
theorem history_radial_margin (positive : 0 < a) (beta : 0 ≤ β) (acute : β < Real.pi / 2)
    {b ζ : ℝ} (bpos : 0 < b) (ratio : a ≤ b)
    (inner_disk : Metric.ball (0 : Plane) a ⊆ G.slopes)
    (upper : ∀ p ∈ G.slopes, ‖p‖ ≤ b)
    (sector : Real.tan β < a / b) (zeta : 0 ≤ ζ) (direction : Real.arccos (a / b) ≤ ζ)
    (exterior : annularHistoryAngle (a / b) β + ζ < Real.pi / 2)
    (start : C.Vertex Set.univ) (n : ℕ)
    (nonroot : R.parents.parent^[n] start ∉ R.parents.roots)
    (different : R.parents.parent^[n] start ≠ start) :
    annularRadialMargin (a / b) β ζ *
      (‖K.projectedVertex (R.parents.parent^[n] start) - K.projectedVertex start‖ *
        ‖K.projectedVertex (R.parents.parent (R.parents.parent^[n] start)) -
          K.projectedVertex (R.parents.parent^[n] start)‖) ≤
      inner ℝ (K.projectedVertex (R.parents.parent^[n] start) - K.projectedVertex start)
        (K.projectedVertex (R.parents.parent (R.parents.parent^[n] start)) -
          K.projectedVertex (R.parents.parent^[n] start)) := by
  let v := R.parents.parent^[n] start
  let edge := K.projectedVertex (R.parents.parent v) - K.projectedVertex v
  have edge_ne : edge ≠ 0 := by
    intro zero
    have same := K.projectedVertex_injective (sub_eq_zero.mp zero)
    have strict := R.parents.ascending v nonroot
    rw [same] at strict
    exact lt_irrefl _ strict
  obtain ⟨p, active, close⟩ := R.parent_active_angle positive bpos ratio inner_disk upper nonroot
  have pne : p ≠ 0 := by
    intro zero
    have norm := G.boundary_norm_ge inner_disk active.1
    rw [zero, norm_zero] at norm
    linarith
  have coefficient : a * Real.cos β ≤ b :=
    (mul_le_of_le_one_right positive.le (Real.cos_le_one β)).trans ratio
  have gain : 0 ≤ a * Real.cos β :=
    mul_nonneg positive.le (Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], acute.le⟩)
  have expression : (a * Real.cos β) / b = (a / b) * Real.cos β := by ring
  have history := R.history_angle_bound positive beta acute.le inner_disk bpos coefficient upper
    start n active different
  rw [expression] at history
  change InnerProductGeometry.angle p (K.projectedVertex v - K.projectedVertex start) ≤
    annularHistoryAngle (a / b) β at history
  have angle : 0 ≤ annularHistoryAngle (a / b) β := Real.arccos_nonneg _
  have within := annular_history_angle_sector (div_pos positive bpos)
    ((div_le_one bpos).mpr ratio) beta acute sector
  have finish (δ : ℝ) (nonnegative : 0 ≤ δ)
      (small : annularHistoryAngle (a / b) β + δ < Real.pi / 2)
      (close : InnerProductGeometry.angle p edge ≤ δ)
      (margin : annularRadialMargin (a / b) β ζ ≤
        Real.cos (annularHistoryAngle (a / b) β + δ)) :
      annularRadialMargin (a / b) β ζ *
        (‖K.projectedVertex v - K.projectedVertex start‖ * ‖edge‖) ≤
          inner ℝ (K.projectedVertex v - K.projectedVertex start) edge := by
    have triangle := InnerProductGeometry.angle_le_angle_add_angle
      (K.projectedVertex v - K.projectedVertex start) p edge
    rw [InnerProductGeometry.angle_comm (K.projectedVertex v - K.projectedVertex start) p]
      at triangle
    have bound : InnerProductGeometry.angle (K.projectedVertex v - K.projectedVertex start) edge ≤
        annularHistoryAngle (a / b) β + δ := by linarith
    have scalar := (angle_le_iff_cos_mul_norm_le
      (K.projectedVertex_injective.ne different |> sub_ne_zero.mpr)
      edge_ne (add_nonneg angle nonnegative) (by linarith [Real.pi_pos])).mp bound
    exact (mul_le_mul_of_nonneg_right margin
      (mul_nonneg (norm_nonneg _) (norm_nonneg _))).trans scalar
  rcases close with close | close
  · apply finish β beta (by linarith) close
    exact (min_le_left _ _).trans_eq (by rw [add_comm])
  · exact finish ζ zeta exterior (close.trans direction) (min_le_right _ _)

end Unfoldings.ConvexRoof.CompatiblePotentialRouting
