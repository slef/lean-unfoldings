module

public import Unfoldings.Roof.AdaptivePotentialStep
public import Unfoldings.Topology.SelectedForest
public import Unfoldings.Topology.ParentPaths

/-! Original-edge forests whose parent paths preserve the progress-body invariant. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof

open InnerProductGeometry

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexRoof C)

/-- Each nonroot follows an original seam with progress on every partial edge and
a radial margin uniform over all admissible histories arriving at the vertex. -/
structure AdaptivePotentialRouting (U : Set Face) (E : SlopeEnvelope) (L : Set Plane)
    (r margin : ℝ) where
  parents : AscendingParents (C.Vertex Set.univ)
  roots_eq : parents.roots = {v | K.projectedVertex v ∉ interior (K.restrictedCarrier U)}
  height_eq : parents.height = fun v => E.height (K.projectedVertex v)
  selection : parents.EdgeSelection C.seamGraph
  endpoint : ∀ v ∉ parents.roots, K.projectedVertex (parents.parent v) ∈ K.restrictedCarrier U
  ascent : ∀ v ∉ parents.roots,
    r * ‖K.projectedVertex (parents.parent v) - K.projectedVertex v‖ ≤
      E.height (K.projectedVertex (parents.parent v)) - E.height (K.projectedVertex v)
  along : ∀ v ∉ parents.roots,
    let x := K.projectedVertex v
    let d := K.projectedVertex (parents.parent v) - x
    ∀ a b : ℝ, 0 ≤ a → a ≤ b → E.HistoryProgress L (x + a • d) (x + b • d)
  radial : ∀ v ∉ parents.roots,
    let x := K.projectedVertex v
    let d := K.projectedVertex (parents.parent v) - x
    ∀ q : Plane, E.HistoryProgress L q x → ∀ t : ℝ, 0 ≤ t →
      margin * (‖x + t • d - q‖ * ‖d‖) ≤ inner ℝ (x + t • d - q) d

open Classical in
/-- Active slopes determine headings at the original mesh vertices. Selecting
an edge nearest each heading produces a rooted forest by strict ascent. -/
theorem exists_adaptivePotentialRouting (U : Set Face) (E : SlopeEnvelope) (L : Set Plane)
    {r θ maxWidth : ℝ} (positive : 0 < r) (disk : Metric.closedBall (0 : Plane) r ⊆ L)
    (nonnegative : 0 ≤ θ) (acute : (maxWidth + θ) / 2 < Real.pi / 2)
    (angles : ∀ f ∈ U, ∀ i, (K.projectedTriangle f).cornerAngle i ≤ θ)
    (cones : ∀ p ∈ E.slopes, ∃ (axis : Plane) (width : ℝ),
      axis ≠ 0 ∧ θ ≤ width ∧ width ≤ maxWidth ∧
        ∀ z : Plane, z ≠ 0 → (z ∈ SlopeEnvelope.historyCone L p ↔ angle axis z ≤ width / 2)) :
    Nonempty (K.AdaptivePotentialRouting U E L r (Real.cos ((maxWidth + θ) / 2))) := by
  let roots : Set (C.Vertex Set.univ) :=
    {v | K.projectedVertex v ∉ interior (K.restrictedCarrier U)}
  have outgoing (v : {v : C.Vertex Set.univ // v ∉ roots}) :
      ∃ (w : C.Vertex Set.univ) (s : C.Seam),
        C.seamGraph.IsLink s v.val w ∧ w ≠ v.val ∧ K.projectedVertex w ∈ K.restrictedCarrier U ∧
        let x := K.projectedVertex v.val
        let d := K.projectedVertex w - x
        (r * ‖d‖ ≤ E.height (K.projectedVertex w) - E.height x) ∧
        (∀ a b : ℝ, 0 ≤ a → a ≤ b → E.HistoryProgress L (x + a • d) (x + b • d)) ∧
        ∀ q : Plane, E.HistoryProgress L q x → ∀ t : ℝ, 0 ≤ t →
          Real.cos ((maxWidth + θ) / 2) * (‖x + t • d - q‖ * ‖d‖) ≤
            inner ℝ (x + t • d - q) d := by
    obtain ⟨p, active⟩ := E.exists_active (K.projectedVertex v.val)
    obtain ⟨axis, width, axis_ne, wide, bounded, cone⟩ := cones p active.1
    have width_acute : (width + θ) / 2 < Real.pi / 2 :=
      (by linarith : (width + θ) / 2 ≤ (maxWidth + θ) / 2).trans_lt acute
    obtain ⟨w, s, link, different, endpoint, ascent, along, radial⟩ :=
      K.exists_adaptivePotential_seam_step U E L positive disk nonnegative wide width_acute
        angles v.val (not_not.mp v.property) active axis_ne cone
    have margin := Real.cos_le_cos_of_nonneg_of_le_pi
      (show 0 ≤ (width + θ) / 2 by linarith)
      (show (maxWidth + θ) / 2 ≤ Real.pi by linarith [Real.pi_pos])
      (show (width + θ) / 2 ≤ (maxWidth + θ) / 2 by linarith)
    refine ⟨w, s, link, different, endpoint, ascent, along, ?_⟩
    intro q history t ht
    exact (mul_le_mul_of_nonneg_right margin (mul_nonneg (norm_nonneg _) (norm_nonneg _))).trans
      (radial q history t ht)
  choose next seam link different endpoint ascent along radial using outgoing
  let parents : AscendingParents (C.Vertex Set.univ) := {
    roots := roots
    parent v := if root : v ∈ roots then v else next ⟨v, root⟩
    height v := E.height (K.projectedVertex v)
    fixed_root v root := dite_eq_left root
    ascending v nonroot := by
      rw [dite_eq_right nonroot]
      have strict : 0 < ‖K.projectedVertex (next ⟨v, nonroot⟩) - K.projectedVertex v‖ :=
        norm_pos_iff.mpr (sub_ne_zero.mpr (K.projectedVertex_injective.ne (different ⟨v, nonroot⟩)))
      linarith [ascent ⟨v, nonroot⟩, mul_pos positive strict] }
  let selection : parents.EdgeSelection C.seamGraph := {
    edge v := seam ⟨v.val, v.property⟩
    link v := by
      change C.seamGraph.IsLink (seam ⟨v.val, v.property⟩) v.val
        (if root : v.val ∈ roots then v.val else next ⟨v.val, root⟩)
      rw [dite_eq_right v.property]
      exact link ⟨v.val, v.property⟩ }
  refine ⟨⟨parents, rfl, rfl, selection, ?_, ?_, ?_, ?_⟩⟩
  · intro v nonroot
    simpa only [parents, dite_eq_right nonroot] using endpoint ⟨v, nonroot⟩
  · intro v nonroot
    simpa only [parents, dite_eq_right nonroot] using ascent ⟨v, nonroot⟩
  · intro v nonroot
    simpa only [parents, dite_eq_right nonroot] using along ⟨v, nonroot⟩
  · intro v nonroot
    simpa only [parents, dite_eq_right nonroot] using radial ⟨v, nonroot⟩

namespace AdaptivePotentialRouting

variable {K} {U : Set Face} {E : SlopeEnvelope} {L : Set Plane} {r margin : ℝ}
  (R : K.AdaptivePotentialRouting U E L r margin)

theorem rootedForest : R.selection.graph.IsRootedForest R.parents.roots :=
  R.selection.graph_rootedForest

theorem parent_stays {v : C.Vertex Set.univ}
    (member : K.projectedVertex v ∈ K.restrictedCarrier U) :
    K.projectedVertex (R.parents.parent v) ∈ K.restrictedCarrier U := by
  by_cases root : v ∈ R.parents.roots
  · rwa [R.parents.fixed_root v root]
  · exact R.endpoint v root

theorem parent_progress (v : C.Vertex Set.univ) :
    E.HistoryProgress L (K.projectedVertex v) (K.projectedVertex (R.parents.parent v)) := by
  by_cases root : v ∈ R.parents.roots
  · rw [R.parents.fixed_root v root]
    exact SlopeEnvelope.HistoryProgress.refl E _
  · have along := R.along v root 0 1 le_rfl zero_le_one
    have endpoint : K.projectedVertex v +
        (1 : ℝ) • (K.projectedVertex (R.parents.parent v) - K.projectedVertex v) =
          K.projectedVertex (R.parents.parent v) := by rw [one_smul]; abel
    simpa only [zero_smul, add_zero, endpoint] using along

/-- Progress is inherited by any ancestor and by any history reaching the start. -/
theorem ancestor_progress {v w : C.Vertex Set.univ} (ancestor : R.parents.Ancestor v w) :
    E.HistoryProgress L (K.projectedVertex v) (K.projectedVertex w) := by
  obtain ⟨n, rfl⟩ := ancestor
  induction n with
  | zero => exact SlopeEnvelope.HistoryProgress.refl E _
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact SlopeEnvelope.HistoryProgress.trans E ih (R.parent_progress _)

theorem root_mem_frontier {v : C.Vertex Set.univ}
    (member : K.projectedVertex v ∈ K.restrictedCarrier U) :
    K.projectedVertex (R.parents.root v) ∈ frontier (K.restrictedCarrier U) := by
  have stays (n : ℕ) : K.projectedVertex (R.parents.parent^[n] v) ∈ K.restrictedCarrier U := by
    induction n with
    | zero => exact member
    | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact R.parent_stays ih
  have root := R.parents.root_mem v
  rw [R.roots_eq] at root
  have root_stays := stays (R.parents.distanceToRoot v)
  rw [R.parents.iterate_distanceToRoot_eq_root] at root_stays
  exact ⟨subset_closure root_stays, root⟩

end AdaptivePotentialRouting
end Unfoldings.ConvexRoof
