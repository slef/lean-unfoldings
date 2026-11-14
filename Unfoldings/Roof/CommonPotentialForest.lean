module

public import Unfoldings.Roof.CommonPotentialStep
public import Unfoldings.Topology.SelectedForest
public import Unfoldings.Topology.ParentPaths

/-! Construct common-potential original-edge forests on selected whole-face patches. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexRoof C)

/-- Constructed routing data; roots are exactly vertices outside the patch interior.
Vertices outside the closed patch are isolated roots and contribute no selected edge. -/
structure CommonPotentialRouting (U : Set Face) (E : SlopeEnvelope) (a β : ℝ) where
  parents : AscendingParents (C.Vertex Set.univ)
  roots_eq : parents.roots = {v | K.projectedVertex v ∉ interior (K.restrictedCarrier U)}
  height_eq : parents.height = fun v => E.height (K.projectedVertex v)
  selection : parents.EdgeSelection C.seamGraph
  step : ∀ v ∉ parents.roots, ∃ p, E.Active (K.projectedVertex v) p ∧
    InnerProductGeometry.angle p (K.projectedVertex (parents.parent v) - K.projectedVertex v) ≤ β ∧
    (a * Real.cos β) * ‖K.projectedVertex (parents.parent v) - K.projectedVertex v‖ ≤
      E.height (K.projectedVertex (parents.parent v)) - E.height (K.projectedVertex v) ∧
    K.projectedVertex (parents.parent v) ∈ K.restrictedCarrier U

open Classical in
/-- Local geometry constructs the parents and original named edges. Strict potential
progress proves acyclicity; no forest or parent map is supplied to the construction. -/
theorem exists_commonPotentialRouting (U : Set Face) (E : SlopeEnvelope) {a β : ℝ}
    (positive : 0 < a) (beta : 0 ≤ β) (acute : β < Real.pi / 2)
    (lower : ∀ p ∈ E.slopes, a ≤ ‖p‖)
    (angles : ∀ f ∈ U, ∀ i, (K.projectedTriangle f).cornerAngle i ≤ 2 * β) :
    Nonempty (K.CommonPotentialRouting U E a β) := by
  let roots : Set (C.Vertex Set.univ) :=
    {v | K.projectedVertex v ∉ interior (K.restrictedCarrier U)}
  have outgoing (v : {v : C.Vertex Set.univ // v ∉ roots}) :=
    K.exists_commonPotential_seam_step U E positive beta acute.le lower angles v.val
      (not_not.mp v.property)
  choose next edge slope link different active close progress endpoint using outgoing
  have gain : 0 < a * Real.cos β :=
    mul_pos positive (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], acute⟩)
  let parents : AscendingParents (C.Vertex Set.univ) := {
    roots := roots
    parent v := if root : v ∈ roots then v else next ⟨v, root⟩
    height v := E.height (K.projectedVertex v)
    fixed_root v root := dite_eq_left root
    ascending v nonroot := by
      rw [dite_eq_right nonroot]
      have strict : 0 < ‖K.projectedVertex (next ⟨v, nonroot⟩) - K.projectedVertex v‖ :=
        norm_pos_iff.mpr (sub_ne_zero.mpr (K.projectedVertex_injective.ne (different ⟨v, nonroot⟩)))
      have bound := progress ⟨v, nonroot⟩
      linarith [mul_pos gain strict] }
  let selection : parents.EdgeSelection C.seamGraph := {
    edge v := edge ⟨v.val, v.property⟩
    link v := by
      change C.seamGraph.IsLink (edge ⟨v.val, v.property⟩) v.val
        (if root : v.val ∈ roots then v.val else next ⟨v.val, root⟩)
      rw [dite_eq_right v.property]
      exact link ⟨v.val, v.property⟩ }
  refine ⟨⟨parents, rfl, rfl, selection, ?_⟩⟩
  intro v nonroot
  change v ∉ roots at nonroot
  refine ⟨slope ⟨v, nonroot⟩, active ⟨v, nonroot⟩, ?_⟩
  simp only [parents, dite_eq_right nonroot]
  exact ⟨close ⟨v, nonroot⟩, progress ⟨v, nonroot⟩, endpoint ⟨v, nonroot⟩⟩

namespace CommonPotentialRouting

variable {K} {U : Set Face} {E : SlopeEnvelope} {a β : ℝ}
  (R : K.CommonPotentialRouting U E a β)

theorem rootedForest : R.selection.graph.IsRootedForest R.parents.roots :=
  R.selection.graph_rootedForest

theorem parent_stays {v : C.Vertex Set.univ}
    (member : K.projectedVertex v ∈ K.restrictedCarrier U) :
    K.projectedVertex (R.parents.parent v) ∈ K.restrictedCarrier U := by
  by_cases root : v ∈ R.parents.roots
  · rwa [R.parents.fixed_root v root]
  · obtain ⟨_, _, _, _, endpoint⟩ := R.step v root
    exact endpoint

theorem ancestor_stays {v w : C.Vertex Set.univ}
    (member : K.projectedVertex v ∈ K.restrictedCarrier U) (ancestor : R.parents.Ancestor v w) :
    K.projectedVertex w ∈ K.restrictedCarrier U := by
  obtain ⟨n, rfl⟩ := ancestor
  induction n with
  | zero => exact member
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact R.parent_stays ih

/-- Every selected patch vertex reaches an actual boundary root in this original-edge forest. -/
theorem root_mem_frontier {v : C.Vertex Set.univ}
    (member : K.projectedVertex v ∈ K.restrictedCarrier U) :
    K.projectedVertex (R.parents.root v) ∈ frontier (K.restrictedCarrier U) := by
  refine ⟨subset_closure (R.ancestor_stays member (R.parents.ancestor_root v)), ?_⟩
  have root := R.parents.root_mem v
  rwa [R.roots_eq] at root

/-- Exactly one boundary root lies in each restricted tree; outside isolated vertices
are absent from this statement. -/
theorem exists_unique_boundary_root {v : C.Vertex Set.univ}
    (member : K.projectedVertex v ∈ K.restrictedCarrier U) :
    ∃! r, K.projectedVertex r ∈ frontier (K.restrictedCarrier U) ∧
      R.selection.graph.Reaches v r := by
  let r := R.parents.root v
  have rroot := R.parents.root_mem v
  have reaches := R.selection.reaches_of_ancestor (R.parents.ancestor_root v)
  refine ⟨r, ⟨R.root_mem_frontier member, reaches⟩, ?_⟩
  intro s hs
  have sroot : s ∈ R.parents.roots := by
    rw [R.roots_eq]
    exact hs.1.2
  obtain ⟨q, _hq, unique⟩ := R.rootedForest.2 v (Set.mem_univ _)
  exact (unique s ⟨sroot, hs.2⟩).trans (unique r ⟨rroot, reaches⟩).symm

end CommonPotentialRouting
end Unfoldings.ConvexRoof
