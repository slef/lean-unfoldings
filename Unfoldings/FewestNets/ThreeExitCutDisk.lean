module

public import Unfoldings.FewestNets.ThreeExitPlane
public import Unfoldings.Roof.CompatibleComponentCutDisk

/-! Three-exit parent choices cut the selected component to a disk along original seams. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof

open FewestNets

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  (K : ConvexRoof C) {slopes : Set Plane} (seed : Face)

local notation "U" => K.selectionComponent slopes seed
local notation "S" => K.restrictedCarrier U
local notation "V" => {v : C.Vertex Set.univ // K.projectedVertex v ∈ S}

/-- The data for two possible upward original-edge parents at each interior vertex,
with compatible exit directions at the actual boundary roots. -/
structure ThreeExitComponentChoices where
  choice : ThreeExitChoices V
  roots_eq : choice.boundary = {v | K.projectedVertex v.val ∈ frontier S}
  eastEdge : {v // v ∉ choice.boundary} → C.Seam
  westEdge : {v // v ∉ choice.boundary} → C.Seam
  east_link : ∀ v, C.seamGraph.IsLink (eastEdge v) v.val.val (choice.eastParent v.val).val
  west_link : ∀ v, C.seamGraph.IsLink (westEdge v) v.val.val (choice.westParent v.val).val

namespace ThreeExitComponentChoices

variable {K seed} (R : K.ThreeExitComponentChoices (slopes := slopes) seed)

open Classical in
/-- Name the original seam selected by the reachability assignment. -/
def edge (v : {v // v ∉ R.choice.parents.roots}) : C.Seam :=
  if R.choice.choosesEast v.val then R.eastEdge v else R.westEdge v

theorem edge_link (v : {v // v ∉ R.choice.parents.roots}) :
    C.seamGraph.IsLink (R.edge v) v.val.val (R.choice.parents.parent v.val).val := by
  classical
  unfold edge
  rw [R.choice.parent_eq v.val v.property]
  by_cases east : R.choice.choosesEast v.val
  · simpa only [ite_eq_left east] using R.east_link v
  · simpa only [ite_eq_right east] using R.west_link v

open Classical in
/-- The original seam selection admits a disk realization. The compatible
exterior continuations are used separately in the planar development. -/
theorem cut_disk (convex : Convex ℝ slopes) (closed : IsClosed slopes)
    (selected : K.normalSlope seed ∈ slopes) :
    Nonempty ((C.restrictFaces U).Realization
      {s : (C.restrictFaces U).Seam | s.val ∉ Set.range R.edge} ≃ₜ
        Metric.closedBall (0 : Plane) 1) :=
  K.exists_component_cut_disk_of_local_parents convex closed seed selected
    R.choice.parents R.roots_eq R.edge R.edge_link

end ThreeExitComponentChoices

end Unfoldings.ConvexRoof
