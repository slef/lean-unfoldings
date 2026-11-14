module

public import Unfoldings.Roof.CommonPotentialHistories
public import Unfoldings.Roof.SelectedStrictRegion
public import Unfoldings.Roof.ClippedExteriorRay
public import Unfoldings.Convex.ExteriorPieces
public import Unfoldings.Topology.AttachAscendingParents

/-! Construct and attach the original-edge and safe exterior forests of a clipped roof. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexRoof C)

structure CompatiblePotentialRouting (U : Set Face) (G : SlopeEnvelope)
    (boundary_nonempty : (frontier G.slopes).Nonempty) (a β : ℝ) where
  original : K.CommonPotentialRouting U (G.boundaryEnvelope boundary_nonempty) a β
  exterior : G.ExteriorPlan {v // v ∈ original.parents.roots}
  exterior_points : ∀ v, exterior.point v = K.projectedVertex v.val
  exterior_height : ∀ v : {v // v ∈ original.parents.roots},
    G.height (K.projectedVertex v.val) =
      (G.boundaryEnvelope boundary_nonempty).height (K.projectedVertex v.val)

open Classical in
/-- The input consists of the actual roof, compact convex slope clipping, and corner bounds
only on selected original faces. Both forests and their consistent exterior rays are constructed. -/
theorem exists_compatiblePotentialRouting {slopes : Set Plane} (convex : Convex ℝ slopes)
    (compact : IsCompact slopes) (nonempty : slopes.Nonempty)
    (origin : (0 : Plane) ∈ interior slopes) (boundary_nonempty : (frontier slopes).Nonempty)
    (no_boundary : ∀ f, K.normalSlope f ∉ frontier slopes) {a β : ℝ}
    (positive : 0 < a) (inner_disk : Metric.ball (0 : Plane) a ⊆ slopes)
    (beta : 0 ≤ β) (acute : β < Real.pi / 2)
    (angles : ∀ f, K.normalSlope f ∈ slopes →
      ∀ i, (K.projectedTriangle f).cornerAngle i ≤ 2 * β) :
    Nonempty (K.CompatiblePotentialRouting {f | K.normalSlope f ∈ slopes}
      (K.clippedExtension slopes compact nonempty) boundary_nonempty a β) := by
  let G := K.clippedExtension slopes compact nonempty
  let B := G.boundaryEnvelope boundary_nonempty
  let U : Set Face := {f | K.normalSlope f ∈ slopes}
  have lower : ∀ p ∈ B.slopes, a ≤ ‖p‖ :=
    fun _ hp => G.boundary_norm_ge inner_disk hp
  obtain ⟨I⟩ := K.exists_commonPotentialRouting U B positive beta acute lower angles
  have strict_iff (x : Plane) : B.height x < G.height x ↔ x ∈ interior (K.selectedCarrier slopes) :=
    (K.clippedExtension_strict_region_iff compact nonempty boundary_nonempty x).trans
      (K.interior_selectedCarrier_iff_normal_cell convex compact no_boundary x).symm
  have equal (v : {v // v ∈ I.parents.roots}) : G.height (K.projectedVertex v.val) =
      B.height (K.projectedVertex v.val) := by
    have outside : K.projectedVertex v.val ∉ interior (K.selectedCarrier slopes) := by
      exact (Set.ext_iff.mp I.roots_eq v.val).mp v.property
    exact le_antisymm (le_of_not_gt (fun strict => outside ((strict_iff _).mp strict)))
      (G.boundary_height_le boundary_nonempty _)
  obtain ⟨O, points⟩ := G.exists_exteriorPlan
    (fun v : {v // v ∈ I.parents.roots} => K.projectedVertex v.val)
    (K.projectedVertex_injective.comp Subtype.val_injective) convex origin boundary_nonempty
    (fun v => (equal v).symm)
  exact ⟨⟨I, O, fun v => congrFun points v, equal⟩⟩

namespace CompatiblePotentialRouting

variable {K} {U : Set Face} {G : SlopeEnvelope}
  {boundary_nonempty : (frontier G.slopes).Nonempty} {a β : ℝ}
  (R : K.CompatiblePotentialRouting U G boundary_nonempty a β)

theorem shared_height (v : {v // v ∈ R.original.parents.roots}) :
    R.exterior.parents.height v = R.original.parents.height v.val := by
  change G.height (R.exterior.point v) = R.original.parents.height v.val
  rw [R.exterior_points, R.original.height_eq]
  exact R.exterior_height v

/-- The complete finite parent forest keeps every original interior parent unchanged. -/
def parents : AscendingParents (C.Vertex Set.univ) :=
  R.original.parents.attach R.exterior.parents R.shared_height

theorem rootedForest : R.parents.graph.IsRootedForest R.parents.roots :=
  R.parents.graph_rootedForest

theorem original_parent {v : C.Vertex Set.univ} (interior : v ∉ R.original.parents.roots) :
    R.parents.parent v = R.original.parents.parent v :=
  R.original.parents.attach_parent_nonroot R.exterior.parents R.shared_height interior

/-- Every final component continues along an actual contact-free straight exterior ray. -/
theorem terminal_ray_no_contacts (v : C.Vertex Set.univ)
    (root : v ∈ R.parents.roots) (w : {v // v ∈ R.original.parents.roots}) {t : ℝ}
    (positive : 0 < t) :
    ∃ r : {v // v ∈ R.original.parents.roots}, r.val = v ∧
      R.exterior.ray r t ≠ K.projectedVertex w.val := by
  obtain ⟨original_root, terminal⟩ := root
  let r : {v // v ∈ R.original.parents.roots} := ⟨v, original_root⟩
  refine ⟨r, rfl, ?_⟩
  intro equal
  apply terminal
  refine ⟨w, t, positive, ?_⟩
  rw [R.exterior_points]
  exact equal.symm

end CompatiblePotentialRouting
end Unfoldings.ConvexRoof
