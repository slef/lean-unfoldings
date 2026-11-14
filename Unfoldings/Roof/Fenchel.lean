module

public import Unfoldings.Roof.ClippedExtension
public import Unfoldings.Roof.NormalImage

/-! Fenchel equality and the full original normal cells, including the domain boundary. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexRoof C)

/-- Full subgradient of the convex roof function with its actual compact footprint domain.
At the rim this includes the domain's unbounded outward normal cone. -/
def primalNormalCell (x : Plane) : Set Plane :=
  {p | ∀ y ∈ K.footprint,
    inner ℝ y p - inner ℝ x p ≤ -K.roofHeight y + K.roofHeight x}

theorem fenchel_inequality {x : Plane} (member : x ∈ K.footprint) (p : Plane) :
    inner ℝ x p - K.dualCost p ≤ -K.roofHeight x := by
  let := K.nonempty_face
  obtain ⟨z, surface, projection⟩ := member
  obtain ⟨f, y, hy, equal⟩ := Set.mem_iUnion.mp surface
  have on_face : x ∈ (K.projectedTriangle f).carrier := by
    rw [projectedTriangle, Triangle.affineImage_carrier]
    exact ⟨y, hy, (congrArg Cap.horizontal equal).trans projection⟩
  have bound := FiniteDual.affine_le_on_face K.dualPoint K.dualLevel
    (K.projectedTriangle_subset_dualFace f on_face) p
  change inner ℝ x p - K.dualCost p ≤ _ at bound
  rw [K.roofHeight_eq_supportHeight_of_mem_projectedTriangle f on_face,
    K.supportHeight_gradient]
  linarith

theorem primalNormalCell_iff_dual {x : Plane} (member : x ∈ K.footprint) (p : Plane) :
    p ∈ K.primalNormalCell x ↔ K.dualCost p = inner ℝ x p + K.roofHeight x := by
  let := K.nonempty_face
  constructor
  · intro support
    apply le_antisymm
    · apply FiniteDual.cost_le
      intro i
      have in_face : K.dualPoint i ∈ K.footprint :=
        ⟨_, Set.mem_iUnion.mpr ⟨i.1, (C.triangle i.1).vertex i.2,
          (C.triangle i.1).vertex_mem i.2, rfl⟩, rfl⟩
      have bound := support _ in_face
      have height := K.roofHeight_face i.1
        ⟨(C.triangle i.1).vertex i.2, (C.triangle i.1).vertex_mem i.2⟩
      have vertex_height : K.roofHeight (K.dualPoint i) = -K.dualLevel i := by
        dsimp only [dualLevel]
        rw [neg_neg]
        exact height
      rw [vertex_height] at bound
      linarith
    · linarith [K.fenchel_inequality member p]
  · intro equal y hy
    have bound := K.fenchel_inequality hy p
    rw [equal] at bound
    linarith

theorem original_slope_mem_primalNormalCell (f : Face) {x : Plane}
    (member : x ∈ (K.projectedTriangle f).carrier) :
    K.normalSlope f ∈ K.primalNormalCell x := by
  intro y _hy
  have support := K.normalSlope_supports
    (K.roofHeight_eq_supportHeight_of_mem_projectedTriangle f member).symm y
  rw [inner_sub_right] at support
  have first : inner ℝ (K.normalSlope f) y = inner ℝ y (K.normalSlope f) :=
    real_inner_comm _ _
  have last : inner ℝ (K.normalSlope f) x = inner ℝ x (K.normalSlope f) :=
    real_inner_comm _ _
  rw [first, last] at support
  linarith

theorem convex_primalNormalCell (x : Plane) : Convex ℝ (K.primalNormalCell x) := by
  have equation : K.primalNormalCell x = ⋂ y ∈ K.footprint,
      {p | inner ℝ (y - x) p ≤ -K.roofHeight y + K.roofHeight x} := by
    ext p
    simp only [primalNormalCell, Set.mem_ofPred_eq, Set.mem_iInter, inner_sub_left]
  rw [equation]
  apply convex_iInter
  intro y
  apply convex_iInter
  intro _
  exact convex_halfSpace_le (innerSL ℝ (y - x)).toLinearMap.isLinear _

theorem primalNormalCell_nonempty {x : Plane} (member : x ∈ K.footprint) :
    (K.primalNormalCell x).Nonempty := by
  rw [K.footprint_eq_union_projectedTriangles] at member
  obtain ⟨f, hf⟩ := Set.mem_iUnion.mp member
  exact ⟨K.normalSlope f, K.original_slope_mem_primalNormalCell f hf⟩

end Unfoldings.ConvexRoof
