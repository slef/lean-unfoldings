module

public import Unfoldings.Roof.Fenchel

/-! Original supporting faces recovered from finite primal contact hulls. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexRoof C)

theorem dualPoint_mem_footprint (i : Face × Fin 3) : K.dualPoint i ∈ K.footprint :=
  ⟨_, Set.mem_iUnion.mpr ⟨i.1, (C.triangle i.1).vertex i.2,
    (C.triangle i.1).vertex_mem i.2, rfl⟩, rfl⟩

theorem dualPoint_roofHeight (i : Face × Fin 3) :
    K.roofHeight (K.dualPoint i) = -K.dualLevel i := by
  dsimp only [dualLevel]
  rw [neg_neg]
  exact K.roofHeight_face i.1
    ⟨(C.triangle i.1).vertex i.2, (C.triangle i.1).vertex_mem i.2⟩

theorem dualFace_subset_footprint (s : Plane) (c : ℝ) :
    FiniteDual.face K.dualPoint K.dualLevel s c ⊆ K.footprint := by
  apply convexHull_min ?_ K.convex_projection
  rintro _ ⟨i, rfl, _⟩
  exact K.dualPoint_mem_footprint i

/-- The contact hull has exactly the original graph height, for every supporting slope,
including slopes in the unbounded normal cones at original rim vertices. -/
theorem roofHeight_on_dualFace {s x : Plane} {c : ℝ}
    (dual : K.dualCost s = -c)
    (member : x ∈ FiniteDual.face K.dualPoint K.dualLevel s c) :
    -K.roofHeight x = inner ℝ x s + c := by
  have concave := K.roofHeight_concave.add
    ((innerSL ℝ s).toLinearMap.concaveOn convex_univ)
  have convex : Convex ℝ {y : Plane | -c ≤ K.roofHeight y + inner ℝ s y} := by
    simpa only [Set.mem_univ, true_and, Pi.add_apply, ContinuousLinearMap.coe_coe,
      innerSL_apply_apply]
      using concave.convex_ge (-c)
  have bound : -c ≤ K.roofHeight x + inner ℝ s x := by
    apply convexHull_min (t := {y : Plane | -c ≤ K.roofHeight y + inner ℝ s y}) ?_
      convex member
    rintro _ ⟨i, rfl, equal⟩
    change -c ≤ K.roofHeight (K.dualPoint i) + inner ℝ s (K.dualPoint i)
    rw [K.dualPoint_roofHeight, equal]
    linarith [real_inner_comm s (K.dualPoint i)]
  have lower := K.fenchel_inequality (K.dualFace_subset_footprint s c member) s
  rw [dual] at lower
  linarith [real_inner_comm s x]

/-- An interior active clipped slope lies on the original roof over its actual domain. -/
theorem clippedExtension_interior_active_original {slopes : Set Plane}
    (compact : IsCompact slopes) (nonempty : slopes.Nonempty) {x p : Plane}
    (active : (K.clippedExtension slopes compact nonempty).Active x p)
    (inside : p ∈ interior slopes) :
    x ∈ K.footprint ∧ (K.clippedExtension slopes compact nonempty).height x =
      -K.roofHeight x := by
  let := K.nonempty_face
  have member := FiniteDual.mem_face_of_interior_maximizer K.dualPoint K.dualLevel inside
    (fun q hq => (active.2 ▸ (K.clippedExtension slopes compact nonempty).affine_le x hq))
  change x ∈ FiniteDual.face K.dualPoint K.dualLevel p (-K.dualCost p) at member
  have height := K.roofHeight_on_dualFace (s := p) (c := -K.dualCost p)
    (by rw [neg_neg]) member
  refine ⟨K.dualFace_subset_footprint _ _ member, ?_⟩
  rw [active.2]
  change inner ℝ x p - K.dualCost p = _
  linarith

end Unfoldings.ConvexRoof
