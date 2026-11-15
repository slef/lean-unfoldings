module

public import Unfoldings.Geometry.HingeSweepContinuity

/-! Actual outward hinge gaps have product coordinates beyond the source-centered hinge circle. -/

@[expose] public section

noncomputable section

open scoped NNReal

namespace Unfoldings.PolygonalRay

variable {n : ℕ} (R : PolygonalRay ℂ n) (hinge : Fin (n + 1)) (nonzero : R.direction ≠ 0)
  (angle : ℝ) (radial : ∀ θ ∈ Set.Icc 0 angle, (R.rotateSuffix hinge θ).Outward)
  (outward : (R.suffix hinge).Outward)

/-- These are coordinates on the actual unbounded gap, with the original source as radial center.
The common hinge is excluded; each remaining point has a unique real angle and radius. -/
def hingeExteriorHomeomorph (positive : 0 < angle) (small : angle < Real.pi) :
    (Set.Icc 0 angle × Set.Ioi (nndist R.start (R.chain.vertex hinge))) ≃ₜ
      {z : ℂ // z ∈ (R.suffix hinge).rotationGap outward nonzero angle ∧
        dist R.start (R.chain.vertex hinge) < dist R.start z} := by
  let X := Set.Icc 0 angle × Set.Ioi (nndist R.start (R.chain.vertex hinge))
  let Y := {z : ℂ // z ∈ (R.suffix hinge).rotationGap outward nonzero angle ∧
    dist R.start (R.chain.vertex hinge) < dist R.start z}
  let f : X → Y := fun p =>
    ⟨R.hingeCirclePoint hinge nonzero angle radial p.2.val p.1, by
      have higher : dist R.start (R.chain.vertex hinge) < (p.2.val : ℝ) := p.2.property
      refine ⟨?_, ?_⟩
      · exact (Set.ext_iff.mp (R.range_hingeCirclePoint hinge outward nonzero angle
          positive small radial p.2.val higher) _).mp ⟨p.1, rfl⟩ |>.1
      · rw [R.hingeCirclePoint_radius]
        exact higher⟩
  have continuous_f : Continuous f := by
    have base : Continuous (fun p : X => (p.1, p.2.val)) :=
      continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)
    have raw := (R.continuous_hingeSweepPoint hinge nonzero angle radial).comp base
    exact raw.subtype_mk _
  have injective : Function.Injective f := by
    intro p q same
    have points : R.hingeCirclePoint hinge nonzero angle radial p.2.val p.1 =
        R.hingeCirclePoint hinge nonzero angle radial q.2.val q.1 := congrArg Subtype.val same
    have radii : p.2 = q.2 := by
      apply Subtype.ext
      apply NNReal.eq
      have equal := congrArg (dist R.start) points
      simpa only [R.hingeCirclePoint_radius] using equal
    apply Prod.ext
    · have higher : dist R.start (R.chain.vertex hinge) < (p.2.val : ℝ) := p.2.property
      apply R.hingeCirclePoint_injective hinge outward nonzero angle positive small radial
        p.2.val higher
      simpa only [← radii] using points
    · exact radii
  have surjective : Function.Surjective f := by
    intro z
    let r := nndist R.start z.val
    have higher : dist R.start (R.chain.vertex hinge) < (r : ℝ) := z.property.2
    have member := (Set.ext_iff.mp
      (R.range_hingeCirclePoint hinge outward nonzero angle positive small radial r higher)
      z.val).mpr ⟨z.property.1, rfl⟩
    obtain ⟨θ, equal⟩ := member
    exact ⟨(θ, ⟨r, higher⟩), Subtype.ext equal⟩
  let coordinate : Y → Set.Ioi (nndist R.start (R.chain.vertex hinge)) := fun z =>
    ⟨nndist R.start z.val, z.property.2⟩
  have continuous_coordinate : Continuous coordinate := by
    fun_prop
  have equal : coordinate ∘ f = Prod.snd := by
    funext p
    apply Subtype.ext
    apply NNReal.eq
    exact R.hingeCirclePoint_radius hinge nonzero angle radial p.2.val p.1
  have proper_comp : IsProperMap (coordinate ∘ f) := by
    rw [equal]
    exact isProperMap_snd_of_compactSpace
  have proper_f := isProperMap_of_comp_of_t2 continuous_f continuous_coordinate proper_comp
  exact (Equiv.ofBijective f ⟨injective, surjective⟩).toHomeomorphOfContinuousClosed
    continuous_f proper_f.isClosedMap

@[simp] theorem hingeExteriorHomeomorph_apply (positive : 0 < angle) (small : angle < Real.pi)
    (p : Set.Icc 0 angle × Set.Ioi (nndist R.start (R.chain.vertex hinge))) :
    (R.hingeExteriorHomeomorph hinge nonzero angle radial outward positive small p).val =
      R.hingeCirclePoint hinge nonzero angle radial p.2.val p.1 := rfl

end Unfoldings.PolygonalRay
