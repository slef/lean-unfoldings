module

public import Unfoldings.Geometry.PolygonalRotationGap
public import Unfoldings.Geometry.PolygonalRayEquations
public import Unfoldings.Geometry.SourceRotation
public import Unfoldings.Geometry.UnboundedArrangement

/-! Finite closed convex cells cover source-rotation gaps, including their unbounded ends. -/

@[expose] public section

noncomputable section

namespace Unfoldings.PolygonalRay

variable {n : ℕ} (R : PolygonalRay ℂ n)

def gapEquations (angle : ℝ) : Set (ℂ →ᵃ[ℝ] ℝ) :=
  R.equations ∪ (fun l => l.comp (sourceRotation R.start angle).symm.toAffineMap) '' R.equations

theorem finite_gapEquations (angle : ℝ) : (R.gapEquations angle).Finite :=
  R.finite_equations.union (R.finite_equations.image _)

theorem gapEquations_ne_zero (angle : ℝ) (l : ℂ →ᵃ[ℝ] ℝ)
    (member : l ∈ R.gapEquations angle) : l ≠ 0 := by
  rcases member with old | ⟨k, hk, rfl⟩
  · exact R.equations_ne_zero l old
  · intro zero
    apply R.equations_ne_zero k hk
    ext x
    have equality := congrArg (fun f : ℂ →ᵃ[ℝ] ℝ => f (sourceRotation R.start angle x)) zero
    change k ((sourceRotation R.start angle).symm (sourceRotation R.start angle x)) = 0 at equality
    rw [AffineIsometryEquiv.symm_apply_apply] at equality
    exact equality

variable (outward : R.Outward) (nonzero : R.direction ≠ 0)

theorem gapEquations_cover (angle : ℝ) (sine : Real.sin angle ≠ 0) (z : ℂ)
    (boundary : z ∈ frontier (R.rotationGap outward nonzero angle)) :
    ∃ l ∈ R.gapEquations angle, l z = 0 := by
  rw [R.frontier_rotationGap outward nonzero angle sine] at boundary
  rcases boundary with old | ⟨x, hx, equal⟩
  · obtain ⟨l, hl, zero⟩ := R.equations_cover z old
    exact ⟨l, Or.inl hl, zero⟩
  · obtain ⟨l, hl, zero⟩ := R.equations_cover x hx
    refine ⟨l.comp (sourceRotation R.start angle).symm.toAffineMap,
      Or.inr ⟨l, hl, rfl⟩, ?_⟩
    have rotated : sourceRotation R.start angle x = z := by
      simpa only [sourceRotation_apply] using equal
    change l ((sourceRotation R.start angle).symm z) = 0
    rw [← rotated, AffineIsometryEquiv.symm_apply_apply]
    exact zero

/-- The cell cover is constructed from actual bank lines, rather than supplied as a certificate. -/
theorem exists_rotationGap_cell_cover (angle : ℝ) (sine : Real.sin angle ≠ 0) :
    ∃ (I : Type) (_ : Fintype I) (cells : I → Set ℂ),
      (∀ i, IsClosed (cells i) ∧ Convex ℝ (cells i) ∧ (interior (cells i)).Nonempty) ∧
      (∀ i j, i ≠ j → Disjoint (interior (cells i)) (interior (cells j))) ∧
      R.rotationGap outward nonzero angle = ⋃ i, cells i := by
  let lines := R.gapEquations angle
  let : Fintype lines := (R.finite_gapEquations angle).fintype
  let f (i : lines) := i.val
  obtain ⟨S, finite, nonempty, cover⟩ := AffineArrangement.exists_finite_unbounded_chamber_cover f
    (fun i => R.gapEquations_ne_zero angle i.val i.property)
    (R.isClosed_rotationGap outward nonzero angle sine)
    (R.rotationGap_regular_closed outward nonzero angle sine) (by
      intro z hz
      obtain ⟨l, hl, zero⟩ := R.gapEquations_cover outward nonzero angle sine z hz
      exact ⟨⟨l, hl⟩, zero⟩)
  let : Fintype S := finite.fintype
  refine ⟨S, inferInstance, (fun i => AffineArrangement.closedChamber f i.val), ?_, ?_, ?_⟩
  · intro i
    refine ⟨AffineArrangement.isClosed_closedChamber f i.val,
      AffineArrangement.convex_closedChamber f i.val, ?_⟩
    rw [AffineArrangement.interior_closedChamber f i.val (nonempty i.val i.property).1]
    exact (nonempty i.val i.property).1
  · intro i j different
    exact AffineArrangement.disjoint_chamber_interiors f
      (nonempty i.val i.property).1 (nonempty j.val j.property).1
      (fun same => different (Subtype.ext same))
  · rw [cover]
    ext z
    simp only [Set.mem_iUnion, Subtype.exists, exists_prop]

end Unfoldings.PolygonalRay
