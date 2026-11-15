module

public import Unfoldings.Geometry.AffineArrangement

/-! Exact local cones of finite affine arrangement cells, including unbounded cells. -/

@[expose] public section

open Filter Topology

namespace Unfoldings.AffineArrangement

variable {E I : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Finite I] (f : I → E →ᵃ[ℝ] ℝ) (signs : I → Bool)

/-- Only inequalities active at the original point constrain its tangent directions. -/
def tangentCell (x : E) : Set E :=
  {v | ∀ i, signed (f i) (signs i) x = 0 → 0 ≤ (signed (f i) (signs i)).linear v}

omit [FiniteDimensional ℝ E] [Finite I] in
theorem zero_mem_tangentCell (x : E) : (0 : E) ∈ tangentCell f signs x := by
  intro i _active
  simp only [map_zero, le_refl]

omit [FiniteDimensional ℝ E] [Finite I] in
theorem mem_tangentCell_smul_iff (x v : E) {r : ℝ} (positive : 0 < r) :
    r • v ∈ tangentCell f signs x ↔ v ∈ tangentCell f signs x := by
  simp only [tangentCell, Set.mem_ofPred_eq, map_smul, smul_eq_mul,
    mul_nonneg_iff_of_pos_left positive]

omit [Finite I] in
theorem isClosed_tangentCell (x : E) : IsClosed (tangentCell f signs x) := by
  have equality : tangentCell f signs x =
      ⋂ i, ⋂ (_ : signed (f i) (signs i) x = 0),
        (signed (f i) (signs i)).linear ⁻¹' Set.Ici 0 := by
    ext v
    simp only [tangentCell, Set.mem_ofPred_eq, Set.mem_iInter, Set.mem_preimage, Set.mem_Ici]
  rw [equality]
  exact isClosed_iInter fun i => isClosed_iInter fun _ =>
    isClosed_Ici.preimage (signed (f i) (signs i)).linear.continuous_of_finiteDimensional

omit [FiniteDimensional ℝ E] [Finite I] in
theorem convex_tangentCell (x : E) : Convex ℝ (tangentCell f signs x) := by
  have equality : tangentCell f signs x =
      ⋂ i, ⋂ (_ : signed (f i) (signs i) x = 0),
        (signed (f i) (signs i)).linear ⁻¹' Set.Ici 0 := by
    ext v
    simp only [tangentCell, Set.mem_ofPred_eq, Set.mem_iInter, Set.mem_preimage, Set.mem_Ici]
  rw [equality]
  exact convex_iInter fun i => convex_iInter fun _ =>
    (convex_Ici (0 : ℝ)).linear_preimage _

/-- Inactive inequalities have positive clearance; active inequalities are exactly linear. -/
theorem eventually_mem_closedChamber_iff_tangent {x : E} (member : x ∈ closedChamber f signs) :
    ∀ᶠ z in 𝓝 x, z ∈ closedChamber f signs ↔ z - x ∈ tangentCell f signs x := by
  have inactive_near : ∀ᶠ z in 𝓝 x,
      ∀ i, signed (f i) (signs i) x ≠ 0 → 0 < signed (f i) (signs i) z := by
    apply eventually_all.mpr
    intro i
    by_cases active : signed (f i) (signs i) x = 0
    · exact Filter.Eventually.of_forall (fun _ nonzero => (nonzero active).elim)
    · have positive : 0 < signed (f i) (signs i) x :=
        lt_of_le_of_ne (member i) (Ne.symm active)
      filter_upwards [(isOpen_lt continuous_const
        (signed (f i) (signs i)).continuous_of_finiteDimensional).mem_nhds positive] with z hz
      exact fun _ => hz
  filter_upwards [inactive_near] with z near
  have linearized (i : I) : (signed (f i) (signs i)).linear (z - x) =
      signed (f i) (signs i) z - signed (f i) (signs i) x :=
    (signed (f i) (signs i)).linear_apply_vsub z x
  constructor
  · intro inside i active
    rw [linearized, active, sub_zero]
    exact inside i
  · intro tangent i
    by_cases active : signed (f i) (signs i) x = 0
    · have bound := tangent i active
      rwa [linearized, active, sub_zero] at bound
    · exact (near i active).le

/-- A genuine ball around any cell point has exactly its translated active tangent cone. -/
theorem exists_radius_mem_closedChamber_iff_tangent {x : E}
    (member : x ∈ closedChamber f signs) :
    ∃ r : ℝ, 0 < r ∧ ∀ z, dist z x < r →
      (z ∈ closedChamber f signs ↔ z - x ∈ tangentCell f signs x) := by
  obtain ⟨r, positive, included⟩ := Metric.mem_nhds_iff.mp
    (eventually_mem_closedChamber_iff_tangent f signs member)
  exact ⟨r, positive, fun z near => included (Metric.mem_ball.mpr near)⟩

end Unfoldings.AffineArrangement
