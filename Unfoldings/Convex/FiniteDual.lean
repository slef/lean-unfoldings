module

public import Unfoldings.Convex.SlopeEnvelope
public import Mathlib.Analysis.Convex.Hull
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Topology.Order.Lattice

/-! Finite polyhedral conjugates and preservation of entire primal supporting faces. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FiniteDual

variable {I : Type*} [Fintype I] [Nonempty I]
  (point : I → Plane) (level : I → ℝ)

/-- The conjugate determined by finitely many lifted primal vertices. -/
def cost (p : Plane) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun i => inner ℝ (point i) p - level i)

theorem vertex_le (p : Plane) (i : I) :
    inner ℝ (point i) p - level i ≤ cost point level p :=
  Finset.le_sup' (fun j => inner ℝ (point j) p - level j) (Finset.mem_univ i)

theorem cost_le {p : Plane} {c : ℝ}
    (bound : ∀ i, inner ℝ (point i) p - level i ≤ c) : cost point level p ≤ c :=
  Finset.sup'_le _ _ (fun i _ => bound i)

theorem exists_cost_eq (p : Plane) :
    ∃ i, cost point level p = inner ℝ (point i) p - level i := by
  obtain ⟨i, _, equal⟩ := Finset.exists_mem_eq_sup' (s := Finset.univ)
    Finset.univ_nonempty (fun i => inner ℝ (point i) p - level i)
  exact ⟨i, equal⟩

theorem continuous_cost : Continuous (cost point level) :=
  Continuous.finset_sup'_apply Finset.univ_nonempty
    (fun _i _ => (continuous_const.inner continuous_id).sub continuous_const)

/-- Clipping is performed on slopes, without altering any primal vertex data. -/
def clipped (slopes : Set Plane) (compact : IsCompact slopes) (nonempty : slopes.Nonempty) :
    SlopeEnvelope where
  slopes := slopes
  compact := compact
  nonempty := nonempty
  dual := cost point level
  continuous_dual := continuous_cost point level

/-- The original primal supporting face, with its complete convex domain. -/
def face (s : Plane) (c : ℝ) : Set Plane :=
  convexHull ℝ {x | ∃ i, point i = x ∧ level i = inner ℝ (point i) s + c}

theorem cost_at_support {s : Plane} {c : ℝ}
    (support : ∀ i, inner ℝ (point i) s + c ≤ level i)
    (contact : ∃ i, level i = inner ℝ (point i) s + c) : cost point level s = -c := by
  apply le_antisymm
  · exact cost_le point level (fun i => by linarith [support i])
  · obtain ⟨i, equal⟩ := contact
    have bound := vertex_le point level s i
    linarith

/-- Every dual slope lies below the original plane throughout its whole supporting face. -/
theorem affine_le_on_face {s x : Plane} {c : ℝ} (member : x ∈ face point level s c)
    (q : Plane) : inner ℝ x q - cost point level q ≤ inner ℝ x s + c := by
  let l : Plane →L[ℝ] ℝ := innerSL ℝ q - innerSL ℝ s
  have convex : Convex ℝ {y : Plane |
      inner ℝ y q - cost point level q ≤ inner ℝ y s + c} := by
    convert (convex_Iic (c + cost point level q)).linear_preimage l.toLinearMap using 1
    ext y
    change (inner ℝ y q - cost point level q ≤ inner ℝ y s + c) ↔
      (inner ℝ q y - inner ℝ s y ≤ c + cost point level q)
    constructor <;> intro h <;> linarith [real_inner_comm q y, real_inner_comm s y]
  apply convexHull_min (t := {y : Plane |
    inner ℝ y q - cost point level q ≤ inner ℝ y s + c}) ?_ convex member
  rintro y ⟨i, rfl, equal⟩
  have bound := vertex_le point level q i
  change inner ℝ (point i) q - cost point level q ≤ inner ℝ (point i) s + c
  linarith

/-- If a primal face slope survives clipping, its entire original closed face survives
with exactly the original affine height. This includes boundary and subdivision points. -/
theorem clipped_preserves_face {slopes : Set Plane} (compact : IsCompact slopes)
    (nonempty : slopes.Nonempty) {s x : Plane} {c : ℝ}
    (support : ∀ i, inner ℝ (point i) s + c ≤ level i)
    (contact : ∃ i, level i = inner ℝ (point i) s + c)
    (selected : s ∈ slopes) (member : x ∈ face point level s c) :
    (clipped point level slopes compact nonempty).height x = inner ℝ x s + c := by
  let E := clipped point level slopes compact nonempty
  apply le_antisymm
  · exact E.height_le (fun q _ => affine_le_on_face point level member q)
  · have lower := E.affine_le x selected
    change inner ℝ x s - cost point level s ≤ E.height x at lower
    rw [cost_at_support point level support contact] at lower
    linarith

end Unfoldings.FiniteDual
