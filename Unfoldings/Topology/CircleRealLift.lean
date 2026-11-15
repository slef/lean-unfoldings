module

public import Unfoldings.Topology.CirclePositiveAngle
public import Mathlib.Topology.Maps.Proper.Basic

/-! Continuity of bounded real circle lifts, including an arc's initial point. -/

@[expose] public section

namespace Unfoldings

/-- A real lift in an interval shorter than a full turn inherits the continuity of its phase. -/
theorem continuous_of_continuous_circle_exp_of_mem_Icc
    {X : Type*} [TopologicalSpace X] {f : X → ℝ} {a b : ℝ} (short : b - a < 2 * Real.pi)
    (bounds : ∀ x, f x ∈ Set.Icc a b) (phase : Continuous (fun x => Circle.exp (f x))) :
    Continuous f := by
  have injective : Set.InjOn Circle.exp (Set.Icc a b) := by
    intro x hx y hy equal
    exact Circle.exp_injOn_Ico (a := a) (b := a + 2 * Real.pi) (by linarith)
      ⟨hx.1, by linarith [hx.2]⟩ ⟨hy.1, by linarith [hy.2]⟩ equal
  let F : X → Set.Icc a b := fun x => ⟨f x, bounds x⟩
  have equal : F.graph = {p : X × Set.Icc a b | Circle.exp (f p.1) = Circle.exp p.2.val} := by
    ext p
    change F p.1 = p.2 ↔ Circle.exp (f p.1) = Circle.exp p.2.val
    constructor
    · intro same
      exact congrArg (fun t : Set.Icc a b => Circle.exp t.val) same
    · intro same
      exact Subtype.ext (injective (bounds p.1) p.2.property same)
  have closed : IsClosed F.graph := by
    rw [equal]
    exact isClosed_eq (phase.comp continuous_fst)
      (Circle.exp.continuous.comp (continuous_subtype_val.comp continuous_snd))
  exact continuous_subtype_val.comp (continuous_of_isClosed_graph closed)

end Unfoldings
