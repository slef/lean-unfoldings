module

public import Unfoldings.Basic
public import Mathlib.Analysis.Convex.Function
public import Mathlib.Analysis.Normed.Affine.AddTorsorBases
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Topology.Order.Lattice

/-! Finite lower envelopes of affine support planes, independent of a triangulation. -/

@[expose] public section

noncomputable section

namespace Unfoldings.AffineEnvelope

variable {I : Type*} [Fintype I] [Nonempty I] (support : I → Plane →ᵃ[ℝ] ℝ)

/-- The lower envelope of a nonempty finite family of affine heights. -/
def height (p : Plane) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty (fun i => support i p)

theorem height_le (p : Plane) (i : I) : height support p ≤ support i p :=
  Finset.inf'_le _ (Finset.mem_univ i)

theorem exists_height_eq (p : Plane) : ∃ i, height support p = support i p := by
  obtain ⟨i, _, equal⟩ := Finset.exists_mem_eq_inf' (s := Finset.univ)
    Finset.univ_nonempty (fun i => support i p)
  exact ⟨i, equal⟩

theorem continuous_height : Continuous (height support) :=
  Continuous.finset_inf'_apply Finset.univ_nonempty
    (fun i _ => (support i).continuous_of_finiteDimensional)

theorem concave_height : ConcaveOn ℝ Set.univ (height support) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb sum
  obtain ⟨i, equal⟩ := exists_height_eq support (a • x + b • y)
  rw [equal, Convex.combo_affine_apply sum]
  exact add_le_add (smul_le_smul_of_nonneg_left (height_le support x i) ha)
    (smul_le_smul_of_nonneg_left (height_le support y i) hb)

omit [Fintype I] [Nonempty I] in
/-- The closed convex region where a particular support plane is active. -/
def cell (i : I) : Set Plane := {p | ∀ j, support i p ≤ support j p}

omit [Fintype I] [Nonempty I] in
theorem cell_eq_iInter (i : I) : cell support i = ⋂ j, {p | support i p ≤ support j p} := by
  ext p
  simp only [cell, Set.mem_ofPred_eq, Set.mem_iInter]

omit [Fintype I] [Nonempty I] in
theorem isClosed_cell (i : I) : IsClosed (cell support i) := by
  rw [cell_eq_iInter]
  exact isClosed_iInter fun j => isClosed_le
    (support i).continuous_of_finiteDimensional (support j).continuous_of_finiteDimensional

omit [Fintype I] [Nonempty I] in
theorem convex_cell (i : I) : Convex ℝ (cell support i) := by
  rw [cell_eq_iInter]
  apply convex_iInter
  intro j
  have rule := (convex_Iic (0 : ℝ)).affine_preimage (support i - support j)
  rw [AffineMap.coe_sub] at rule
  change Convex ℝ {p | support i p - support j p ≤ 0} at rule
  simpa only [sub_nonpos] using rule

theorem mem_cell_iff (i : I) (p : Plane) :
    p ∈ cell support i ↔ height support p = support i p := by
  constructor
  · intro active
    obtain ⟨j, equal⟩ := exists_height_eq support p
    exact le_antisymm (height_le support p i) (equal ▸ active j)
  · intro active j
    rw [← active]
    exact height_le support p j

/-- A horizontal superlevel section of the affine roof. It need not be bounded. -/
def clip (Z : ℝ) : Set Plane := {p | Z ≤ height support p}

theorem isClosed_clip (Z : ℝ) : IsClosed (clip support Z) :=
  isClosed_Ici.preimage (continuous_height support)

theorem convex_clip (Z : ℝ) : Convex ℝ (clip support Z) := by
  simpa only [clip, Set.mem_univ, true_and] using (concave_height support).convex_ge Z

/-- Strictly higher points lie in the interior of the horizontal section. -/
theorem mem_interior_clip {Z : ℝ} {p : Plane} (higher : Z < height support p) :
    p ∈ interior (clip support Z) := by
  have opens : IsOpen {p | Z < height support p} :=
    isOpen_lt continuous_const (continuous_height support)
  have included : {q | Z < height support q} ⊆ clip support Z := by
    intro q member
    exact le_of_lt (show Z < height support q from member)
  exact opens.subset_interior_iff.mpr included higher

theorem height_eq_level_of_frontier {Z : ℝ} {p : Plane} (boundary : p ∈ frontier (clip support Z)) :
    height support p = Z := by
  have member := (isClosed_clip support Z).frontier_subset boundary
  apply le_antisymm _ member
  by_contra higher
  exact boundary.2 (mem_interior_clip support (lt_of_not_ge higher))

end Unfoldings.AffineEnvelope
