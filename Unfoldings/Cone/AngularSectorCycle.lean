module

public import Unfoldings.Cone.ComplementarySectors
public import Unfoldings.Cone.HeadingSector
public import Mathlib.Data.Finset.Max

/-! The actual regions and shared rays in a finite cycle of possibly reentrant sectors. -/

@[expose] public section

noncomputable section

open scoped NNReal

namespace Unfoldings

variable {n : ℕ} (heading : Fin (n + 2) → ℝ)

/-- The sector between two consecutive real headings, in its common planar position. -/
def placedAngularSector (i : Fin (n + 1)) : Set ℂ :=
  rotation (Circle.exp (heading i.castSucc)) ''
    closedAngularSector (heading i.succ - heading i.castSucc)

theorem mem_placedAngularSector_iff (i : Fin (n + 1)) (z : ℂ) :
    z ∈ placedAngularSector heading i ↔ ∃ (r : ℝ≥0) (θ : ℝ),
      θ ∈ Set.Icc (heading i.castSucc) (heading i.succ) ∧ z = (r : ℂ) * polarRay θ := by
  constructor
  · rintro ⟨q, ⟨r, φ, bounds, rfl⟩, rfl⟩
    refine ⟨r, heading i.castSucc + φ, ⟨?_, ?_⟩, rotate_polar_point _ _ _⟩
    · linarith [bounds.1]
    · linarith [bounds.2]
  · rintro ⟨r, θ, bounds, rfl⟩
    refine ⟨(r : ℂ) * polarRay (θ - heading i.castSucc),
      ⟨r, θ - heading i.castSucc, ⟨sub_nonneg.mpr bounds.1, ?_⟩, rfl⟩, ?_⟩
    · linarith [bounds.2]
    · rw [rotate_polar_point, add_sub_cancel]

variable (ordered : StrictMono heading) (start : heading 0 = 0)
  (finish : heading (Fin.last (n + 1)) = 2 * Real.pi)

include start finish in
/-- The sectors of a full cycle cover the entire plane. -/
theorem exists_mem_placedAngularSector (z : ℂ) : ∃ i, z ∈ placedAngularSector heading i := by
  classical
  obtain ⟨r, θ, bounds, eq⟩ := exists_polar_nonnegative_heading z
  let ends := Finset.univ.filter (fun j : Fin (n + 1) => θ ≤ heading j.succ)
  have last_member : Fin.last n ∈ ends := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [Fin.succ_last, finish]
    exact bounds.2
  let i := ends.min' ⟨Fin.last n, last_member⟩
  have high : θ ≤ heading i.succ := (Finset.mem_filter.mp (ends.min'_mem _)).2
  have low (k : Fin (n + 1)) (equal : k = i) : heading k.castSucc ≤ θ := by
    revert equal
    refine Fin.cases ?_ (fun j => ?_) k
    · intro _
      simpa only [Fin.castSucc_zero, start] using bounds.1
    · intro at_minimum
      by_contra! late
      have previous : j.castSucc ∈ ends := by
        apply Finset.mem_filter.mpr
        have same : j.castSucc.succ = j.succ.castSucc := Fin.ext rfl
        exact ⟨Finset.mem_univ _, same.symm ▸ late.le⟩
      have minimal : i ≤ j.castSucc := ends.min'_le _ previous
      exact (not_le_of_gt Fin.castSucc_lt_succ) (at_minimum.symm ▸ minimal)
  exact ⟨i, (mem_placedAngularSector_iff heading i z).mpr ⟨r, θ, ⟨low i rfl, high⟩, eq⟩⟩

include ordered start finish in
/-- Two distinct ordered sectors can touch only at the apex, their consecutive ray,
or the closing ray between the first and last sectors. -/
theorem placedAngularSector_shared {i j : Fin (n + 1)} (earlier : i < j) {z : ℂ}
    (in_i : z ∈ placedAngularSector heading i) (in_j : z ∈ placedAngularSector heading j) :
    z = 0 ∨
      (i.succ = j.castSucc ∧ ∃ r : ℝ≥0, z = (r : ℂ) * polarRay (heading i.succ)) ∨
      (i = 0 ∧ j = Fin.last n ∧ ∃ r : ℝ≥0, z = (r : ℂ)) := by
  obtain ⟨r, θ, first, point_i⟩ := (mem_placedAngularSector_iff heading i z).mp in_i
  obtain ⟨s, φ, last, point_j⟩ := (mem_placedAngularSector_iff heading j z).mp in_j
  have radii := polar_radius_eq r s θ φ (point_i.symm.trans point_j)
  subst s
  by_cases zero : r = 0
  · exact Or.inl (by simpa [zero] using point_i)
  have between : i.succ ≤ j.castSucc := Fin.le_iff_val_le_val.mpr earlier
  have order : θ ≤ φ :=
    first.2.trans ((ordered.monotone between).trans last.1)
  have all (k : Fin (n + 2)) : heading k ∈ Set.Icc 0 (2 * Real.pi) := by
    exact ⟨start ▸ ordered.monotone (Fin.zero_le k), finish ▸ ordered.monotone (Fin.le_last k)⟩
  have θbound : θ ∈ Set.Icc 0 (2 * Real.pi) :=
    ⟨(all _).1.trans first.1, first.2.trans (all _).2⟩
  have φbound : φ ∈ Set.Icc 0 (2 * Real.pi) :=
    ⟨(all _).1.trans last.1, last.2.trans (all _).2⟩
  rcases polar_eq_heading_cases r zero θ φ θbound φbound
      (point_i.symm.trans point_j) with same | ⟨zero_heading, full_heading⟩ |
      ⟨full_heading, zero_heading⟩
  · have edge := le_antisymm (ordered.monotone between)
      (last.1.trans (same.symm ▸ first.2))
    have named := ordered.injective edge
    have same_heading := le_antisymm first.2 ((ordered.monotone between).trans (same ▸ last.1))
    exact Or.inr (Or.inl ⟨named, r, same_heading ▸ point_i⟩)
  · have first_index : i.castSucc = 0 := ordered.injective
      ((le_antisymm (zero_heading ▸ first.1) (all _).1).trans start.symm)
    have last_index : j.succ = Fin.last (n + 1) := ordered.injective
      ((le_antisymm (all _).2 (full_heading ▸ last.2)).trans finish.symm)
    have first_value : i.val = 0 := congrArg (fun k : Fin (n + 2) => k.val) first_index
    have last_value : j.val + 1 = n + 1 := congrArg (fun k : Fin (n + 2) => k.val) last_index
    refine Or.inr (Or.inr ⟨Fin.ext first_value, Fin.ext ?_, r, ?_⟩)
    · rw [Fin.val_last]
      omega
    · simpa only [zero_heading, polarRay_zero, mul_one] using point_i
  · have bad : 2 * Real.pi ≤ 0 := full_heading ▸ zero_heading ▸ order
    linarith [Real.pi_pos]

/-- A genuine convex heading interval gives a closed subset of the plane. -/
theorem isClosed_headingSector (a b : ℝ) (positive : 0 < b - a) (small : b - a < Real.pi) :
    IsClosed (headingSector a b) :=
  (rotation (Circle.exp a)).toHomeomorph.isClosedMap _
    (isClosed_planarSector (b - a) (Real.sin_pos_of_pos_of_lt_pi positive small).ne')

/-- Each placed sector below a full turn is covered by two genuine convex subcells. -/
theorem placedAngularSector_eq_convex_halves (i : Fin (n + 1))
    (positive : heading i.castSucc < heading i.succ)
    (small : heading i.succ - heading i.castSucc < 2 * Real.pi) :
    let a := heading i.castSucc
    let b := heading i.succ
    let m := (a + b) / 2
    placedAngularSector heading i = headingSector a m ∪ headingSector m b := by
  dsimp only
  set a := heading i.castSucc
  set b := heading i.succ
  let m := (a + b) / 2
  change placedAngularSector heading i = headingSector a m ∪ headingSector m b
  have first_pos : 0 < m - a := by dsimp [m]; linarith
  have first_small : m - a < Real.pi := by dsimp [m]; linarith
  have second_pos : 0 < b - m := by dsimp [m]; linarith
  have second_small : b - m < Real.pi := by dsimp [m]; linarith
  ext z
  rw [Set.mem_union, mem_headingSector_iff_polar a m first_pos first_small,
    mem_headingSector_iff_polar m b second_pos second_small, mem_placedAngularSector_iff]
  change (∃ r : ℝ≥0, ∃ θ ∈ Set.Icc a b, z = (r : ℂ) * polarRay θ) ↔ _
  constructor
  · rintro ⟨r, θ, h, eq⟩
    by_cases before : θ ≤ m
    · exact Or.inl ⟨r, θ, ⟨h.1, before⟩, eq⟩
    · exact Or.inr ⟨r, θ, ⟨le_of_not_ge before, h.2⟩, eq⟩
  · rintro (⟨r, θ, h, eq⟩ | ⟨r, θ, h, eq⟩)
    · exact ⟨r, θ, ⟨h.1, h.2.trans (sub_pos.mp second_pos).le⟩, eq⟩
    · exact ⟨r, θ, ⟨(sub_pos.mp first_pos).le.trans h.1, h.2⟩, eq⟩

end Unfoldings
