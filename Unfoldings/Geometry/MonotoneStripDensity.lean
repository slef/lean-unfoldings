module

public import Unfoldings.Geometry.MonotoneStripSubdivision
public import Mathlib.Topology.Baire.Lemmas

/-! Finite waterfall walls are closed nowhere dense; points off them lie in strict cells. -/

@[expose] public section

namespace Unfoldings

namespace MonotoneHeightGraph

variable (G : MonotoneHeightGraph)

theorem mem_range_point_iff (z : ℂ) :
    z ∈ Set.range G.point ↔ G.coordinate (z.re + z.im) = z.re := by
  constructor
  · rintro ⟨h, rfl⟩
    rw [G.point_height]
    rfl
  · intro coordinate
    exact ⟨z.re + z.im, G.point_eq_of_coordinate z coordinate⟩

theorem isClosed_range_point : IsClosed (Set.range G.point) := by
  have equal : Set.range G.point = {z | G.coordinate (z.re + z.im) = z.re} :=
    Set.ext G.mem_range_point_iff
  rw [equal]
  exact isClosed_eq
    (G.continuous.comp (Complex.continuous_re.add Complex.continuous_im)) Complex.continuous_re

theorem dense_compl_range_point : Dense (Set.range G.point)ᶜ := by
  apply dense_iff_inter_open.mpr
  intro U opened present
  obtain ⟨z, member⟩ := present
  let h := z.re + z.im
  let f := fun x : ℝ => (⟨x, h - x⟩ : ℂ)
  have continuous : Continuous f := by
    have parts := Complex.continuous_ofReal.add
      ((Complex.continuous_ofReal.comp ((continuous_const (y := h)).sub continuous_id)).mul
        (continuous_const (y := Complex.I)))
    convert parts using 1
    ext x
    apply Complex.ext <;> simp [f]
  have source : f z.re = z := by
    apply Complex.ext
    · rfl
    · change z.re + z.im - z.re = z.im
      ring
  obtain ⟨x, inside, different⟩ := (dense_compl_singleton (G.coordinate h)).inter_open_nonempty
    (f ⁻¹' U) (opened.preimage continuous) ⟨z.re, source.symm ▸ member⟩
  refine ⟨f x, inside, ?_⟩
  intro on_graph
  have height : (f x).re + (f x).im = h := by change x + (h - x) = h; ring
  have coordinate := (G.mem_range_point_iff (f x)).mp on_graph
  rw [height] at coordinate
  exact different coordinate.symm

end MonotoneHeightGraph

namespace MonotoneStrip.Subdivision

variable {S : MonotoneStrip} (T : S.Subdivision)

theorem finite_walls : T.walls.Finite := by
  induction T with
  | leaf S => exact (Set.finite_singleton S.upper).insert S.lower
  | split _ _ _ _ first last => exact first.union last

theorem dense_avoiding_walls : Dense {z | ∀ G ∈ T.walls, z ∉ Set.range G.point} := by
  let family := (fun G : MonotoneHeightGraph => (Set.range G.point)ᶜ) '' T.walls
  have family_finite : family.Finite := T.finite_walls.image _
  have dense := family_finite.dense_sInter
    (by rintro _ ⟨G, _, rfl⟩; exact G.isClosed_range_point.isOpen_compl)
    (by rintro _ ⟨G, _, rfl⟩; exact G.dense_compl_range_point)
  have equal : ⋂₀ family = {z | ∀ G ∈ T.walls, z ∉ Set.range G.point} := by
    ext z
    constructor
    · intro member G wall
      exact member _ ⟨G, wall, rfl⟩
    · intro member U in_family
      obtain ⟨G, wall, rfl⟩ := in_family
      exact member G wall
  exact equal ▸ dense

theorem exists_strict_cell_of_avoids_walls {z : ℂ} (member : z ∈ S.carrier)
    (avoids : ∀ G ∈ T.walls, z ∉ Set.range G.point) :
    ∃ R ∈ T.cells, z ∈ R.strictCarrier := by
  obtain ⟨R, cell, inside⟩ := (T.cover z).mp member
  have walls := T.cell_walls cell
  have first : R.lower.coordinate (z.re + z.im) ≠ z.re := by
    intro equal
    exact avoids R.lower walls.1 ⟨z.re + z.im, R.lower.point_eq_of_coordinate z equal⟩
  have last : R.upper.coordinate (z.re + z.im) ≠ z.re := by
    intro equal
    exact avoids R.upper walls.2 ⟨z.re + z.im, R.upper.point_eq_of_coordinate z equal⟩
  exact ⟨R, cell, lt_of_le_of_ne inside.1 first, lt_of_le_of_ne inside.2 last.symm⟩

end MonotoneStrip.Subdivision
end Unfoldings
