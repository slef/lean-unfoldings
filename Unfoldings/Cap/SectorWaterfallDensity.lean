module

public import Unfoldings.Cap.GeometricSectorData
public import Unfoldings.Geometry.MonotoneStripDensity

/-! Strict interiors of finite sector waterfalls are dense in their physical sweep region. -/

@[expose] public section

noncomputable section

namespace Unfoldings

variable {t : ℝ} (positive : 0 < t) (small : t < 1) (q : Plane)

def sectorSweepInterior (cutoff : ℝ) : Set Plane :=
  {p | ∀ i : FiveSector,
    ((fiveSectorFrame t positive small i).place (p - q)).re +
      ((fiveSectorFrame t positive small i).place (p - q)).im < cutoff}

theorem isOpen_sectorSweepInterior (cutoff : ℝ) :
    IsOpen (sectorSweepInterior positive small q cutoff) := by
  simp only [sectorSweepInterior, Set.ofPred_forall]
  apply isOpen_iInter_of_finite
  intro i
  have input := (fiveSectorFrame t positive small i).place.continuous.comp
    (continuous_id.sub (continuous_const (y := q)))
  exact isOpen_lt ((Complex.continuous_re.comp input).add (Complex.continuous_im.comp input))
    continuous_const

theorem dense_avoiding_sector_waterfall_walls
    (P : ∀ i : FiveSector, (fiveSectorFrame t positive small i).enclosingStrip.Subdivision) :
    Dense {p : Plane | ∀ i G, G ∈ (P i).walls →
      (fiveSectorFrame t positive small i).place (p - q) ∉ Set.range G.point} := by
  let Wall := fun i : FiveSector => {G : MonotoneHeightGraph // G ∈ (P i).walls}
  let : ∀ i : FiveSector, Finite (Wall i) := fun i => (P i).finite_walls.to_subtype
  let W := Sigma Wall
  let A := fun i : FiveSector =>
    (AffineEquiv.toContinuousAffineEquiv
      (centeredPlaneFrame q (fiveSectorFrame t positive small i).place)).toHomeomorph
  have apply_frame (i : FiveSector) (p : Plane) :
      A i p = (fiveSectorFrame t positive small i).place (p - q) := centeredPlaneFrame_apply _ _ _
  let D := fun w : W => (A w.1) ⁻¹' (Set.range w.2.val.point)ᶜ
  have opened (w : W) : IsOpen (D w) :=
    w.2.val.isClosed_range_point.isOpen_compl.preimage (A w.1).continuous
  have dense (w : W) : Dense (D w) :=
    w.2.val.dense_compl_range_point.preimage (A w.1).isOpenMap
  have all_dense := (Set.finite_range D).dense_sInter
    (by rintro U ⟨w, rfl⟩; exact opened w)
    (by rintro U ⟨w, rfl⟩; exact dense w)
  have equal : ⋂₀ Set.range D = {p : Plane | ∀ i G, G ∈ (P i).walls →
      (fiveSectorFrame t positive small i).place (p - q) ∉ Set.range G.point} := by
    ext p
    constructor
    · intro member i G wall
      have result := member (D ⟨i, ⟨G, wall⟩⟩) ⟨⟨i, ⟨G, wall⟩⟩, rfl⟩
      change A i p ∉ Set.range G.point at result
      rwa [apply_frame] at result
    · intro member U in_family
      obtain ⟨⟨i, G⟩, rfl⟩ := in_family
      change A i p ∉ Set.range G.val.point
      rw [apply_frame]
      exact member i G.val G.property
  exact equal ▸ all_dense

theorem sectorSweepInterior_subset_closure_strict_cells
    (P : ∀ i : FiveSector, (fiveSectorFrame t positive small i).enclosingStrip.Subdivision)
    (cutoff : ℝ) :
    sectorSweepInterior positive small q cutoff ⊆ closure {p : Plane |
      ∃ i : FiveSector, ∃ S ∈ (P i).cells,
        (fiveSectorFrame t positive small i).place (p - q) ∈ S.strictCarrier ∧
          ((fiveSectorFrame t positive small i).place (p - q)).re +
            ((fiveSectorFrame t positive small i).place (p - q)).im ∈ Set.Icc 0 cutoff} := by
  have dense := dense_avoiding_sector_waterfall_walls positive small q P
  have subset := dense.open_subset_closure_inter
    (isOpen_sectorSweepInterior positive small q cutoff)
  refine subset.trans (closure_mono ?_)
  intro p member
  obtain ⟨i, cone⟩ := exists_mem_closedFiveSector positive small (p - q)
  let B := fiveSectorFrame t positive small i
  have root : B.place (p - q) ∈ B.enclosingStrip.carrier := B.enclosingStrip_mem cone
  obtain ⟨S, cell, strict⟩ := (P i).exists_strict_cell_of_avoids_walls root (member.2 i)
  have nonnegative := B.quadrant_nonneg cone
  exact ⟨i, S, cell, strict, add_nonneg nonnegative.1 nonnegative.2, (member.1 i).le⟩

theorem open_subset_closure_sector_strict_cells
    (P : ∀ i : FiveSector, (fiveSectorFrame t positive small i).enclosingStrip.Subdivision)
    (cutoff : ℝ) (U : Set Plane) (opened : IsOpen U)
    (inside : U ⊆ sectorSweepInterior positive small q cutoff) :
    U ⊆ closure (U ∩ {p : Plane |
      ∃ i : FiveSector, ∃ S ∈ (P i).cells,
        (fiveSectorFrame t positive small i).place (p - q) ∈ S.strictCarrier ∧
          ((fiveSectorFrame t positive small i).place (p - q)).re +
            ((fiveSectorFrame t positive small i).place (p - q)).im ∈ Set.Icc 0 cutoff}) := by
  have dense := dense_avoiding_sector_waterfall_walls positive small q P
  refine (dense.open_subset_closure_inter opened).trans (closure_mono ?_)
  intro p member
  refine ⟨member.1, ?_⟩
  obtain ⟨i, cone⟩ := exists_mem_closedFiveSector positive small (p - q)
  let B := fiveSectorFrame t positive small i
  have root : B.place (p - q) ∈ B.enclosingStrip.carrier := B.enclosingStrip_mem cone
  obtain ⟨S, cell, strict⟩ := (P i).exists_strict_cell_of_avoids_walls root (member.2 i)
  have nonnegative := B.quadrant_nonneg cone
  exact ⟨i, S, cell, strict, add_nonneg nonnegative.1 nonnegative.2,
    (inside member.1 i).le⟩

theorem triangle_sectorSweep_mem_closure_strict_cells
    (P : ∀ i : FiveSector, (fiveSectorFrame t positive small i).enclosingStrip.Subdivision)
    (cutoff : ℝ) (T : Triangle) {p : Plane} (member : p ∈ T.carrier)
    (inside : p ∈ sectorSweepInterior positive small q cutoff) :
    p ∈ closure ((sectorSweepInterior positive small q cutoff ∩ interior T.carrier) ∩
      {p : Plane | ∃ i : FiveSector, ∃ S ∈ (P i).cells,
        (fiveSectorFrame t positive small i).place (p - q) ∈ S.strictCarrier ∧
          ((fiveSectorFrame t positive small i).place (p - q)).re +
            ((fiveSectorFrame t positive small i).place (p - q)).im ∈ Set.Icc 0 cutoff}) := by
  have regular := T.convex_carrier.closure_interior_eq_closure_of_nonempty_interior
    T.interior_nonempty
  rw [T.compact_carrier.isClosed.closure_eq] at regular
  have near := (isOpen_sectorSweepInterior positive small q cutoff).inter_closure
    ⟨inside, regular.symm ▸ member⟩
  have dense := open_subset_closure_sector_strict_cells positive small q P cutoff
    (sectorSweepInterior positive small q cutoff ∩ interior T.carrier)
    ((isOpen_sectorSweepInterior positive small q cutoff).inter isOpen_interior)
    Set.inter_subset_left
  exact closure_minimal dense isClosed_closure near

end Unfoldings
