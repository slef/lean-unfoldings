module

public import Unfoldings.Cap.SectorWaterfallDensity
public import Unfoldings.Geometry.MonotoneStripTopology
public import Unfoldings.Geometry.MonotoneStripSlab
public import Unfoldings.Geometry.RecoverableStripClosure

/-! Avoiding the finite physical waterfall walls is an open dense condition. -/

@[expose] public section

noncomputable section

namespace Unfoldings

variable {t : ℝ} (positive : 0 < t) (small : t < 1) (q : Plane)

def sectorWaterfallRegular
    (P : ∀ i : FiveSector, (fiveSectorFrame t positive small i).enclosingStrip.Subdivision) :
    Set Plane := {p | ∀ i G, G ∈ (P i).walls →
      (fiveSectorFrame t positive small i).place (p - q) ∉ Set.range G.point}

theorem isOpen_sectorWaterfallRegular
    (P : ∀ i : FiveSector, (fiveSectorFrame t positive small i).enclosingStrip.Subdivision) :
    IsOpen (sectorWaterfallRegular positive small q P) := by
  let Wall := fun i : FiveSector => {G : MonotoneHeightGraph // G ∈ (P i).walls}
  let : ∀ i : FiveSector, Finite (Wall i) := fun i => (P i).finite_walls.to_subtype
  have equal : sectorWaterfallRegular positive small q P =
      ⋂ i : FiveSector, ⋂ G : Wall i,
        (fun p : Plane => (fiveSectorFrame t positive small i).place (p - q)) ⁻¹'
          (Set.range G.val.point)ᶜ := by
    ext p
    simp only [sectorWaterfallRegular, Set.mem_ofPred_eq, Set.mem_iInter,
      Set.mem_preimage, Set.mem_compl_iff, Wall, Subtype.forall]
  rw [equal]
  apply isOpen_iInter_of_finite
  intro i
  apply isOpen_iInter_of_finite
  intro G
  exact G.val.isClosed_range_point.isOpen_compl.preimage
    ((fiveSectorFrame t positive small i).place.continuous.comp
      (continuous_id.sub continuous_const))

theorem dense_sectorWaterfallRegular
    (P : ∀ i : FiveSector, (fiveSectorFrame t positive small i).enclosingStrip.Subdivision) :
    Dense (sectorWaterfallRegular positive small q P) :=
  dense_avoiding_sector_waterfall_walls positive small q P

/-- Every regular point in the controlled region lies in an actual open strip,
with strictly positive source height and height strictly below the cutoff. -/
theorem sectorWaterfallRegular_mem_openSlab
    (P : ∀ i : FiveSector, (fiveSectorFrame t positive small i).enclosingStrip.Subdivision)
    {cutoff : ℝ} {p : Plane} (regular : p ∈ sectorWaterfallRegular positive small q P)
    (inside : p ∈ sectorSweepInterior positive small q cutoff) :
    ∃ i : FiveSector, ∃ S ∈ (P i).cells,
      (fiveSectorFrame t positive small i).place (p - q) ∈ S.openSlab 0 cutoff := by
  obtain ⟨i, cone⟩ := exists_mem_closedFiveSector positive small (p - q)
  let B := fiveSectorFrame t positive small i
  have root : B.place (p - q) ∈ B.enclosingStrip.carrier := B.enclosingStrip_mem cone
  obtain ⟨S, cell, strict⟩ := (P i).exists_strict_cell_of_avoids_walls root (regular i)
  have root_bounds := (P i).cell_bounds cell
    ((B.place (p - q)).re + (B.place (p - q)).im)
  have root_strict : B.place (p - q) ∈ B.enclosingStrip.strictCarrier :=
    ⟨root_bounds.1.trans_lt strict.1, strict.2.trans_le root_bounds.2⟩
  have nonnegative := B.quadrant_nonneg cone
  have height := B.enclosingStrip.strict_height_pos_of_source B.enclosingStrip_source.1
    B.enclosingStrip_source.2 root_strict (add_nonneg nonnegative.1 nonnegative.2)
  exact ⟨i, S, cell, strict, height, inside i⟩

end Unfoldings
