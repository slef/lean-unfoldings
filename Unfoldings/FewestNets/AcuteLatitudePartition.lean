module

public import Unfoldings.FewestNets.AcuteLatitudeChordPairing
public import Unfoldings.FewestNets.AcuteLatitudeNorthSector
public import Unfoldings.FewestNets.LatitudeRingsPartition

/-! The earlier acute latitude grid instantiates the general spherical partition. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FewestNets.AcuteLatitudeGrid

open Real Module

variable {a : ℝ} (positive : 0 < a) (small : a ≤ π / 6)

/-- The latitude sweep and both fans give a spherical partition. -/
theorem chordSphere_partition :
    (⋃ i, chordTriangleOnSphere (chordBasis positive small i)) = Set.univ ∧
      Pairwise fun i j => Disjoint (strictChordTriangleOnSphere (chordBasis positive small i))
        (strictChordTriangleOnSphere (chordBasis positive small j)) := by
  let G : LatitudeRings := ⟨stripCount a, colatitude a, rowSize a⟩
  have admissible : G.Admissible := by
    refine ⟨(fun _ valid => colatitude_mem positive small valid), ?_, ?_⟩
    · intro j valid
      have count := rowSize_pos positive small valid
      have h := (longitudeStep_pos_lt_pi positive small valid).2
      have p : 0 < (rowSize a j : ℝ) := Nat.cast_pos.mpr count
      have t := (div_lt_iff₀ p).mp h
      rw [mul_comm 2 π] at t
      exact Nat.succ_le_of_lt (Nat.cast_lt.mp ((mul_lt_mul_iff_of_pos_left pi_pos).mp t))
    · dsimp only [G]
      change cos (colatitude a (stripCount a)) < 0
      rw [colatitude_last positive small, cos_pi_sub, neg_lt_zero]
      exact cos_pos_of_mem_Ioo
        ⟨by linarith only [polarRadius_pos positive, pi_pos],
          by linarith only [polarRadius_lt small, pi_gt_d2]⟩
  have vertices (i : ChordFace a) : LatitudeRings.chordVertices G i = chordVertices a i := by
    have row (j k : ℕ) : LatitudeRings.rowSite G j k = rowSite a j k := by
      unfold LatitudeRings.rowSite rowSite
      rfl
    rcases i with e | ⟨j, k⟩ | e
    · change ![latitudeSite 0 0, G.rowSite 0 (e.val + 1), G.rowSite 0 e.val] =
        ![latitudeSite 0 0, rowSite a 0 (e.val + 1), rowSite a 0 e.val]
      rw [row, row]
    · change G.latitudeSweepChordVertices j.val
        (LatitudeRings.sweepOrder (G.rowSize j.val) (G.rowSize (j.val + 1))) k =
          latitudeSweepChordVertices a j.val
            (sweepOrder (rowSize a j.val) (rowSize a (j.val + 1))) k
      have same : LatitudeRings.sweepOrder (G.rowSize j.val) (G.rowSize (j.val + 1)) =
          sweepOrder (rowSize a j.val) (rowSize a (j.val + 1)) := by
        unfold LatitudeRings.sweepOrder sweepOrder
        rfl
      rw [same]
      delta LatitudeRings.latitudeSweepChordVertices latitudeSweepChordVertices
      cases sweepOrder (rowSize a j.val) (rowSize a (j.val + 1)) k <;>
        simp only [LatitudeRings.latitudeSweepCrossSites, latitudeSweepCrossSites, row]
    · change ![latitudeSite π 0, G.rowSite (stripCount a) e.val, G.rowSite (stripCount a) (e.val + 1)] =
        ![latitudeSite π 0, rowSite a (stripCount a) e.val, rowSite a (stripCount a) (e.val + 1)]
      rw [row, row]
  have oriented : G.Oriented := by
    refine ⟨admissible, ?_⟩
    intro i
    have h := vertices (.inr (.inl i))
    change LatitudeRings.annularVertices G i = _ at h
    rw [h]
    exact chordVertices_det_neg positive small (.inr (.inl i))
  have equal (i : ChordFace a) :
      LatitudeRings.chordBasis oriented i = chordBasis positive small i := by
    apply DFunLike.coe_injective
    funext j
    rw [LatitudeRings.chordBasis_apply, chordBasis_apply, vertices]
  simpa only [equal] using LatitudeRings.chordSphere_partition oriented

end Unfoldings.FewestNets.AcuteLatitudeGrid
