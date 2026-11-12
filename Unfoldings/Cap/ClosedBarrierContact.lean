module

public import Unfoldings.Cap.CrossFrameInnerTerminalSeparation
public import Unfoldings.Geometry.ClosedInnerBarriers
public import Unfoldings.Geometry.WeakCircleCaps

/-! Actual cross-frame circle barriers identify the only possible endpoint contact. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap.RadialCutForest.FiveSectorFrameData

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexCap C} {source : Plane} {cuts : Set Plane} {N : K.RadialCutForest source cuts}
  {D : FacewiseDevelopment C N.completedRetain} {t : ℝ} {positive : 0 < t} {small : t < 1}
  (B : N.FiveSectorFrameData positive small D)

theorem inner_barrier_point_eq_of_norm_le (i l : FiveSector) (center m p : Plane)
    (first_barrier : 0 < (B.sectorFrame i (m - center)).re ∧
      0 < (B.sectorFrame i (m - center)).im)
    (last_barrier : 0 < (B.sectorFrame l (m - center)).re ∧
      0 < (B.sectorFrame l (m - center)).im)
    (first : 0 ≤ (B.sectorFrame i (p - center)).re ∧
      0 < (B.sectorFrame i (p - center)).im)
    (last : 0 ≤ (B.sectorFrame l (p - center)).re ∧
      0 < (B.sectorFrame l (p - center)).im)
    (horizontal : (B.sectorFrame i (p - center)).re ≤ (B.sectorFrame i (m - center)).re)
    (vertical : (B.sectorFrame l (p - center)).im ≤ (B.sectorFrame l (m - center)).im)
    (outside : ‖m - center‖ ≤ ‖p - center‖) : p = m := by
  let calibration := N.calibratedFrame D B.anchor B.reference
  let F := Complex.orthonormalBasisOneI.repr.trans (fiveSectorFrame t positive small i).place
  let G := Complex.orthonormalBasisOneI.repr.trans (fiveSectorFrame t positive small l).place
  have equal := oriented_inner_barrier_point_eq_of_norm_le F G
    (fiveSectorFrame_commutes_mul t positive small i)
    (fiveSectorFrame_commutes_mul t positive small l)
    (m := calibration (m - center)) (z := calibration (p - center))
    first_barrier last_barrier first last horizontal vertical
    (by simpa only [calibration.norm_map] using outside)
  have displacement := calibration.injective equal
  simpa only [sub_add_cancel] using congrArg (fun z : Plane => z + center) displacement

theorem weak_circle_caps_inter_subset_singleton (i l : FiveSector) (center m : Plane)
    (radius : ℝ)
    (first_barrier : 0 < (B.sectorFrame i (m - center)).re ∧
      0 < (B.sectorFrame i (m - center)).im)
    (last_barrier : 0 < (B.sectorFrame l (m - center)).re ∧
      0 < (B.sectorFrame l (m - center)).im)
    (inside : ‖m - center‖ ≤ radius) :
    weakCircleUpperCap (B.sectorFrame i) center radius (B.sectorFrame i (m - center)).re ∩
        weakCircleLowerCap (B.sectorFrame l) center radius (B.sectorFrame l (m - center)).im ⊆
      {m} := by
  intro p member
  apply Set.mem_singleton_iff.mpr
  exact B.inner_barrier_point_eq_of_norm_le i l center m p first_barrier last_barrier
    ⟨member.1.1, member.1.2.1⟩ ⟨member.2.1, member.2.2.1⟩
    member.1.2.2.1 member.2.2.2.1 (inside.trans_eq member.1.2.2.2.symm)

theorem weak_circle_caps_inter_subset_bank_points (i l : FiveSector) (center first last : Plane)
    (radius first_bound last_bound : ℝ)
    (first_inside : ‖first - center‖ ≤ radius) (last_inside : ‖last - center‖ ≤ radius)
    (quadrants : ∀ a, a = i ∨ a = l →
      (0 < (B.sectorFrame a (first - center)).re ∧
        0 < (B.sectorFrame a (first - center)).im) ∧
      (0 < (B.sectorFrame a (last - center)).re ∧
        0 < (B.sectorFrame a (last - center)).im))
    (first_bound_le : first_bound ≤ (B.sectorFrame i (first - center)).re)
    (last_bound_le : last_bound ≤ (B.sectorFrame l (last - center)).im)
    (alternative : (B.sectorFrame i (first - center)).re ≤
        (B.sectorFrame i (last - center)).re ∨
      (B.sectorFrame l (last - center)).im ≤ (B.sectorFrame l (first - center)).im) :
    weakCircleUpperCap (B.sectorFrame i) center radius first_bound ∩
        weakCircleLowerCap (B.sectorFrame l) center radius last_bound ⊆ {first, last} := by
  intro p member
  rcases alternative with horizontal | vertical
  · have equal : p = last := B.inner_barrier_point_eq_of_norm_le i l center last p
      (quadrants i (Or.inl rfl)).2 (quadrants l (Or.inr rfl)).2
      ⟨member.1.1, member.1.2.1⟩ ⟨member.2.1, member.2.2.1⟩
      ((member.1.2.2.1.trans first_bound_le).trans horizontal)
      (member.2.2.2.1.trans last_bound_le) (last_inside.trans_eq member.1.2.2.2.symm)
    exact Set.mem_insert_of_mem _ (Set.mem_singleton_iff.mpr equal)
  · have equal : p = first := B.inner_barrier_point_eq_of_norm_le i l center first p
      (quadrants i (Or.inl rfl)).1 (quadrants l (Or.inr rfl)).1
      ⟨member.1.1, member.1.2.1⟩ ⟨member.2.1, member.2.2.1⟩
      (member.1.2.2.1.trans first_bound_le)
      ((member.2.2.2.1.trans last_bound_le).trans vertical)
      (first_inside.trans_eq member.2.2.2.2.symm)
    exact Set.mem_insert_iff.mpr (Or.inl equal)

end Unfoldings.ConvexCap.RadialCutForest.FiveSectorFrameData
