module

public import Unfoldings.Cone.AngularFan
public import Unfoldings.Cone.SectorInterior

/-!
# Genuine planar images of angular fan pieces

The interiors of the rigidly placed closed sectors have exactly the open
intervals of cumulative real headings. A fan of width at most one full turn
therefore has pairwise disjoint piece interiors, allowing boundary contacts.
-/

@[expose] public section

noncomputable section

namespace Unfoldings.AngularFan

variable {n : ℕ} (A : AngularFan n)

def faceImage (i : Fin (n + 1)) : Set ℂ :=
  (rotation (Circle.exp (A.heading i.castSucc))).toHomeomorph '' planarSector (A.angle i)

/-- Nonoverlap refers to actual planar interiors, independently of boundary contacts. -/
def Nonoverlapping : Prop :=
  Pairwise (fun i j => Disjoint (interior (A.faceImage i)) (interior (A.faceImage j)))

theorem heading_nonneg (i : Fin (n + 2)) : 0 ≤ A.heading i := by
  rw [← A.heading_zero]
  exact A.heading_strictMono.monotone (Fin.zero_le i)

theorem heading_le_totalAngle (i : Fin (n + 2)) : A.heading i ≤ A.totalAngle := by
  rw [← A.heading_last]
  exact A.heading_strictMono.monotone (Fin.le_last i)

theorem mem_interior_faceImage_iff (i : Fin (n + 1)) (z : ℂ) :
    z ∈ interior (A.faceImage i) ↔
      ∃ r : ℝ, 0 < r ∧ ∃ θ ∈ Set.Ioo (A.heading i.castSucc) (A.heading i.succ),
        z = (r : ℂ) * polarRay θ := by
  let h := (rotation (Circle.exp (A.heading i.castSucc))).toHomeomorph
  change z ∈ interior (h '' planarSector (A.angle i)) ↔ _
  rw [← h.image_interior]
  constructor
  · rintro ⟨w, inside, mapped⟩
    obtain ⟨r, positive, θ, bounds, rfl⟩ := exists_polar_of_mem_interior_planarSector
      (A.angle i) (A.positive i) (A.small i) w inside
    refine ⟨r, positive, A.heading i.castSucc + θ, ?_, ?_⟩
    · rw [A.heading_succ]
      constructor <;> linarith [bounds.1, bounds.2]
    · change polarRay (A.heading i.castSucc) * ((r : ℂ) * polarRay θ) = z at mapped
      rw [← mapped, polarRay_add]
      ring
  · rintro ⟨r, positive, θ, bounds, rfl⟩
    have local_heading : θ - A.heading i.castSucc ∈ Set.Ioo 0 (A.angle i) := by
      rw [A.heading_succ] at bounds
      constructor <;> linarith [bounds.1, bounds.2]
    refine ⟨(r : ℂ) * polarRay (θ - A.heading i.castSucc),
      polar_mem_interior_planarSector (A.angle i) r _ (A.positive i) (A.small i)
        positive local_heading, ?_⟩
    change polarRay (A.heading i.castSucc) * ((r : ℂ) *
      polarRay (θ - A.heading i.castSucc)) = (r : ℂ) * polarRay θ
    calc
      _ = (r : ℂ) * (polarRay (A.heading i.castSucc) *
          polarRay (θ - A.heading i.castSucc)) := by ring
      _ = _ := by rw [← polarRay_add, add_sub_cancel]

/-- At one full turn, terminal banks may coincide but no two genuine piece interiors overlap. -/
theorem nonoverlapping_of_totalAngle_le (width : A.totalAngle ≤ 2 * Real.pi) :
    A.Nonoverlapping := by
  intro i j different
  apply Set.disjoint_left.mpr
  intro z zi zj
  obtain ⟨r, rpos, θ, θbounds, θpoint⟩ := (A.mem_interior_faceImage_iff i z).mp zi
  obtain ⟨s, spos, φ, φbounds, φpoint⟩ := (A.mem_interior_faceImage_iff j z).mp zj
  have θglobal : θ ∈ Set.Ioo 0 A.totalAngle :=
    ⟨(A.heading_nonneg i.castSucc).trans_lt θbounds.1,
      θbounds.2.trans_le (A.heading_le_totalAngle i.succ)⟩
  have φglobal : φ ∈ Set.Ioo 0 A.totalAngle :=
    ⟨(A.heading_nonneg j.castSucc).trans_lt φbounds.1,
      φbounds.2.trans_le (A.heading_le_totalAngle j.succ)⟩
  let x : PolarStrip 0 A.totalAngle := (⟨r, rpos⟩, ⟨θ, θglobal⟩)
  let y : PolarStrip 0 A.totalAngle := (⟨s, spos⟩, ⟨φ, φglobal⟩)
  have equal : polarStripMap 0 A.totalAngle x = polarStripMap 0 A.totalAngle y :=
    θpoint.symm.trans φpoint
  have headings : θ = φ := congrArg (fun p : PolarStrip 0 A.totalAngle => p.2.val)
    (polarStripMap_injective 0 A.totalAngle (by simpa only [sub_zero] using width) equal)
  rcases lt_or_gt_of_ne different with ordered | ordered
  · have gap := A.heading_strictMono.monotone
      (show i.succ ≤ j.castSucc from Nat.succ_le_of_lt ordered)
    linarith [θbounds.2, φbounds.1]
  · have gap := A.heading_strictMono.monotone
      (show j.succ ≤ i.castSucc from Nat.succ_le_of_lt ordered)
    linarith [φbounds.2, θbounds.1]

end Unfoldings.AngularFan
