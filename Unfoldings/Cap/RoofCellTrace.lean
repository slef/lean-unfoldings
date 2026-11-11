module

public import Unfoldings.Cap.RoofExtension
public import Unfoldings.Cap.FaceDirections
public import Unfoldings.Geometry.FiniteConvexTrace

/-!
# Actual finite polygonal traces on the unbounded roof

Every horizontal segment, including those outside the original footprint,
has a finite strictly ordered trace in actual active support cells. Its
spatial secants use the original supporting face's actual tangent map.
-/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexCap C)

structure RoofCellTrace (p q : Plane) where
  turns : ℕ
  time : Fin (turns + 2) → unitInterval
  increasing : StrictMono time
  start : time 0 = 0
  finish : time (Fin.last (turns + 1)) = 1
  face : Fin (turns + 1) → Face
  contained : ∀ i, ∀ t ∈ Set.Icc (time i.castSucc) (time i.succ),
    AffineMap.lineMap p q (t : ℝ) ∈ K.roofCell (face i)

/-- Construct a whole-piece active-face trace anywhere on the extended roof. -/
def roofCellTrace (p q : Plane) : K.RoofCellTrace p q :=
  Classical.choice (by
    obtain ⟨n, positive, time, increasing, start, finish, face, inside⟩ :=
      exists_finite_closed_convex_segment_partition K.roofCell K.isClosed_roofCell
        K.convex_roofCell p q (fun x _ => K.roofCells_cover x)
    cases n with
    | zero => exact (Nat.lt_irrefl 0 positive).elim
    | succ n => exact ⟨⟨n, time, increasing, start, finish, face, inside⟩⟩)

namespace RoofCellTrace

variable {K} {p q : Plane} (T : K.RoofCellTrace p q)

def point (i : Fin (T.turns + 2)) : Plane := AffineMap.lineMap p q (T.time i : ℝ)

def spatialPoint (i : Fin (T.turns + 2)) : Space := K.roofPoint (T.point i)

theorem point_mem_first (i : Fin (T.turns + 1)) : T.point i.castSucc ∈ K.roofCell (T.face i) :=
  T.contained i (T.time i.castSucc) ⟨le_rfl, (T.increasing Fin.castSucc_lt_succ).le⟩

theorem point_mem_last (i : Fin (T.turns + 1)) : T.point i.succ ∈ K.roofCell (T.face i) :=
  T.contained i (T.time i.succ) ⟨(T.increasing Fin.castSucc_lt_succ).le, le_rfl⟩

/-- Each true spatial secant of the extended roof is an actual supporting-face tangent. -/
theorem spatialPoint_sub (i : Fin (T.turns + 1)) :
    T.spatialPoint i.succ - T.spatialPoint i.castSucc =
      ((T.time i.succ : ℝ) - (T.time i.castSucc : ℝ)) •
        K.spatialDirection (T.face i) (q - p) := by
  have first := (K.mem_roofCell_iff _ _).mp (T.point_mem_first i)
  have last := (K.mem_roofCell_iff _ _).mp (T.point_mem_last i)
  have height : K.roofHeight (T.point i.succ) - K.roofHeight (T.point i.castSucc) =
      -inner ℝ (K.normalSlope (T.face i)) (T.point i.succ - T.point i.castSucc) := by
    rw [first, last, K.supportHeight_difference]
    ring
  have difference : T.spatialPoint i.succ - T.spatialPoint i.castSucc =
      K.spatialDirection (T.face i) (T.point i.succ - T.point i.castSucc) := by
    rw [K.spatialDirection_eq_section]
    ext j
    fin_cases j
    · rfl
    · rfl
    · exact height
  have chord : T.point i.succ - T.point i.castSucc =
      ((T.time i.succ : ℝ) - (T.time i.castSucc : ℝ)) • (q - p) := by
    simp only [point, AffineMap.lineMap_apply_module']
    module
  rw [difference, chord]
  simp only [spatialDirection, pullbackDirection, map_smul]

end RoofCellTrace
end Unfoldings.ConvexCap
