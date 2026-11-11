module

public import Unfoldings.Cap.SectionPartition
public import Unfoldings.Cap.FaceDirections

/-!
# Actual section pieces and their spatial tangent vectors

Bundle the constructed finite original-face trace. Each spatial secant equals
the true tangent vector of its original face multiplied by its positive time
increment. Face transitions and cut-crossing rotations are further obligations.
-/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexCap C)

structure SectionFaceTrace (p q : Plane) where
  turns : ℕ
  time : Fin (turns + 2) → unitInterval
  increasing : StrictMono time
  start : time 0 = 0
  finish : time (Fin.last (turns + 1)) = 1
  face : Fin (turns + 1) → Face
  contained : ∀ i, ∀ t ∈ Set.Icc (time i.castSucc) (time i.succ),
    AffineMap.lineMap p q (t : ℝ) ∈ (K.projectedTriangle (face i)).carrier

/-- The trace and its original face labels are constructed from actual cap geometry. -/
def sectionFaceTrace {p q : Plane} (first : p ∈ K.footprint) (last : q ∈ K.footprint) :
    K.SectionFaceTrace p q :=
  Classical.choice (by
    obtain ⟨n, positive, time, increasing, start, finish, face, inside⟩ :=
      K.exists_section_face_partition first last
    cases n with
    | zero => exact (Nat.lt_irrefl 0 positive).elim
    | succ n => exact ⟨⟨n, time, increasing, start, finish, face, inside⟩⟩)

/-- Height increments within one actual original face have its actual normal slope. -/
theorem roofHeight_sub_of_face (f : Face) {p q : Plane}
    (first : p ∈ (K.projectedTriangle f).carrier) (last : q ∈ (K.projectedTriangle f).carrier) :
    K.roofHeight q - K.roofHeight p = -inner ℝ (K.normalSlope f) (q - p) := by
  rw [K.roofHeight_eq_supportHeight_of_mem f first, K.roofHeight_eq_supportHeight_of_mem f last,
    K.supportHeight_difference]
  ring

namespace SectionFaceTrace

variable {K} {p q : Plane} (T : K.SectionFaceTrace p q)

def point (i : Fin (T.turns + 2)) : Plane := AffineMap.lineMap p q (T.time i : ℝ)

def spatialPoint (i : Fin (T.turns + 2)) : Space :=
  Cap.horizontalAtHeight (T.point i) (K.roofHeight (T.point i))

theorem point_mem_face_first (i : Fin (T.turns + 1)) :
    T.point i.castSucc ∈ (K.projectedTriangle (T.face i)).carrier :=
  T.contained i (T.time i.castSucc) ⟨le_rfl, (T.increasing Fin.castSucc_lt_succ).le⟩

theorem point_mem_face_last (i : Fin (T.turns + 1)) :
    T.point i.succ ∈ (K.projectedTriangle (T.face i)).carrier :=
  T.contained i (T.time i.succ) ⟨(T.increasing Fin.castSucc_lt_succ).le, le_rfl⟩

theorem point_sub (i : Fin (T.turns + 1)) : T.point i.succ - T.point i.castSucc =
    ((T.time i.succ : ℝ) - (T.time i.castSucc : ℝ)) • (q - p) := by
  simp only [point, AffineMap.lineMap_apply_module']
  module

/-- Every actual spatial secant is the tangent vector of its actual labeled original face. -/
theorem spatialPoint_sub (i : Fin (T.turns + 1)) :
    T.spatialPoint i.succ - T.spatialPoint i.castSucc =
      ((T.time i.succ : ℝ) - (T.time i.castSucc : ℝ)) •
        K.spatialDirection (T.face i) (q - p) := by
  have height := K.roofHeight_sub_of_face (T.face i)
    (T.point_mem_face_first i) (T.point_mem_face_last i)
  have difference : T.spatialPoint i.succ - T.spatialPoint i.castSucc =
      K.spatialDirection (T.face i) (T.point i.succ - T.point i.castSucc) := by
    rw [K.spatialDirection_eq_section]
    ext j
    fin_cases j
    · change T.point i.succ 0 - T.point i.castSucc 0 = (T.point i.succ - T.point i.castSucc) 0
      rfl
    · change T.point i.succ 1 - T.point i.castSucc 1 = (T.point i.succ - T.point i.castSucc) 1
      rfl
    · exact height
  rw [difference, T.point_sub]
  simp only [spatialDirection, pullbackDirection, map_smul]

/-- The trace's real time increments are all strictly positive. -/
theorem time_step_pos (i : Fin (T.turns + 1)) :
    0 < (T.time i.succ : ℝ) - (T.time i.castSucc : ℝ) :=
  sub_pos.mpr (T.increasing Fin.castSucc_lt_succ)

end SectionFaceTrace
end Unfoldings.ConvexCap
