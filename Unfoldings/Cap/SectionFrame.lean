module

public import Unfoldings.Cap.SectionMidpoints
public import Unfoldings.Cap.VertexProgress
public import Unfoldings.Geometry.PositiveDirectionFrame

/-!
# Positively oriented horizontal coordinates on regular cap sections

Every original vertex stays strictly off the section axis. Actual interior
sample points have zero transverse coordinate and strictly increasing horizontal
coordinates. These properties identify genuine ray-counter changes without
endpoint conventions at original vertices.
-/

@[expose] public section

noncomputable section

namespace Unfoldings

namespace ConvexCap

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexCap C)

/-- Complete original-vertex avoidance gives strictly nonzero transverse vertex coordinates. -/
theorem projectedVertex_off_section_axis {p q : Plane} (different : p ≠ q)
    (regular : ∀ t : ℝ, ∀ f j, AffineMap.lineMap p q t ≠ (K.projectedTriangle f).vertex j)
    (v : C.Vertex Set.univ) :
    positiveDirectionFrame (q - p) (K.projectedVertex v - p) 1 ≠ 0 := by
  intro zero
  obtain ⟨t, on_line⟩ := exists_lineMap_of_positiveFrame_vertical_zero different zero
  obtain ⟨⟨f, j⟩, rfl⟩ := C.vertexOfCorner_surjective Set.univ v
  exact regular t f j on_line.symm

namespace SectionFaceTrace

variable {K} {p q : Plane} (T : K.SectionFaceTrace p q)

theorem middleTime_between (i : Fin (T.turns + 1)) :
    (T.time i.castSucc : ℝ) < T.middleTime i ∧ T.middleTime i < (T.time i.succ : ℝ) := by
  have positive := T.time_step_pos i
  unfold middleTime
  constructor <;> linarith

theorem middleTime_increasing : StrictMono T.middleTime := by
  apply Fin.strictMono_iff_lt_succ.mpr
  intro i
  have first := (T.middleTime_between i.castSucc).2
  have last := (T.middleTime_between i.succ).1
  rw [Fin.succ_castSucc] at first
  exact first.trans last

/-- Actual interior sample coordinates use the same real section parameter. -/
theorem middlePoint_frame_horizontal (i : Fin (T.turns + 1)) :
    positiveDirectionFrame (q - p) (T.middlePoint i - p) 0 = T.middleTime i * ‖q - p‖ := by
  rw [T.middlePoint_eq_section, AffineMap.lineMap_apply_module', add_sub_cancel_right, map_smul]
  change T.middleTime i * positiveDirectionFrame (q - p) (q - p) 0 = _
  rw [positiveDirectionFrame_horizontal]

theorem middlePoint_frame_vertical (i : Fin (T.turns + 1)) :
    positiveDirectionFrame (q - p) (T.middlePoint i - p) 1 = 0 := by
  rw [T.middlePoint_eq_section, AffineMap.lineMap_apply_module', add_sub_cancel_right, map_smul]
  change T.middleTime i * positiveDirectionFrame (q - p) (q - p) 1 = 0
  rw [positiveDirectionFrame_vertical, mul_zero]

end SectionFaceTrace
end ConvexCap
end Unfoldings
