module

public import Unfoldings.Development.SingleSeam
public import Unfoldings.Cap.RetainedSectionTurn
public import Unfoldings.Cap.SectionSeams
public import Unfoldings.Cap.SectionTraceTurns

/-!
# Constructed intrinsic turns of vertex-avoiding straight sections

Each actual crossing is unfolded using its genuine outward hinge, without a
global development of the curved cap. The resulting total absolute intrinsic
turn is at most twice the tilt, independently of the number of crossed faces.
This is weaker than the paper's sharp twice-tilt-times-sine bound.
-/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexCap C)

/-- The genuine absolute intrinsic section turn in the constructed outward original hinge. -/
def intrinsicSectionTurn (s : C.Seam) (direction : Plane) : ℝ :=
  let D := C.singleSeamDevelopment s (K.folding.incident_faces_ne s)
  InnerProductGeometry.angle (D.developedDirection K (C.left s).face direction)
    (D.developedDirection K (C.right s).face direction)

theorem intrinsicSectionTurn_nonneg (s : C.Seam) (direction : Plane) :
    0 ≤ K.intrinsicSectionTurn s direction := InnerProductGeometry.angle_nonneg _ _

/-- The actual local intrinsic bend is no greater than the spatial bend of that same section. -/
theorem intrinsicSectionTurn_le_spatial (s : C.Seam) (direction : Plane)
    (transverse : orient 0 (K.projectedSeamVector s) direction ≠ 0) :
    K.intrinsicSectionTurn s direction ≤
      InnerProductGeometry.angle (K.spatialDirection (C.left s).face direction)
        (K.spatialDirection (C.right s).face direction) :=
  (C.singleSeamDevelopment s (K.folding.incident_faces_ne s)).retained_section_angle_le K s
    (Set.mem_singleton s) direction transverse

namespace SectionFaceTrace

variable {K} {p q : Plane} (T : K.SectionFaceTrace p q) (different : p ≠ q)
  (regular : ∀ t : ℝ, ∀ f j, AffineMap.lineMap p q t ≠ (K.projectedTriangle f).vertex j)

open Classical in
/-- Repeated labels give zero; every changed label uses its constructed actual transverse seam. -/
def intrinsicTurn (i : Fin T.turns) : ℝ :=
  if changes : T.face i.castSucc ≠ T.face i.succ then
    K.intrinsicSectionTurn
      (T.exists_transverse_adjacent_seam different regular i changes).choose (q - p)
  else 0

include different regular in
open Classical in
theorem intrinsicTurn_nonneg (i : Fin T.turns) : 0 ≤ T.intrinsicTurn different regular i := by
  unfold intrinsicTurn
  split_ifs
  · exact K.intrinsicSectionTurn_nonneg _ _
  · exact le_rfl

include different regular in
open Classical in
/-- Every original-face transition is bounded using its actual two original spatial tangents. -/
theorem intrinsicTurn_le_spatial (i : Fin T.turns) :
    T.intrinsicTurn different regular i ≤
      InnerProductGeometry.angle (K.spatialDirection (T.face i.castSucc) (q - p))
        (K.spatialDirection (T.face i.succ) (q - p)) := by
  unfold intrinsicTurn
  split_ifs with changes
  · let s := (T.exists_transverse_adjacent_seam different regular i changes).choose
    obtain ⟨faces, _, transverse⟩ :=
      (T.exists_transverse_adjacent_seam different regular i changes).choose_spec
    change ((C.left s).face = T.face i.castSucc ∧ (C.right s).face = T.face i.succ) ∨
      ((C.right s).face = T.face i.castSucc ∧ (C.left s).face = T.face i.succ) at faces
    change K.intrinsicSectionTurn s (q - p) ≤ _
    have bound := K.intrinsicSectionTurn_le_spatial s (q - p) transverse
    rcases faces with ⟨left, right⟩ | ⟨right, left⟩
    · simpa only [left, right] using bound
    · simpa only [left, right, InnerProductGeometry.angle_comm] using bound
  · exact InnerProductGeometry.angle_nonneg _ _

include different regular in
open Classical in
/-- Actual absolute intrinsic section turning is uniformly bounded before the mesh is supplied. -/
theorem sum_intrinsicTurn_le_tilt {φ : ℝ} (nonnegative : 0 ≤ φ) (small : φ < Real.pi / 2)
    (tilt : K.TiltBound φ) :
    (∑ i, T.intrinsicTurn different regular i) ≤ 2 * φ :=
  (Finset.sum_le_sum (fun i _ => T.intrinsicTurn_le_spatial different regular i)).trans
    (T.sum_spatialDirection_turn_le_tilt different nonnegative small tilt)

end SectionFaceTrace
end Unfoldings.ConvexCap
