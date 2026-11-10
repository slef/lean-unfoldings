module

public import Unfoldings.Polyhedron.GermDirections
public import Unfoldings.Complex.LinkOrdering
public import Unfoldings.Geometry.AngularCrofton

/-! Angular crossing integrals of the actual spatial vertex link. -/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialFolding

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  (F : SpatialFolding C)

theorem germDirection_angle (p : C.Germ) :
    InnerProductGeometry.angle (F.germDirection p) (F.germDirection (C.turnGerm p)) =
      (C.triangle p.1.1).cornerAngle p.1.2 := by
  obtain ⟨⟨f, i⟩, side⟩ := p
  cases side
  · exact (F.place f).angle_map _ _ _
  · exact ((F.place f).angle_map _ _ _).trans (EuclideanGeometry.angle_comm _ _ _)

variable {retain : Set C.Seam} {v : C.Vertex retain} {n : ℕ}
  (c : (C.linkSystem retain v).Chain n)

theorem germDirection_chain_rotates
    (closes : C.linkMate retain v (C.linkTurn retain v c.last) = c.first)
    (i : Fin (n + 1)) :
    F.germDirection (C.linkTurn retain v (c.point i)).val =
      F.germDirection (c.point (finRotate (n + 1) i)).val := by
  refine Fin.lastCases ?_ (fun k => ?_) i
  · rw [finRotate_last]
    have equal := congrArg (fun p : C.LinkGerm retain v => F.germDirection p.val) closes
    change F.germDirection (C.mateGerm retain
      (C.linkTurn retain v (c.point (Fin.last n))).val) =
      F.germDirection (c.point 0).val at equal
    simpa only [F.germDirection_mate] using equal
  · rw [show finRotate (n + 1) k.castSucc = k.succ from finRotate_of_lt k.isLt]
    have equal := congrArg (fun p : C.LinkGerm retain v => F.germDirection p.val) (c.next k)
    change F.germDirection (C.mateGerm retain
      (C.linkTurn retain v (c.point k.castSucc)).val) = _ at equal
    simpa only [F.germDirection_mate] using equal

/-- A closed chain represents every actual link direction, including the turned germs. -/
theorem exists_chain_germDirection_iff
    (closes : C.linkMate retain v (C.linkTurn retain v c.last) = c.first)
    (covers : ∀ p, c.Visited p) (P : Space → Prop) :
    (∃ i, P (F.germDirection (c.point i).val)) ↔
      ∃ p : C.LinkGerm retain v, P (F.germDirection p.val) := by
  constructor
  · rintro ⟨i, hi⟩
    exact ⟨c.point i, hi⟩
  · rintro ⟨p, hp⟩
    obtain ⟨i, equal | equal⟩ := covers p
    · exact ⟨i, equal ▸ hp⟩
    · rw [equal] at hp
      change P (F.germDirection (C.linkTurn retain v (c.point i)).val) at hp
      rw [F.germDirection_chain_rotates c closes] at hp
      exact ⟨finRotate (n + 1) i, hp⟩

theorem sum_germDirection_angles
    (closes : C.linkMate retain v (C.linkTurn retain v c.last) = c.first)
    (covers : ∀ p, c.Visited p) :
    (∑ i : Fin (n + 1), InnerProductGeometry.angle (F.germDirection (c.point i).val)
      (F.germDirection (c.point (finRotate (n + 1) i)).val)) = C.totalAngle retain v := by
  calc
    _ = ∑ i : Fin (n + 1), (C.triangle (c.point i).val.1.1).cornerAngle
        (c.point i).val.1.2 := by
      apply Finset.sum_congr rfl
      intro i _
      rw [← F.germDirection_chain_rotates c closes i]
      exact F.germDirection_angle (c.point i).val
    _ = C.totalAngle retain v := C.sum_linkCornerAngle retain v c covers

/-- No convexity is needed for the actual link's crossing integral. -/
theorem lintegral_link_crossings
    (closes : C.linkMate retain v (C.linkTurn retain v c.last) = c.first)
    (covers : ∀ p, c.Visited p) (f : Space →L[ℝ] ℝ) (nonzero : f ≠ 0) :
    (∫⁻ z in {z | 0 < f z}, angularCrossings
      (fun i => F.germDirection (c.point i).val) (finRotate (n + 1)) z ∂solidAngleMeasure) =
      ENNReal.ofReal (2 * C.totalAngle retain v) := by
  rw [lintegral_angularCrossings _ _ (fun i => F.germDirection_ne_zero _) f nonzero,
    F.sum_germDirection_angles c closes covers]

end Unfoldings.SpatialFolding
