module

public import Unfoldings.FewestNets.AcuteLatitudeRingEdges

/-! Every triangle contributes exactly one side to the latitude intervals. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FewestNets.AcuteLatitudeGrid

variable (a : ℝ)

/-- The triangle at a named oriented ring side. True is its northern side. -/
def ringSideFace (p : RingEdge a × Bool) : ChordFace a :=
  if p.2 then northRingFace a p.1 else southRingFace a p.1

/-- Read the unique latitude side from the actual midpoint advance or polar sector. -/
def chordFaceRingSide : ChordFace a → RingEdge a × Bool
  | .inl b => (⟨0, b⟩, true)
  | .inr (.inl ⟨j, i⟩) =>
    match sweepOrder (rowSize a j.val) (rowSize a (j.val + 1)) i with
    | .inl b => (⟨j.castSucc, b⟩, false)
    | .inr b => (⟨j.succ, b⟩, true)
  | .inr (.inr b) => (⟨Fin.last (stripCount a), b⟩, false)

private theorem northRingFace_succ (j : Fin (stripCount a)) (b : Fin (rowSize a (j.val + 1))) :
    northRingFace a ⟨j.succ, b⟩ =
      .inr (.inl ⟨j, upperRank (sweepOrder _ _) b⟩) := by
  simp only [northRingFace, Fin.val_succ, Nat.succ_ne_zero]
  rfl

private theorem southRingFace_castSucc (j : Fin (stripCount a)) (b : Fin (rowSize a j.val)) :
    southRingFace a ⟨j.castSucc, b⟩ =
      .inr (.inl ⟨j, lowerRank (sweepOrder _ _) b⟩) := by
  simp only [southRingFace, Fin.val_castSucc, dite_eq_left j.isLt]

theorem ringSideFace_chordFaceRingSide (face : ChordFace a) :
    ringSideFace a (chordFaceRingSide a face) = face := by
  rcases face with b | ⟨j, i⟩ | b
  · simp [chordFaceRingSide, ringSideFace, northRingFace]
  · let step := sweepOrder (rowSize a j.val) (rowSize a (j.val + 1))
    unfold chordFaceRingSide
    change ringSideFace a (match step i with
      | .inl b => (⟨j.castSucc, b⟩, false)
      | .inr b => (⟨j.succ, b⟩, true)) = _
    cases advance : step i with
    | inl d =>
      rw [ringSideFace, ite_eq_right (by decide : false ≠ true), southRingFace_castSucc]
      unfold lowerRank
      rw [← advance, step.symm_apply_apply]
    | inr d =>
      rw [ringSideFace, ite_eq_left rfl, northRingFace_succ]
      unfold upperRank
      rw [← advance, step.symm_apply_apply]
  · simp [chordFaceRingSide, ringSideFace, southRingFace]

private theorem ringEdge_ext (p q : RingEdge a) (row : p.1 = q.1)
    (site : p.2.val = q.2.val) : p = q :=
  Sigma.ext row ((Fin.heq_ext_iff (congrArg (fun r => rowSize a (Fin.val r)) row)).mpr site)

theorem chordFaceRingSide_ringSideFace (p : RingEdge a × Bool) :
    chordFaceRingSide a (ringSideFace a p) = p := by
  obtain ⟨⟨row, b⟩, side⟩ := p
  cases side with
  | false =>
    change chordFaceRingSide a (southRingFace a ⟨row, b⟩) = _
    unfold southRingFace
    split
    · rename_i strip
      let j : Fin (stripCount a) := ⟨row.val, strip⟩
      let step := sweepOrder (rowSize a j.val) (rowSize a (j.val + 1))
      change chordFaceRingSide a (.inr (.inl ⟨j, lowerRank step b⟩)) = _
      change (match step (step.symm (.inl b)) with
        | .inl k => ((⟨j.castSucc, k⟩ : RingEdge a), false)
        | .inr k => ((⟨j.succ, k⟩ : RingEdge a), true)) = _
      rw [step.apply_symm_apply]
      congr 1
    · rename_i no_strip
      change ¬ row.val < stripCount a at no_strip
      have bound := row.isLt
      have last : row.val = stripCount a := by omega
      change ((⟨Fin.last (stripCount a), Fin.cast (congrArg (rowSize a) last) b⟩ : RingEdge a), false) = _
      congr 1
      have equal : Fin.last (stripCount a) = row := Fin.ext last.symm
      exact Sigma.ext equal ((Fin.heq_ext_iff (congrArg (fun r : Fin (stripCount a + 1) =>
        rowSize a r.val) equal)).mpr rfl)
  | true =>
    change chordFaceRingSide a (northRingFace a ⟨row, b⟩) = _
    unfold northRingFace
    split
    · rename_i pole
      change ((⟨0, Fin.cast (congrArg (rowSize a) pole) b⟩ : RingEdge a), true) = _
      congr 1
      have equal : (0 : Fin (stripCount a + 1)) = row := Fin.ext pole.symm
      exact Sigma.ext equal ((Fin.heq_ext_iff (congrArg (fun r : Fin (stripCount a + 1) =>
        rowSize a r.val) equal)).mpr rfl)
    · rename_i away
      change row.val ≠ 0 at away
      have bound := row.isLt
      let j : Fin (stripCount a) := ⟨row.val - 1, by omega⟩
      have previous : j.val + 1 = row.val := by dsimp [j]; omega
      let d : Fin (rowSize a (j.val + 1)) := Fin.cast (congrArg (rowSize a) previous.symm) b
      let step := sweepOrder (rowSize a j.val) (rowSize a (j.val + 1))
      change chordFaceRingSide a (.inr (.inl ⟨j, upperRank step d⟩)) = _
      change (match step (step.symm (.inr d)) with
        | .inl k => ((⟨j.castSucc, k⟩ : RingEdge a), false)
        | .inr k => ((⟨j.succ, k⟩ : RingEdge a), true)) = _
      rw [step.apply_symm_apply]
      change (((⟨j.succ, d⟩ : RingEdge a), true)) = _
      exact congrArg (fun e : RingEdge a => (e, true))
        (ringEdge_ext a ⟨j.succ, d⟩ ⟨row, b⟩ (Fin.ext previous) rfl)

/-- The latitude sides of the actual triangles and the two sides of each row interval are equivalent. -/
def chordFaceRingEquiv : ChordFace a ≃ RingEdge a × Bool :=
  ⟨chordFaceRingSide a, ringSideFace a, ringSideFace_chordFaceRingSide a,
    chordFaceRingSide_ringSideFace a⟩

/-- Pairing the latitude side is an involution on the actual triangles. -/
def ringFaceMate (i : ChordFace a) : ChordFace a :=
  let e := chordFaceRingEquiv a i
  (chordFaceRingEquiv a).symm (e.1, !e.2)

theorem ringFaceMate_involutive : Function.Involutive (ringFaceMate a) := by
  intro i
  apply (chordFaceRingEquiv a).injective
  simp [ringFaceMate]

theorem ringFaceMate_opposite (i : ChordFace a) :
    orientedChordEdge (chordVertices a (ringFaceMate a i)) (ringSlot (ringFaceMate a i)) =
      (orientedChordEdge (chordVertices a i) (ringSlot i)).swap := by
  obtain ⟨⟨e, side⟩, rfl⟩ := (chordFaceRingEquiv a).symm.surjective i
  unfold ringFaceMate
  simp only [Equiv.apply_symm_apply]
  cases side
  · exact ringFaces_opposite a e
  · have pair := ringFaces_opposite a e
    exact (congrArg Prod.swap pair).symm

end Unfoldings.FewestNets.AcuteLatitudeGrid
