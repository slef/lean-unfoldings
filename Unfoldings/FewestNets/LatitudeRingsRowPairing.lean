module

public import Unfoldings.FewestNets.LatitudeRingsRowEdges

/-! Every triangle contributes exactly one side to the latitude intervals. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FewestNets.LatitudeRings

variable (G : LatitudeRings)

/-- The triangle at a named oriented ring side. True is its northern side. -/
def ringSideFace (p : RingEdge G × Bool) : ChordFace G :=
  if p.2 then northRingFace G p.1 else southRingFace G p.1

/-- Read the unique latitude side from the actual midpoint advance or polar sector. -/
def chordFaceRingSide : ChordFace G → RingEdge G × Bool
  | .inl b => (⟨0, b⟩, true)
  | .inr (.inl ⟨j, i⟩) =>
    match sweepOrder (rowSize G j.val) (rowSize G (j.val + 1)) i with
    | .inl b => (⟨j.castSucc, b⟩, false)
    | .inr b => (⟨j.succ, b⟩, true)
  | .inr (.inr b) => (⟨Fin.last (stripCount G), b⟩, false)

private theorem northRingFace_succ (j : Fin (stripCount G)) (b : Fin (rowSize G (j.val + 1))) :
    northRingFace G ⟨j.succ, b⟩ =
      .inr (.inl ⟨j, upperRank (sweepOrder _ _) b⟩) := by
  simp only [northRingFace, Fin.val_succ, Nat.succ_ne_zero]
  rfl

private theorem southRingFace_castSucc (j : Fin (stripCount G)) (b : Fin (rowSize G j.val)) :
    southRingFace G ⟨j.castSucc, b⟩ =
      .inr (.inl ⟨j, lowerRank (sweepOrder _ _) b⟩) := by
  simp only [southRingFace, Fin.val_castSucc, dite_eq_left j.isLt]

theorem ringSideFace_chordFaceRingSide (face : ChordFace G) :
    ringSideFace G (chordFaceRingSide G face) = face := by
  rcases face with b | ⟨j, i⟩ | b
  · simp [chordFaceRingSide, ringSideFace, northRingFace]
  · let step := sweepOrder (rowSize G j.val) (rowSize G (j.val + 1))
    unfold chordFaceRingSide
    change ringSideFace G (match step i with
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

private theorem ringEdge_ext (p q : RingEdge G) (row : p.1 = q.1)
    (site : p.2.val = q.2.val) : p = q :=
  Sigma.ext row ((Fin.heq_ext_iff (congrArg (fun r => rowSize G (Fin.val r)) row)).mpr site)

theorem chordFaceRingSide_ringSideFace (p : RingEdge G × Bool) :
    chordFaceRingSide G (ringSideFace G p) = p := by
  obtain ⟨⟨row, b⟩, side⟩ := p
  cases side with
  | false =>
    change chordFaceRingSide G (southRingFace G ⟨row, b⟩) = _
    unfold southRingFace
    split
    · rename_i strip
      let j : Fin (stripCount G) := ⟨row.val, strip⟩
      let step := sweepOrder (rowSize G j.val) (rowSize G (j.val + 1))
      change chordFaceRingSide G (.inr (.inl ⟨j, lowerRank step b⟩)) = _
      change (match step (step.symm (.inl b)) with
        | .inl k => ((⟨j.castSucc, k⟩ : RingEdge G), false)
        | .inr k => ((⟨j.succ, k⟩ : RingEdge G), true)) = _
      rw [step.apply_symm_apply]
      congr 1
    · rename_i no_strip
      change ¬ row.val < stripCount G at no_strip
      have bound := row.isLt
      have last : row.val = stripCount G := by omega
      change ((⟨Fin.last (stripCount G), Fin.cast (congrArg (rowSize G) last) b⟩ : RingEdge G), false) = _
      congr 1
      have equal : Fin.last (stripCount G) = row := Fin.ext last.symm
      exact Sigma.ext equal ((Fin.heq_ext_iff (congrArg (fun r : Fin (stripCount G + 1) =>
        rowSize G r.val) equal)).mpr rfl)
  | true =>
    change chordFaceRingSide G (northRingFace G ⟨row, b⟩) = _
    unfold northRingFace
    split
    · rename_i pole
      change ((⟨0, Fin.cast (congrArg (rowSize G) pole) b⟩ : RingEdge G), true) = _
      congr 1
      have equal : (0 : Fin (stripCount G + 1)) = row := Fin.ext pole.symm
      exact Sigma.ext equal ((Fin.heq_ext_iff (congrArg (fun r : Fin (stripCount G + 1) =>
        rowSize G r.val) equal)).mpr rfl)
    · rename_i away
      change row.val ≠ 0 at away
      have bound := row.isLt
      let j : Fin (stripCount G) := ⟨row.val - 1, by omega⟩
      have previous : j.val + 1 = row.val := by dsimp [j]; omega
      let d : Fin (rowSize G (j.val + 1)) := Fin.cast (congrArg (rowSize G) previous.symm) b
      let step := sweepOrder (rowSize G j.val) (rowSize G (j.val + 1))
      change chordFaceRingSide G (.inr (.inl ⟨j, upperRank step d⟩)) = _
      change (match step (step.symm (.inr d)) with
        | .inl k => ((⟨j.castSucc, k⟩ : RingEdge G), false)
        | .inr k => ((⟨j.succ, k⟩ : RingEdge G), true)) = _
      rw [step.apply_symm_apply]
      change (((⟨j.succ, d⟩ : RingEdge G), true)) = _
      exact congrArg (fun e : RingEdge G => (e, true))
        (ringEdge_ext G ⟨j.succ, d⟩ ⟨row, b⟩ (Fin.ext previous) rfl)

/-- The latitude sides of the actual triangles and the two sides of each row interval are equivalent. -/
def chordFaceRingEquiv : ChordFace G ≃ RingEdge G × Bool :=
  ⟨chordFaceRingSide G, ringSideFace G, ringSideFace_chordFaceRingSide G,
    chordFaceRingSide_ringSideFace G⟩

/-- Pairing the latitude side is an involution on the actual triangles. -/
def ringFaceMate (i : ChordFace G) : ChordFace G :=
  let e := chordFaceRingEquiv G i
  (chordFaceRingEquiv G).symm (e.1, !e.2)

theorem ringFaceMate_involutive : Function.Involutive (ringFaceMate G) := by
  intro i
  apply (chordFaceRingEquiv G).injective
  simp [ringFaceMate]

theorem ringFaceMate_opposite (i : ChordFace G) :
    orientedChordEdge (chordVertices G (ringFaceMate G i)) (ringSlot (ringFaceMate G i)) =
      (orientedChordEdge (chordVertices G i) (ringSlot i)).swap := by
  obtain ⟨⟨e, side⟩, rfl⟩ := (chordFaceRingEquiv G).symm.surjective i
  unfold ringFaceMate
  simp only [Equiv.apply_symm_apply]
  cases side
  · exact ringFaces_opposite G e
  · have pair := ringFaces_opposite G e
    exact (congrArg Prod.swap pair).symm

end Unfoldings.FewestNets.LatitudeRings
