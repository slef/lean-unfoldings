module

public import Unfoldings.FewestNets.LatitudeChordMesh
public import Unfoldings.FewestNets.LatitudeSweepPairing

/-! Each latitude segment has its two named incident triangles, including at the polar rows. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FewestNets.AcuteLatitudeGrid

/-- A longitude interval on any of the boundary or interior rows. -/
abbrev RingEdge (a : ℝ) := Σ j : Fin (stripCount a + 1), Fin (rowSize a j.val)

/-- The triangular side on the north of a latitude interval. -/
def northRingFace (a : ℝ) (e : RingEdge a) : ChordFace a :=
  if at_pole : e.1.val = 0 then
    .inl (Fin.cast (congrArg (rowSize a) at_pole) e.2)
  else
    let j : Fin (stripCount a) := ⟨e.1.val - 1, by omega⟩
    have previous : j.val + 1 = e.1.val := by dsimp [j]; omega
    let b : Fin (rowSize a (j.val + 1)) := Fin.cast (congrArg (rowSize a) previous.symm) e.2
    .inr (.inl ⟨j, upperRank (sweepOrder _ _) b⟩)

/-- The triangular side on the south of the same latitude interval. -/
def southRingFace (a : ℝ) (e : RingEdge a) : ChordFace a :=
  if annular : e.1.val < stripCount a then
    let j : Fin (stripCount a) := ⟨e.1.val, annular⟩
    .inr (.inl ⟨j, lowerRank (sweepOrder _ _) e.2⟩)
  else
    have last : e.1.val = stripCount a := by omega
    .inr (.inr (Fin.cast (congrArg (rowSize a) last) e.2))

/-- The edge index of the latitude side in each ordered triangle. -/
def ringSlot {a : ℝ} : ChordFace a → Fin 3
  | .inl _ | .inr (.inr _) => 0
  | .inr (.inl _) => 2

/-- The northern triangle traverses the row interval from east to west. -/
theorem northRingFace_edge (a : ℝ) (e : RingEdge a) :
    orientedChordEdge (chordVertices a (northRingFace a e)) (ringSlot (northRingFace a e)) =
      (rowSite a e.1.val (e.2.val + 1), rowSite a e.1.val e.2.val) := by
  unfold northRingFace
  split
  · rename_i at_pole
    simp only [ringSlot, chordVertices, orientedChordEdge, Fin.val_cast]
    change (rowSite a 0 (e.2.val + 1), rowSite a 0 e.2.val) = _
    exact congrArg (fun row => (rowSite a row (e.2.val + 1), rowSite a row e.2.val)) at_pole.symm
  · rename_i away
    let j : Fin (stripCount a) := ⟨e.1.val - 1, by omega⟩
    have previous : j.val + 1 = e.1.val := by dsimp [j]; omega
    let b : Fin (rowSize a (j.val + 1)) := Fin.cast (congrArg (rowSize a) previous.symm) e.2
    let step := sweepOrder (rowSize a j.val) (rowSize a (j.val + 1))
    change orientedChordEdge (latitudeSweepChordVertices a j.val step (upperRank step b)) 2 = _
    unfold latitudeSweepChordVertices upperRank
    rw [step.apply_symm_apply]
    change (rowSite a (j.val + 1) (b.val + 1), rowSite a (j.val + 1) b.val) = _
    rw [show b.val = e.2.val from rfl, previous]

/-- The southern triangle traverses the same interval from west to east. -/
theorem southRingFace_edge (a : ℝ) (e : RingEdge a) :
    orientedChordEdge (chordVertices a (southRingFace a e)) (ringSlot (southRingFace a e)) =
      (rowSite a e.1.val e.2.val, rowSite a e.1.val (e.2.val + 1)) := by
  unfold southRingFace
  split
  · rename_i annular
    let step := sweepOrder (rowSize a e.1.val) (rowSize a (e.1.val + 1))
    change orientedChordEdge (latitudeSweepChordVertices a e.1.val step (lowerRank step e.2)) 2 = _
    unfold latitudeSweepChordVertices lowerRank
    rw [step.apply_symm_apply]
    rfl
  · rename_i no_strip
    have last : e.1.val = stripCount a := by omega
    simp only [ringSlot, chordVertices, orientedChordEdge, Fin.val_cast]
    change (rowSite a (stripCount a) e.2.val, rowSite a (stripCount a) (e.2.val + 1)) = _
    exact congrArg (fun row => (rowSite a row e.2.val, rowSite a row (e.2.val + 1))) last.symm

/-- The two actual row sides have exactly reversed endpoints. -/
theorem ringFaces_opposite (a : ℝ) (e : RingEdge a) :
    orientedChordEdge (chordVertices a (northRingFace a e)) (ringSlot (northRingFace a e)) =
      (orientedChordEdge (chordVertices a (southRingFace a e)) (ringSlot (southRingFace a e))).swap := by
  rw [northRingFace_edge, southRingFace_edge]
  rfl

end Unfoldings.FewestNets.AcuteLatitudeGrid
