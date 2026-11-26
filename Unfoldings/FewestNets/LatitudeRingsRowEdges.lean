module

public import Unfoldings.FewestNets.LatitudeRingsChordMesh
public import Unfoldings.FewestNets.LatitudeRingsSweepPairing

/-! Each latitude segment has its two named incident triangles, including at the polar rows. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FewestNets.LatitudeRings

/-- A longitude interval on any of the boundary or interior rows. -/
abbrev RingEdge (G : LatitudeRings) := Σ j : Fin (stripCount G + 1), Fin (rowSize G j.val)

/-- The triangular side on the north of a latitude interval. -/
def northRingFace (G : LatitudeRings) (e : RingEdge G) : ChordFace G :=
  if at_pole : e.1.val = 0 then
    .inl (Fin.cast (congrArg (rowSize G) at_pole) e.2)
  else
    let j : Fin (stripCount G) := ⟨e.1.val - 1, by omega⟩
    have previous : j.val + 1 = e.1.val := by dsimp [j]; omega
    let b : Fin (rowSize G (j.val + 1)) := Fin.cast (congrArg (rowSize G) previous.symm) e.2
    .inr (.inl ⟨j, upperRank (sweepOrder _ _) b⟩)

/-- The triangular side on the south of the same latitude interval. -/
def southRingFace (G : LatitudeRings) (e : RingEdge G) : ChordFace G :=
  if annular : e.1.val < stripCount G then
    let j : Fin (stripCount G) := ⟨e.1.val, annular⟩
    .inr (.inl ⟨j, lowerRank (sweepOrder _ _) e.2⟩)
  else
    have last : e.1.val = stripCount G := by omega
    .inr (.inr (Fin.cast (congrArg (rowSize G) last) e.2))

/-- The edge index of the latitude side in each ordered triangle. -/
def ringSlot {G : LatitudeRings} : ChordFace G → Fin 3
  | .inl _ | .inr (.inr _) => 0
  | .inr (.inl _) => 2

/-- The northern triangle traverses the row interval from east to west. -/
theorem northRingFace_edge (G : LatitudeRings) (e : RingEdge G) :
    orientedChordEdge (chordVertices G (northRingFace G e)) (ringSlot (northRingFace G e)) =
      (rowSite G e.1.val (e.2.val + 1), rowSite G e.1.val e.2.val) := by
  unfold northRingFace
  split
  · rename_i at_pole
    simp only [ringSlot, chordVertices, orientedChordEdge, Fin.val_cast]
    change (rowSite G 0 (e.2.val + 1), rowSite G 0 e.2.val) = _
    exact congrArg (fun row => (rowSite G row (e.2.val + 1), rowSite G row e.2.val)) at_pole.symm
  · rename_i away
    let j : Fin (stripCount G) := ⟨e.1.val - 1, by omega⟩
    have previous : j.val + 1 = e.1.val := by dsimp [j]; omega
    let b : Fin (rowSize G (j.val + 1)) := Fin.cast (congrArg (rowSize G) previous.symm) e.2
    let step := sweepOrder (rowSize G j.val) (rowSize G (j.val + 1))
    change orientedChordEdge (latitudeSweepChordVertices G j.val step (upperRank step b)) 2 = _
    unfold latitudeSweepChordVertices upperRank
    rw [step.apply_symm_apply]
    change (rowSite G (j.val + 1) (b.val + 1), rowSite G (j.val + 1) b.val) = _
    rw [show b.val = e.2.val from rfl, previous]

/-- The southern triangle traverses the same interval from west to east. -/
theorem southRingFace_edge (G : LatitudeRings) (e : RingEdge G) :
    orientedChordEdge (chordVertices G (southRingFace G e)) (ringSlot (southRingFace G e)) =
      (rowSite G e.1.val e.2.val, rowSite G e.1.val (e.2.val + 1)) := by
  unfold southRingFace
  split
  · rename_i annular
    let step := sweepOrder (rowSize G e.1.val) (rowSize G (e.1.val + 1))
    change orientedChordEdge (latitudeSweepChordVertices G e.1.val step (lowerRank step e.2)) 2 = _
    unfold latitudeSweepChordVertices lowerRank
    rw [step.apply_symm_apply]
    rfl
  · rename_i no_strip
    have last : e.1.val = stripCount G := by omega
    simp only [ringSlot, chordVertices, orientedChordEdge, Fin.val_cast]
    change (rowSite G (stripCount G) e.2.val, rowSite G (stripCount G) (e.2.val + 1)) = _
    exact congrArg (fun row => (rowSite G row e.2.val, rowSite G row (e.2.val + 1))) last.symm

/-- The two actual row sides have exactly reversed endpoints. -/
theorem ringFaces_opposite (G : LatitudeRings) (e : RingEdge G) :
    orientedChordEdge (chordVertices G (northRingFace G e)) (ringSlot (northRingFace G e)) =
      (orientedChordEdge (chordVertices G (southRingFace G e)) (ringSlot (southRingFace G e))).swap := by
  rw [northRingFace_edge, southRingFace_edge]
  rfl

end Unfoldings.FewestNets.LatitudeRings
