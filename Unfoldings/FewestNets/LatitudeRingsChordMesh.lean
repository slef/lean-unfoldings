module

public import Unfoldings.FewestNets.LatitudeRingsSweep

/-! The acute latitude chord mesh appends the two exact polar fans to the annular sweep. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FewestNets.LatitudeRings

open Real

/-- The three kinds of triangles in the chord mesh. Each polar fan will
be grouped into one selector. -/
abbrev ChordFace (G : LatitudeRings) :=
  Fin (rowSize G 0) ⊕ (AnnularTriangle G ⊕ Fin (rowSize G (stripCount G)))

/-- Every face records the same cyclic order, with shared edges read oppositely. -/
def chordVertices (G : LatitudeRings) : ChordFace G → Fin 3 → Space
  | .inl e => ![latitudeSite 0 0, rowSite G 0 (e.val + 1), rowSite G 0 e.val]
  | .inr (.inl i) => annularVertices G i
  | .inr (.inr e) => ![latitudeSite π 0, rowSite G (stripCount G) e.val,
      rowSite G (stripCount G) (e.val + 1)]

theorem chordVertices_unit (G : LatitudeRings) (i : ChordFace G) (j : Fin 3) :
    ‖chordVertices G i j‖ = 1 := by
  rcases i with e | i | e
  · fin_cases j <;> exact latitudeSite_unit _ _
  · exact annularVertices_unit G i j
  · fin_cases j <;> exact latitudeSite_unit _ _

end Unfoldings.FewestNets.LatitudeRings
