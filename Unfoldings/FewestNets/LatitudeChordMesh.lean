module

public import Unfoldings.FewestNets.LatitudeSweepEdges

/-! The acute latitude chord mesh appends the two exact polar fans to the annular sweep. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FewestNets.AcuteLatitudeGrid

open Real

/-- The three kinds of triangles in the chord mesh. Each polar fan will
be grouped into one selector. -/
abbrev ChordFace (a : ℝ) :=
  Fin (rowSize a 0) ⊕ (AnnularTriangle a ⊕ Fin (rowSize a (stripCount a)))

/-- Every face records the same cyclic order, with shared edges read oppositely. -/
def chordVertices (a : ℝ) : ChordFace a → Fin 3 → Space
  | .inl e => ![latitudeSite 0 0, rowSite a 0 (e.val + 1), rowSite a 0 e.val]
  | .inr (.inl i) => annularVertices a i
  | .inr (.inr e) => ![latitudeSite π 0, rowSite a (stripCount a) e.val,
      rowSite a (stripCount a) (e.val + 1)]

theorem chordVertices_unit (a : ℝ) (i : ChordFace a) (j : Fin 3) :
    ‖chordVertices a i j‖ = 1 := by
  rcases i with e | i | e
  · fin_cases j <;> exact latitudeSite_unit _ _
  · exact annularVertices_unit a i j
  · fin_cases j <;> exact latitudeSite_unit _ _

end Unfoldings.FewestNets.AcuteLatitudeGrid
