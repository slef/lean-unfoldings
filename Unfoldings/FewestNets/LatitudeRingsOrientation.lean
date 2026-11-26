module

public import Unfoldings.FewestNets.LatitudeChordBase
public import Unfoldings.FewestNets.LatitudeRingsChordMesh
public import Unfoldings.Cap.VerticalProduct

/-! Both polar fans and the annular sweep use the same ambient orientation. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FewestNets.LatitudeRings

open Real Module

local notation "std" => OrthonormalBasis.toBasis (EuclideanSpace.basisFun (Fin 3) ℝ)

/-- The midpoint triangles are consistently oriented in ambient space. -/
structure Oriented (G : LatitudeRings) : Prop extends Admissible G where
  annular_negative : ∀ i : AnnularTriangle G, (std).det (annularVertices G i) < 0

private theorem det_pole_latitude_pair (z row left right : ℝ) :
    (std).det ![Cap.horizontalAtHeight 0 z, latitudeSite row left, latitudeSite row right] =
      z * sin row ^ 2 * sin (right - left) := by
  rw [Basis.det_apply, Matrix.det_fin_three, sin_sub]
  simp only [Basis.toMatrix_apply, OrthonormalBasis.coe_toBasis_repr_apply,
    EuclideanSpace.basisFun_repr, Cap.horizontalAtHeight, latitudeSite]
  norm_num
  ring

private theorem rowLongitude_succ_difference {G : LatitudeRings} (j k : ℕ) :
    rowLongitude (rowSize G j) (k + 1) - rowLongitude (rowSize G j) k =
      longitudeStep G j := by
  simp only [rowLongitude, longitudeStep, Nat.cast_add, Nat.cast_one]
  ring

/-- Every actual triangle has negative determinant in the ambient frame
when its vertices are read in the chosen cyclic order. -/
theorem chordVertices_det_neg {G : LatitudeRings} (hG : Oriented G)
    (face : ChordFace G) : (std).det (chordVertices G face) < 0 := by
  rcases face with e | ⟨j,i⟩ | e
  · change (std).det ![latitudeSite 0 0, rowSite G 0 (e.val + 1), rowSite G 0 e.val] < 0
    have pole : latitudeSite 0 0 = Cap.horizontalAtHeight 0 1 := by
      ext k
      fin_cases k <;> simp [latitudeSite, Cap.horizontalAtHeight]
    rw [pole]
    unfold rowSite
    rw [det_pole_latitude_pair, show rowLongitude (rowSize G 0) e.val -
      rowLongitude (rowSize G 0) (e.val + 1) = -longitudeStep G 0 by
        linarith only [rowLongitude_succ_difference (G := G) 0 e.val],
      sin_neg, one_mul, mul_neg, neg_lt_zero]
    have valid := Nat.zero_le (stripCount G)
    have row := colatitude_mem hG.toAdmissible valid
    have step := longitudeStep_pos_lt_pi hG.toAdmissible valid
    exact mul_pos (pow_pos (sin_pos_of_pos_of_lt_pi row.1 row.2) _) (sin_pos_of_pos_of_lt_pi step.1 step.2)
  · exact hG.annular_negative ⟨j, i⟩
  · let last := stripCount G
    change (std).det ![latitudeSite π 0, rowSite G last e.val,
      rowSite G last (e.val + 1)] < 0
    have pole : latitudeSite π 0 = Cap.horizontalAtHeight 0 (-1) := by
      ext k
      fin_cases k <;> simp [latitudeSite, Cap.horizontalAtHeight]
    rw [pole]
    unfold rowSite
    rw [det_pole_latitude_pair, rowLongitude_succ_difference, neg_one_mul, neg_mul, neg_lt_zero]
    have valid : last ≤ stripCount G := le_rfl
    have row := colatitude_mem hG.toAdmissible valid
    have step := longitudeStep_pos_lt_pi hG.toAdmissible valid
    exact mul_pos (pow_pos (sin_pos_of_pos_of_lt_pi row.1 row.2) _) (sin_pos_of_pos_of_lt_pi step.1 step.2)

/-- All three oriented chord sites form a basis, including the polar cells. -/
theorem exists_chordBasis {G : LatitudeRings} (hG : Oriented G)
    (i : ChordFace G) : ∃ b : Basis (Fin 3) ℝ Space, (b : Fin 3 → Space) = chordVertices G i := by
  have det := chordVertices_det_neg hG i
  have nonzero : IsUnit ((std).det (chordVertices G i)) := isUnit_iff_ne_zero.mpr det.ne
  obtain ⟨independent, _⟩ := (Basis.is_basis_iff_det (std)).mpr nonzero
  have card : Fintype.card (Fin 3) = Module.finrank ℝ Space :=
    (finrank_euclideanSpace (𝕜 := ℝ) (ι := Fin 3)).symm
  exact ⟨basisOfLinearIndependentOfCardEqFinrank independent card,
    coe_basisOfLinearIndependentOfCardEqFinrank _ _⟩

end Unfoldings.FewestNets.LatitudeRings
