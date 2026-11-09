module

public import Unfoldings.Geometry.EdgeLine
public import Unfoldings.Geometry.HingePatch
public import Unfoldings.Geometry.SpatialPlane

/-!
# Unfolding entire spatial support hinges

The actual outward edge placement extends to both closed supporting
half-planes. Supporting functionals identify the two sides and prove that
the resulting piecewise rigid planar parametrization is injective.
-/

@[expose] public section

noncomputable section

namespace Unfoldings

structure SpatialHinge {T U : Triangle} {e f : Fin 3} {identify : T.Edge e ≃ᵢ U.Edge f}
    (H : HingePlacement T U e f identify) where
  left : Plane →ᵃⁱ[ℝ] Space
  right : Plane →ᵃⁱ[ℝ] Space
  joined : ∀ x : T.Edge e, left x.val = right (identify x).val
  leftFunctional : Space →L[ℝ] ℝ
  rightFunctional : Space →L[ℝ] ℝ
  leftLevel : ℝ
  rightLevel : ℝ
  left_range : Set.range left = {z | leftFunctional z = leftLevel}
  right_range : Set.range right = {z | rightFunctional z = rightLevel}
  left_cross : rightFunctional (left (T.opposite e)) < rightLevel
  right_cross : leftFunctional (right (U.opposite f)) < leftLevel

namespace SpatialHinge

variable {T U : Triangle} {e f : Fin 3} {identify : T.Edge e ≃ᵢ U.Edge f}
  {H : HingePlacement T U e f identify} (S : SpatialHinge H)

theorem left_level (x : Plane) : S.leftFunctional (S.left x) = S.leftLevel :=
  S.left_range.le (Set.mem_range_self x)

theorem right_level (x : Plane) : S.rightFunctional (S.right x) = S.rightLevel :=
  S.right_range.le (Set.mem_range_self x)

theorem joined_inverse (x : U.Edge f) : S.right x.val = S.left (identify.symm x).val := by
  have joined := S.joined (identify.symm x)
  rw [identify.apply_symm_apply] at joined
  exact joined.symm

theorem left_height (z : Plane) :
    S.rightFunctional (S.left z) - S.rightLevel =
      (S.rightFunctional (S.left (T.opposite e)) - S.rightLevel) *
        T.coord (Triangle.next (Triangle.next e)) z := by
  let height : Plane →ᵃ[ℝ] ℝ :=
    S.rightFunctional.toLinearMap.toAffineMap.comp S.left.toAffineMap -
      AffineMap.const ℝ Plane S.rightLevel
  have zero (x : T.Edge e) : height x.val = 0 := by
    change S.rightFunctional (S.left x.val) - S.rightLevel = 0
    rw [S.joined, S.right_level, sub_self]
  exact T.affine_height_eq_coord e height
    (zero ⟨_, left_mem_segment ℝ _ _⟩) (zero ⟨_, right_mem_segment ℝ _ _⟩) z

theorem right_height (z : Plane) :
    S.leftFunctional (S.right z) - S.leftLevel =
      (S.leftFunctional (S.right (U.opposite f)) - S.leftLevel) *
        U.coord (Triangle.next (Triangle.next f)) z := by
  let height : Plane →ᵃ[ℝ] ℝ :=
    S.leftFunctional.toLinearMap.toAffineMap.comp S.right.toAffineMap -
      AffineMap.const ℝ Plane S.leftLevel
  have zero (x : U.Edge f) : height x.val = 0 := by
    change S.leftFunctional (S.right x.val) - S.leftLevel = 0
    rw [S.joined_inverse, S.left_level, sub_self]
  exact U.affine_height_eq_coord f height
    (zero ⟨_, left_mem_segment ℝ _ _⟩) (zero ⟨_, right_mem_segment ℝ _ _⟩) z

theorem left_side_iff (z : Plane) : S.rightFunctional (S.left z) ≤ S.rightLevel ↔
    0 ≤ T.coord (Triangle.next (Triangle.next e)) z := by
  have formula := S.left_height z
  have negative : S.rightFunctional (S.left (T.opposite e)) - S.rightLevel < 0 :=
    sub_neg.mpr S.left_cross
  constructor
  · intro bound
    by_contra wrong
    have positive := mul_pos_of_neg_of_neg negative (lt_of_not_ge wrong)
    linarith
  · intro nonnegative
    have bound := mul_nonpos_of_nonpos_of_nonneg negative.le nonnegative
    linarith

theorem right_side_iff (z : Plane) : S.leftFunctional (S.right z) ≤ S.leftLevel ↔
    0 ≤ U.coord (Triangle.next (Triangle.next f)) z := by
  have formula := S.right_height z
  have negative : S.leftFunctional (S.right (U.opposite f)) - S.leftLevel < 0 :=
    sub_neg.mpr S.right_cross
  constructor
  · intro bound
    by_contra wrong
    have positive := mul_pos_of_neg_of_neg negative (lt_of_not_ge wrong)
    linarith
  · intro nonnegative
    have bound := mul_nonpos_of_nonpos_of_nonneg negative.le nonnegative
    linarith

theorem joined_line (z : Plane) (zero : T.coord (Triangle.next (Triangle.next e)) z = 0) :
    S.left z = S.right (H.place.symm z) := by
  have equal (x : T.Edge e) : S.left x.val = S.right (H.place.symm x.val) := by
    rw [H.inverse_joined]
    exact S.joined x
  exact T.affine_eq_of_coord_zero e S.left.toAffineMap
    (S.right.toAffineMap.comp H.place.symm.toAffineEquiv.toAffineMap)
    (equal ⟨_, left_mem_segment ℝ _ _⟩) (equal ⟨_, right_mem_segment ℝ _ _⟩) z zero

def map (z : Plane) : Space :=
  if 0 ≤ T.coord (Triangle.next (Triangle.next e)) z then S.left z
  else S.right (H.place.symm z)

theorem map_left (z : Plane) (side : 0 ≤ T.coord (Triangle.next (Triangle.next e)) z) :
    S.map z = S.left z := ite_eq_left side

theorem map_right (z : Plane) (side : T.coord (Triangle.next (Triangle.next e)) z ≤ 0) :
    S.map z = S.right (H.place.symm z) := by
  by_cases nonnegative : 0 ≤ T.coord (Triangle.next (Triangle.next e)) z
  · rw [S.map_left z nonnegative]
    exact S.joined_line z (le_antisymm side nonnegative)
  · exact ite_eq_right nonnegative

theorem map_injective : Function.Injective S.map := by
  have crossing (x y : Plane) (equal : S.left x = S.right (H.place.symm y)) : x = y := by
    have level : S.rightFunctional (S.left x) = S.rightLevel := by
      rw [equal, S.right_level]
    have formula := S.left_height x
    rw [level, sub_self] at formula
    have zero : T.coord (Triangle.next (Triangle.next e)) x = 0 :=
      (mul_eq_zero.mp formula.symm).resolve_left (ne_of_lt (sub_neg.mpr S.left_cross))
    have same : H.place.symm x = H.place.symm y :=
      S.right.injective ((S.joined_line x zero).symm.trans equal)
    exact H.place.symm.injective same
  intro x y equal
  by_cases first : 0 ≤ T.coord (Triangle.next (Triangle.next e)) x
  · rw [S.map_left x first] at equal
    by_cases last : 0 ≤ T.coord (Triangle.next (Triangle.next e)) y
    · rw [S.map_left y last] at equal
      exact S.left.injective equal
    · rw [S.map_right y (le_of_not_ge last)] at equal
      exact crossing x y equal
  · rw [S.map_right x (le_of_not_ge first)] at equal
    by_cases last : 0 ≤ T.coord (Triangle.next (Triangle.next e)) y
    · rw [S.map_left y last] at equal
      exact (crossing y x equal.symm).symm
    · rw [S.map_right y (le_of_not_ge last)] at equal
      exact H.place.symm.injective (S.right.injective equal)

theorem right_planar_side_iff (_S : SpatialHinge H) (z : Plane) :
    0 ≤ U.coord (Triangle.next (Triangle.next f)) (H.place.symm z) ↔
      T.coord (Triangle.next (Triangle.next e)) z ≤ 0 := by
  have formula := H.rightCoord_eq z
  change U.coord (Triangle.next (Triangle.next f)) (H.place.symm z) =
    H.rightCoord (T.opposite e) * T.coord (Triangle.next (Triangle.next e)) z at formula
  have negative := H.rightCoord_opposite_neg
  constructor
  · intro nonnegative
    by_contra wrong
    have bound := mul_neg_of_neg_of_pos negative (lt_of_not_ge wrong)
    linarith
  · intro nonpositive
    have bound := mul_nonneg_of_nonpos_of_nonpos negative.le nonpositive
    linarith

def carrier : Set Space :=
  {z | S.leftFunctional z = S.leftLevel ∧ S.rightFunctional z ≤ S.rightLevel} ∪
    {z | S.rightFunctional z = S.rightLevel ∧ S.leftFunctional z ≤ S.leftLevel}

theorem range_map : Set.range S.map = S.carrier := by
  ext z
  constructor
  · rintro ⟨x, rfl⟩
    by_cases side : 0 ≤ T.coord (Triangle.next (Triangle.next e)) x
    · rw [S.map_left x side]
      exact Or.inl ⟨S.left_level x, (S.left_side_iff x).mpr side⟩
    · rw [S.map_right x (le_of_not_ge side)]
      exact Or.inr ⟨S.right_level _, (S.right_side_iff _).mpr
        ((S.right_planar_side_iff x).mpr (le_of_not_ge side))⟩
  · intro member
    rcases member with first | second
    · obtain ⟨x, rfl⟩ := S.left_range.ge first.1
      exact ⟨x, S.map_left x ((S.left_side_iff x).mp first.2)⟩
    · obtain ⟨y, rfl⟩ := S.right_range.ge second.1
      refine ⟨H.place y, ?_⟩
      have side : T.coord (Triangle.next (Triangle.next e)) (H.place y) ≤ 0 := by
        apply (S.right_planar_side_iff _).mp
        rw [H.place.symm_apply_apply]
        exact (S.right_side_iff y).mp second.2
      rw [S.map_right _ side, H.place.symm_apply_apply]

def pieces (_S : SpatialHinge H) (i : Fin 2) : Set Plane :=
  if i = 0 then {z | 0 ≤ T.coord (Triangle.next (Triangle.next e)) z}
  else {z | T.coord (Triangle.next (Triangle.next e)) z ≤ 0}

def places (i : Fin 2) : Plane →ᵃⁱ[ℝ] Space :=
  if i = 0 then S.left else S.right.comp H.place.symm.toAffineIsometry

theorem pieces_closed (i : Fin 2) : IsClosed (S.pieces i) := by
  fin_cases i
  · exact isClosed_le continuous_const (T.continuous_coord _)
  · exact isClosed_le (T.continuous_coord _) continuous_const

theorem pieces_convex (i : Fin 2) : Convex ℝ (S.pieces i) := by
  fin_cases i
  · exact (convex_Ici (0 : ℝ)).affine_preimage (T.coord _)
  · exact (convex_Iic (0 : ℝ)).affine_preimage (T.coord _)

theorem pieces_cover : ⋃ i, S.pieces i = Set.univ := by
  apply Set.eq_univ_of_forall
  intro z
  by_cases side : 0 ≤ T.coord (Triangle.next (Triangle.next e)) z
  · exact Set.mem_iUnion.mpr ⟨0, side⟩
  · exact Set.mem_iUnion.mpr ⟨1, (le_of_not_ge side)⟩

theorem pieces_agree (i : Fin 2) (z : Plane) (member : z ∈ S.pieces i) :
    S.map z = S.places i z := by
  fin_cases i
  · exact S.map_left z member
  · exact S.map_right z member

end SpatialHinge
end Unfoldings
