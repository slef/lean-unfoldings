module

public import Unfoldings.FewestNets.IcosahedronFaceIsometry
public import Unfoldings.FewestNets.MeshPentagonRotation

/-! The positive rotation orbit is the exact cycle around the reference macrovertex. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FewestNets.Icosahedron

open MeshStar Real

/-- The five neighbors of original vertex zero in positive cyclic order. -/
def referenceVertexNeighbor : Fin 5 → Fin 12 := ![4, 2, 5, 10, 8]

def referenceVertexFace : Fin 5 → Fin 20 := ![0, 1, 3, 4, 2]

theorem referenceVertexFace_injective : Function.Injective referenceVertexFace := by
  have table : ∀ i j : Fin 5, referenceVertexFace i = referenceVertexFace j → i = j := by
    decide +kernel
  exact table

theorem referenceVertexFace_corners (i : Fin 5) :
    faceVertex (referenceVertexFace i) =
      ![0, referenceVertexNeighbor i, referenceVertexNeighbor (i + 1)] := by
  have table : ∀ (i : Fin 5) (j : Fin 3),
      faceVertex (referenceVertexFace i) j =
        (![0, referenceVertexNeighbor i, referenceVertexNeighbor (i + 1)] : Fin 3 → Fin 12) j :=
    by decide +kernel
  exact funext (table i)

theorem referenceVertexFace_range_iff (f : Fin 20) :
    (0 : Fin 12) ∈ Set.range (faceVertex f) ↔ f ∈ Set.range referenceVertexFace := by
  have table : ∀ f : Fin 20, (∃ j : Fin 3, faceVertex f j = 0) ↔
      (∃ i : Fin 5, referenceVertexFace i = f) := by decide +kernel
  exact table f

private theorem rawVertex_referenceNeighbor_recurrence (i : Fin 5) :
    rawVertex (referenceVertexNeighbor (i + 2)) =
      (goldenRatio - 1) • (rawVertex (referenceVertexNeighbor (i + 1)) + rawVertex 0) -
        rawVertex (referenceVertexNeighbor i) := by
  have table : ∀ (i : Fin 5) (d : Fin 3),
      rawCoordinates (referenceVertexNeighbor (i + 2)) d =
        goldenMultiply (-1, 1)
          (rawCoordinates (referenceVertexNeighbor (i + 1)) d + rawCoordinates 0 d) -
        rawCoordinates (referenceVertexNeighbor i) d := by decide +kernel
  have sub (a b : GoldenInt) : goldenValue (a - b) = goldenValue a - goldenValue b := by
    simp only [goldenValue, Prod.fst_sub, Prod.snd_sub, Int.cast_sub]
    ring
  ext d
  change goldenValue (rawCoordinates (referenceVertexNeighbor (i + 2)) d) =
    (goldenRatio - 1) * (goldenValue (rawCoordinates (referenceVertexNeighbor (i + 1)) d) +
      goldenValue (rawCoordinates 0 d)) - goldenValue (rawCoordinates (referenceVertexNeighbor i) d)
  rw [table i d, sub, goldenValue_multiply, goldenValue_add]
  norm_num [goldenValue]
  ring_nf
  simp

/-- The actual neighbors in the reference frame are given by the model fivefold orbit. -/
theorem map_iterate_fifthTurn_cornerB (L : Space ≃ₗᵢ[ℝ] Space)
    (model : ∀ j, L (modelCorners j) = unitFaceCorners 0 j) (n : ℕ) :
    L (fifthTurn^[n] cornerB) =
      radius⁻¹ • rawVertex (referenceVertexNeighbor ⟨n % 5, Nat.mod_lt _ (by decide)⟩) := by
  have a : L cornerA = radius⁻¹ • rawVertex 0 := model 0
  have b : L cornerB = radius⁻¹ • rawVertex 4 := model 1
  have c : L cornerC = radius⁻¹ • rawVertex 2 := model 2
  have inner_axis (k : ℕ) : inner ℝ cornerA (fifthTurn^[k] cornerB) = √5 / 5 := by
    induction k with
    | zero => exact corner_pair_inner.1
    | succ k ih => rw [Function.iterate_succ_apply', inner_cornerA_fifthTurn, ih]
  induction n using Nat.twoStepInduction with
  | zero => exact b
  | one =>
    change L (fifthTurn cornerB) = radius⁻¹ • rawVertex 2
    rw [fifthTurn_cornerB, c]
  | more k first last =>
    let i : Fin 5 := ⟨k % 5, Nat.mod_lt _ (by decide)⟩
    have first_index : (⟨(k + 1) % 5, Nat.mod_lt _ (by decide)⟩ : Fin 5) = i + 1 := by
      apply Fin.ext
      change (k + 1) % 5 = (k % 5 + 1) % 5
      omega
    have last_index : (⟨(k + 2) % 5, Nat.mod_lt _ (by decide)⟩ : Fin 5) = i + 2 := by
      apply Fin.ext
      change (k + 2) % 5 = (k % 5 + 2) % 5
      omega
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
      fifthTurn_twice_of_neighbor _ (inner_axis k),
      ← Function.iterate_succ_apply' fifthTurn k cornerB,
      map_sub, map_smul, map_add, last, first, a, first_index, last_index,
      rawVertex_referenceNeighbor_recurrence i]
    module

end Unfoldings.FewestNets.Icosahedron
