module

public import Unfoldings.FewestNets.IcosahedronVertexFrame
public import Unfoldings.FewestNets.IcosahedronRealizedStar
public import Unfoldings.FewestNets.IcosahedronGridWeights

/-! The five fine triangles at the original reference vertex. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FewestNets.Icosahedron

open MeshStar NormedSpace TriangleGrid
open scoped BigOperators

def referenceVertexCell {q : ℕ} (hq : 0 < q) : GridCell q :=
  ⟨(0, 0, false), by
    simpa [TriangleGrid.Valid] using (Nat.succ_le_of_lt hq : 1 ≤ q)⟩

def referenceVertexFineFace {q : ℕ} (hq : 0 < q) (k : Fin 5) : MeshFace q :=
  (referenceVertexFace k, referenceVertexCell hq)

def referenceVertexSite {q : ℕ} (hq : 0 < q) : meshSites q :=
  siteOfCorner (referenceVertexFineFace hq 0) 0

theorem localGridWeights_referenceVertexCell {q : ℕ} (hq : 0 < q) :
    localGridWeights (referenceVertexCell hq) 0 = ![q, 0, 0] := by
  funext j
  fin_cases j <;>
    simp [localGridWeights, referenceVertexCell, barycentricCorner, barycentricMin]
  omega

private theorem gridWeights_referenceVertexSite {q : ℕ} (hq : 0 < q) (v : Fin 12) :
    gridWeights (referenceVertexFineFace hq 0) 0 v = if v = 0 then q else 0 := by
  change extendFaceWeights 0 (localGridWeights (referenceVertexCell hq) 0) v = _
  rw [localGridWeights_referenceVertexCell]
  have v0 : faceVertex 0 0 = (0 : Fin 12) := by decide +kernel
  simp [extendFaceWeights, Fin.sum_univ_three, v0, eq_comm]

private theorem gridCell_eq_referenceVertexCell_of_weights {q : ℕ} (hq : 0 < q)
    (t : GridCell q) (j : Fin 3) (h₁ : localGridWeights t j 1 = 0)
    (h₂ : localGridWeights t j 2 = 0) :
    t = referenceVertexCell hq := by
  change barycentricCorner q _ _ _ j 1 = 0 at h₁
  change barycentricCorner q _ _ _ j 2 = 0 at h₂
  rw [barycentricCorner_one] at h₁
  rw [barycentricCorner_two] at h₂
  have both : corner t.val.1.val t.val.2.1.val t.val.2.2 j = (0, 0) :=
    Prod.ext h₁ h₂
  have label (i k : ℕ) (b : Bool) (j : Fin 3)
      (equal : corner i k b j = (0, 0)) : (i, k, b) = (0, 0, false) := by
    cases b <;> fin_cases j <;> simp [corner] at equal ⊢
    omega
  have d := label t.val.1.val t.val.2.1.val t.val.2.2 j both
  exact Subtype.ext (Prod.ext (Fin.ext (congrArg Prod.fst d))
    (Prod.ext (Fin.ext (congrArg (fun g : ℕ × ℕ × Bool => g.2.1) d))
      (congrArg (fun g : ℕ × ℕ × Bool => g.2.2) d)))

theorem exists_referenceVertexFineFace_eq_of_mem_corners {q : ℕ} (hq : 0 < q)
    (t : MeshFace q) (mem : (referenceVertexSite hq : Space) ∈ Set.range (inscribedCorners t)) :
    ∃ k : Fin 5, referenceVertexFineFace hq k = t := by
  obtain ⟨j, equal⟩ := mem
  have weights :=
    gridWeights_eq_of_inscribedCorners_eq hq t (referenceVertexFineFace hq 0) j 0 equal
  have at_zero : gridWeights t j 0 = q := by
    rw [weights, gridWeights_referenceVertexSite, ite_eq_left rfl]
  have orig : (0 : Fin 12) ∈ Set.range (faceVertex t.1) := by
    by_contra absent
    rw [gridWeights, extendFaceWeights_zero_of_outside _ _ absent] at at_zero
    omega
  obtain ⟨k, face_eq⟩ := (referenceVertexFace_range_iff t.1).mp orig
  have h0 : faceVertex t.1 0 = 0 := by
    rw [← face_eq, referenceVertexFace_corners]
    rfl
  have vanish {d : Fin 3} (diff : d ≠ 0) : localGridWeights t.2 j d = 0 := by
    have coord : localGridWeights t.2 j d = gridWeights t j (faceVertex t.1 d) :=
      (extendFaceWeights_faceVertex t.1 _ d).symm
    rw [coord, weights, gridWeights_referenceVertexSite]
    have nonzero : faceVertex t.1 d ≠ 0 := by
      rw [← h0]
      exact (faceVertex_injective t.1).ne diff
    exact ite_eq_right nonzero
  exact ⟨k, Prod.ext face_eq
    (gridCell_eq_referenceVertexCell_of_weights hq t.2 j
      (vanish (by decide : (1 : Fin 3) ≠ 0)) (vanish (by decide : (2 : Fin 3) ≠ 0))).symm⟩

private theorem iterate_fifthTurn_affine (a b : ℝ) (n : ℕ) :
    fifthTurn^[n] (a • cornerA + b • cornerB) = a • cornerA + b • fifthTurn^[n] cornerB := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, fifthTurn_add, fifthTurn_smul, fifthTurn_smul,
      fifthTurn_cornerA, Function.iterate_succ_apply']

theorem map_pentagon_neighbor {q : ℕ} (L : Space ≃ₗᵢ[ℝ] Space)
    (model : ∀ j, L (modelCorners j) = unitFaceCorners 0 j) (k : Fin 5) :
    L ((pentagon q).neighbor k) =
      radius⁻¹ • (rawVertex 0 + (q : ℝ)⁻¹ •
        (rawVertex (referenceVertexNeighbor k) - rawVertex 0)) := by
  have start : cornerA + stepU q = (1 - (q : ℝ)⁻¹) • cornerA + (q : ℝ)⁻¹ • cornerB := by
    rw [stepU]
    module
  have a : L cornerA = radius⁻¹ • rawVertex 0 := model 0
  have next := map_iterate_fifthTurn_cornerB L model k.val
  have mod : (⟨k.val % 5, Nat.mod_lt _ (by decide)⟩ : Fin 5) = k :=
    Fin.ext (Nat.mod_eq_of_lt k.isLt)
  rw [mod] at next
  change L (fifthTurn^[k.val] (cornerA + stepU q)) = _
  rw [start, iterate_fifthTurn_affine, map_add, map_smul, map_smul, a, next]
  module

end Unfoldings.FewestNets.Icosahedron
