module

public import Unfoldings.FewestNets.IcosahedronInteriorStar
public import Unfoldings.FewestNets.IcosahedronMeshCornerIdentity
public import Unfoldings.FewestNets.IcosahedronFaceIncidence

/-! Every fine face at an interior site is one of the six model triangles. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FewestNets.Icosahedron

open TriangleGrid

private theorem exists_faceStarCellKey_of_corner {i j x y : ℕ} (b : Bool) (k : Fin 3)
    (equal : corner x y b k = (i, j)) :
    ∃ l : Fin 6, (x, y, b) = faceStarCellKey i j l := by
  cases b
  · fin_cases k
    · exact ⟨0, by simp [corner, faceStarCellKey] at equal ⊢; omega⟩
    · exact ⟨2, by simp [corner, faceStarCellKey] at equal ⊢; omega⟩
    · exact ⟨4, by simp [corner, faceStarCellKey] at equal ⊢; omega⟩
  · fin_cases k
    · exact ⟨3, by simp [corner, faceStarCellKey] at equal ⊢; omega⟩
    · exact ⟨5, by simp [corner, faceStarCellKey] at equal ⊢; omega⟩
    · exact ⟨1, by simp [corner, faceStarCellKey] at equal ⊢; omega⟩

theorem faceStarCell_injective {q i j : ℕ} (hi : 0 < i) (hj : 0 < j) (sum : i + j < q) :
    Function.Injective (faceStarCell hi hj sum) := by
  intro k l equal
  have keys : faceStarCellKey i j k = faceStarCellKey i j l :=
    congrArg (fun t : GridCell q => (t.val.1.val, t.val.2.1.val, t.val.2.2)) equal
  fin_cases k <;> fin_cases l <;> simp [faceStarCellKey] at keys ⊢ <;> omega

/-- The fine site at the grid position (i,j) inside macroface f. -/
def interiorStarSite {q i j : ℕ} (f : Fin 20) (hi : 0 < i) (hj : 0 < j) (sum : i + j < q) :
    meshSites q :=
  siteOfCorner (f, faceStarCell hi hj sum 0) 0

theorem localGridWeights_faceStarCell_zero {q i j : ℕ} (hi : 0 < i) (hj : 0 < j)
    (sum : i + j < q) :
    localGridWeights (faceStarCell hi hj sum 0) 0 = ![q - (i + j), i, j] := by
  funext d
  fin_cases d <;> simp [localGridWeights, faceStarCell, faceStarCellKey, barycentricCorner,
    barycentricMin]
  omega

/-- A triangle incident to an interior site has the same macroface and a
grid label among the six cyclic model triangles. -/
theorem exists_faceStarCell_eq_of_mem_corners {q i j : ℕ} (hq : 0 < q) (f : Fin 20)
    (hi : 0 < i) (hj : 0 < j) (sum : i + j < q) (t : MeshFace q)
    (mem : (interiorStarSite f hi hj sum : Space) ∈ Set.range (inscribedCorners t)) :
    ∃ l : Fin 6, t = (f, faceStarCell hi hj sum l) := by
  obtain ⟨k, eq⟩ := mem
  let t₀ : MeshFace q := (f, faceStarCell hi hj sum 0)
  have same := gridWeights_eq_of_inscribedCorners_eq hq t t₀ k 0 eq
  have tsub : Set.range (faceVertex f) ⊆ Set.range (faceVertex t.1) := by
    rintro _ ⟨d, rfl⟩
    by_contra absent
    have fix := congrFun same (faceVertex f d)
    rw [gridWeights, extendFaceWeights_zero_of_outside _ _ absent, gridWeights] at fix
    change 0 = extendFaceWeights f (localGridWeights (faceStarCell hi hj sum 0) 0)
      (faceVertex f d) at fix
    rw [extendFaceWeights_faceVertex, localGridWeights_faceStarCell_zero hi hj sum] at fix
    fin_cases d <;> simp at fix <;> omega
  have macro_eq : t.1 = f := (face_eq_of_corner_subset tsub).symm
  have local_eq (d : Fin 3) :
      localGridWeights t.2 k d = (![q - (i + j), i, j] : Fin 3 → ℕ) d := by
    have same_d := congrFun same (faceVertex f d)
    change extendFaceWeights t.1 (localGridWeights t.2 k) (faceVertex f d) =
      extendFaceWeights f (localGridWeights (faceStarCell hi hj sum 0) 0) (faceVertex f d) at same_d
    rwa [macro_eq, extendFaceWeights_faceVertex, extendFaceWeights_faceVertex,
      localGridWeights_faceStarCell_zero hi hj sum] at same_d
  have first := local_eq 1
  have last := local_eq 2
  change barycentricCorner q _ _ _ k 1 = i at first
  change barycentricCorner q _ _ _ k 2 = j at last
  rw [barycentricCorner_one] at first
  rw [barycentricCorner_two] at last
  obtain ⟨l, label⟩ := exists_faceStarCellKey_of_corner t.2.val.2.2 k (Prod.ext first last)
  refine ⟨l, Prod.ext macro_eq (Subtype.ext (Prod.ext (Fin.ext ?_) (Prod.ext (Fin.ext ?_) ?_)))⟩
  · exact congrArg Prod.fst label
  · exact congrArg (fun p : ℕ × ℕ × Bool => p.2.1) label
  · exact congrArg (fun p : ℕ × ℕ × Bool => p.2.2) label

end Unfoldings.FewestNets.Icosahedron
