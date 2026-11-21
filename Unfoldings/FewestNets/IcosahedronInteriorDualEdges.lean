module

public import Unfoldings.FewestNets.IcosahedronInteriorStar
public import Unfoldings.FewestNets.IcosahedronDualEdges
public import Unfoldings.FewestNets.IcosahedronFaceIncidence
public import Unfoldings.FewestNets.MeshStarFacetNormal

/-! Canonical interior star sides give exact lengths of the actual dual network arcs. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FewestNets.Icosahedron

open InnerProductGeometry NormedSpace MeshStar

theorem faceStarCell_ne_succ {q i j : ℕ} (hi : 0 < i) (hj : 0 < j)
    (sum : i + j < q) (k : Fin 6) :
    faceStarCell hi hj sum k ≠ faceStarCell hi hj sum (k + 1) := by
  intro eq
  have same := congrArg (fun t : GridCell q => t.val.2.2) eq
  fin_cases k <;> simp [faceStarCell, faceStarCellKey, Fin.add_def] at same

/-- A candidate side between two consecutive outward star normals is
an actual dual arc with exactly the certified candidate length. -/
theorem exists_meshEdge_angle_eq_interiorStar {q i j : ℕ} (qbig : 100 ≤ q) (hq : 0 < q)
    (f : Fin 20) (hi : 0 < i) (hj : 0 < j) (sum : i + j < q) (k : Fin 6)
    (outward : 0 < inner ℝ (modelInteriorStar q i j).direction ((modelInteriorStar q i j).dual k))
    (outward' : 0 < inner ℝ (modelInteriorStar q i j).direction
      ((modelInteriorStar q i j).dual (k + 1))) :
    ∃ e : MeshEdge q,
      angle (meshEndpoint hq e false) (meshEndpoint hq e true) =
        angle ((modelInteriorStar q i j).dualDirection k)
          ((modelInteriorStar q i j).dualDirection (k + 1)) := by
  classical
  let M := modelInteriorStar q i j
  obtain ⟨L, vertex⟩ := exists_modelFace_isometry f
  let t (a : Fin 6) : MeshFace q := (f, faceStarCell hi hj sum a)
  let p := faceStarCornerIndex
  have corner_eq (a : Fin 6) (b : Fin 3) :
      inscribedCorners (t a) (p a b) =
        L ((![M.direction, M.neighborDirection a, M.neighborDirection (a + 1)] : Fin 3 → Space) b) :=
    by
      rw [← map_normalize_modelGridCorners (t a) L vertex]
      congr 1
      change NormedSpace.normalize
        (modelGridCorners (faceStarCell hi hj sum a) (faceStarCornerIndex a b)) = _
      rw [modelGridCorners_faceStarCell hi hj sum]
      fin_cases b <;> rfl
  have first_normal : facetNormal hq (t k) = L (M.dualDirection k) :=
    facetNormal_eq_map_dualDirection hq _ M k L (p k) (faceStarCornerIndex_bijective k).2
      (corner_eq k) (by rwa [real_inner_comm])
  have second_normal : facetNormal hq (t (k + 1)) = L (M.dualDirection (k + 1)) :=
    facetNormal_eq_map_dualDirection hq _ M (k + 1) L (p (k + 1))
      (faceStarCornerIndex_bijective (k + 1)).2 (corner_eq (k + 1)) (by rwa [real_inner_comm])
  let a : meshSites q := siteOfCorner (t k) (p k 0)
  let b : meshSites q := siteOfCorner (t k) (p k 2)
  have different : a ≠ b := by
    intro eq
    exact (by decide : (0 : Fin 3) ≠ 2)
      ((faceStarCornerIndex_bijective k).1 ((siteOfCorner_injective hq (t k)) eq))
  have pair_face : ∀ z ∈ ({a, b} : Finset (meshSites q)),
      (z : Space) ∈ Set.range (inscribedCorners (t k)) := by
    intro z hz
    rw [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl
    · exact Set.mem_range_self (p k 0)
    · exact Set.mem_range_self (p k 2)
  let e : MeshEdge q := ⟨{a, b}, Finset.card_eq_two.mpr ⟨a, b, different, rfl⟩, t k, pair_face⟩
  have pair_face' : EdgeIncident e (t (k + 1)) := by
    intro z hz
    change z ∈ ({a, b} : Finset (meshSites q)) at hz
    rw [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl
    · refine ⟨p (k + 1) 0, ?_⟩
      change inscribedCorners (t (k + 1)) (p (k + 1) 0) = inscribedCorners (t k) (p k 0)
      rw [corner_eq, corner_eq]
      rfl
    · refine ⟨p (k + 1) 1, ?_⟩
      change inscribedCorners (t (k + 1)) (p (k + 1) 1) = inscribedCorners (t k) (p k 2)
      rw [corner_eq, corner_eq]
      rfl
  have ne : t k ≠ t (k + 1) := fun eq => faceStarCell_ne_succ hi hj sum k (congrArg Prod.snd eq)
  refine ⟨e, ?_⟩
  rcases meshEdgeFaces_of_incident_pair qbig hq e _ _ ne pair_face pair_face' with order | order
  · simp only [meshEndpoint, order, Bool.false_eq_true, ite_false, ite_true]
    rw [first_normal, second_normal]
    exact L.toLinearIsometry.angle_map _ _
  · simp only [meshEndpoint, order, Bool.false_eq_true, ite_false, ite_true]
    rw [first_normal, second_normal]
    exact (L.toLinearIsometry.angle_map _ _).trans (angle_comm _ _)

end Unfoldings.FewestNets.Icosahedron
