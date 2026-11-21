module

public import Unfoldings.FewestNets.IcosahedronFaceCount
public import Unfoldings.FewestNets.IcosahedronFaceIncidence
public import Mathlib.Data.Fintype.BigOperators

/-! Double counting fine face-edge incidences gives the exact Voronoi edge count. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FewestNets.Icosahedron

open scoped BigOperators

/-- A frequency-q mesh with acute fine faces has exactly `30 * q ^ 2` primal
edges, hence the same number of indexed dual Voronoi arcs. -/
theorem card_meshEdge {q : ℕ} (qbig : 100 ≤ q) : Nat.card (MeshEdge q) = 30 * q ^ 2 := by
  classical
  have hq : 0 < q := by omega
  let : Fintype (MeshEdge q) := Fintype.ofFinite _
  let : Fintype (MeshFace q) := Fintype.ofFinite _
  let (e : MeshEdge q) : Fintype {t : MeshFace q // EdgeIncident e t} := Fintype.ofFinite _
  let (t : MeshFace q) : Fintype {e : MeshEdge q // EdgeIncident e t} := Fintype.ofFinite _
  let interchange :
      (Σ e : MeshEdge q, {t : MeshFace q // EdgeIncident e t}) ≃
        (Σ t : MeshFace q, {e : MeshEdge q // EdgeIncident e t}) :=
    { toFun := fun ⟨e, t, ht⟩ => ⟨t, e, ht⟩
      invFun := fun ⟨t, e, ht⟩ => ⟨e, t, ht⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have count := Fintype.card_congr interchange
  rw [Fintype.card_sigma, Fintype.card_sigma] at count
  have left : (∑ e : MeshEdge q, Fintype.card {t : MeshFace q // EdgeIncident e t}) =
      Nat.card (MeshEdge q) * 2 := by
    simp only [← Nat.card_eq_fintype_card, card_edgeIncident qbig hq]
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Nat.card_eq_fintype_card]
    norm_num
  have right : (∑ t : MeshFace q, Fintype.card {e : MeshEdge q // EdgeIncident e t}) =
      (20 * q ^ 2) * 3 := by
    simp only [← Nat.card_eq_fintype_card, card_faceIncident hq]
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Nat.card_eq_fintype_card, card_meshFace]
    norm_num
  rw [left, right, show (20 * q ^ 2) * 3 = (30 * q ^ 2) * 2 by ring] at count
  omega

theorem card_meshEdge_q100 : Nat.card (MeshEdge 100) = 300000 := by
  rw [card_meshEdge (by decide : 100 ≤ 100)]
  decide

theorem card_meshEdge_q400 : Nat.card (MeshEdge 400) = 4800000 := by
  rw [card_meshEdge (by decide : 100 ≤ 400)]
  decide

end Unfoldings.FewestNets.Icosahedron
