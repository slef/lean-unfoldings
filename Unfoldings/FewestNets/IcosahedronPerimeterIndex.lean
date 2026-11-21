module

public import Unfoldings.FewestNets.CheckedMeshPerimeter
public import Unfoldings.FewestNets.IcosahedronSiteWeights
public import Mathlib.Data.List.OfFn

/-! The weighted star perimeter is a sum over finite barycentric labels. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FewestNets.Icosahedron

open MeshStar
open scoped BigOperators

/-- Each original icosahedral edge, with its two corner indices ordered. -/
abbrev MacroEdgeIndex := {e : Fin 12 × Fin 12 // e.1 < e.2 ∧ Adjacent e.1 e.2}

theorem card_macroEdgeIndex : Fintype.card MacroEdgeIndex = 30 := by decide +kernel

abbrev FacePerimeterIndex (q : ℕ) :=
  Fin 20 × (Σ k : Fin (faceMeshKeys q).length,
    ↥(faceWeightOrbit ![(faceMeshKeys q).get k |>.2, (faceMeshKeys q).get k |>.1,
      q - ((faceMeshKeys q).get k).1 - ((faceMeshKeys q).get k).2]))

abbrev SeamPerimeterIndex (q : ℕ) :=
  MacroEdgeIndex × (Σ k : Fin (seamMeshKeys q).length,
    ↥(seamWeightOrbit q ((seamMeshKeys q).get k)))

/-- A site label consists of an original face, edge, or vertex and its weights. -/
abbrev PerimeterIndex (q : ℕ) := FacePerimeterIndex q ⊕ (SeamPerimeterIndex q ⊕ Fin 12)

def faceIndexUpper {q : ℕ} (a : FacePerimeterIndex q) : ℝ :=
  let key := (faceMeshKeys q).get a.2.1
  (face q key.1 key.2).arcUpperPerimeter

def seamIndexUpper {q : ℕ} (a : SeamPerimeterIndex q) : ℝ :=
  (seam q ((seamMeshKeys q).get a.2.1)).arcUpperPerimeter

def perimeterIndexUpper {q : ℕ} : PerimeterIndex q → ℝ :=
  Sum.elim faceIndexUpper (Sum.elim seamIndexUpper (fun _ => (pentagon q).arcUpperPerimeter))

def edgeBarycentricWeights (a b : Fin 12) (w : ℕ × ℕ) (v : Fin 12) : ℕ :=
  if v = a then w.1 else if v = b then w.2 else 0

def perimeterIndexWeights {q : ℕ} (a : PerimeterIndex q) : Fin 12 → ℕ :=
  match a with
  | .inl p => extendFaceWeights p.1 p.2.2.val
  | .inr (.inl p) => edgeBarycentricWeights p.1.val.1 p.1.val.2 p.2.2.val
  | .inr (.inr p) => fun v => if v = p then q else 0

/-- The actual site has the model star encoded by this barycentric label. -/
def perimeterIndexRealizes {q : ℕ} (a : meshSites q) (p : PerimeterIndex q) : Prop :=
  match p with
  | .inl p =>
    let key := (faceMeshKeys q).get p.2.1
    Nonempty (MeshStarRealization a (face q key.1 key.2))
  | .inr (.inl p) => Nonempty (MeshStarRealization a (seam q ((seamMeshKeys q).get p.2.1)))
  | .inr (.inr _) => Nonempty (MeshStarRealization a (pentagon q))

theorem meshStar_arcUpperPerimeter_nonneg {n : ℕ} (M : MeshStar (n + 1)) :
    0 ≤ M.arcUpperPerimeter := by
  unfold arcUpperPerimeter
  apply Finset.sum_nonneg
  intro k _
  unfold dualArcUpper dualChord
  exact div_nonneg (norm_nonneg _) (Real.sqrt_nonneg _)

theorem perimeterIndexUpper_nonneg {q : ℕ} (a : PerimeterIndex q) :
    0 ≤ perimeterIndexUpper a := by
  rcases a with face | seam | pentagon
  · exact meshStar_arcUpperPerimeter_nonneg _
  · exact meshStar_arcUpperPerimeter_nonneg _
  · exact meshStar_arcUpperPerimeter_nonneg _

private theorem sum_list_get_eq_map_sum {ι : Type*} (l : List ι) (f : ι → ℝ) :
    (∑ i : Fin l.length, f (l.get i)) = (l.map f).sum := by
  rw [← List.sum_ofFn]
  have key := congrArg (List.map f) (List.ofFn_get l)
  rw [List.map_ofFn, Function.comp_def] at key
  exact congrArg List.sum key

private theorem sum_faceIndexUpper (q : ℕ) :
    (∑ a : FacePerimeterIndex q, faceIndexUpper a) =
      20 * ((faceMeshKeys q).map (faceWeightedPerimeter q)).sum := by
  rw [Fintype.sum_prod_type]
  have subtotal (f : Fin 20) :
      (∑ a : Σ k : Fin (faceMeshKeys q).length,
          ↥(faceWeightOrbit ![((faceMeshKeys q).get k).2, ((faceMeshKeys q).get k).1,
            q - ((faceMeshKeys q).get k).1 - ((faceMeshKeys q).get k).2]),
        faceIndexUpper (f, a)) = ((faceMeshKeys q).map (faceWeightedPerimeter q)).sum := by
    rw [Fintype.sum_sigma, ← sum_list_get_eq_map_sum]
    apply Finset.sum_congr rfl
    intro k _
    let key := (faceMeshKeys q).get k
    have mem : key ∈ faceMeshKeys q := List.get_mem _ _
    simp only [faceIndexUpper, Finset.sum_const, Finset.card_univ, Fintype.card_coe,
      faceWeightOrbit_card_eq_meshKeyWeight mem, nsmul_eq_mul, faceWeightedPerimeter]
  rw [Finset.sum_congr rfl (fun f _ => subtotal f), Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  norm_num

private theorem sum_seamIndexUpper (q : ℕ) :
    (∑ a : SeamPerimeterIndex q, seamIndexUpper a) =
      30 * ((seamMeshKeys q).map (seamWeightedPerimeter q)).sum := by
  rw [Fintype.sum_prod_type]
  have subtotal (e : MacroEdgeIndex) :
      (∑ a : Σ k : Fin (seamMeshKeys q).length,
          ↥(seamWeightOrbit q ((seamMeshKeys q).get k)), seamIndexUpper (e, a)) =
        ((seamMeshKeys q).map (seamWeightedPerimeter q)).sum := by
    rw [Fintype.sum_sigma, ← sum_list_get_eq_map_sum]
    apply Finset.sum_congr rfl
    intro k _
    have mem : (seamMeshKeys q).get k ∈ seamMeshKeys q := List.get_mem _ _
    simp only [seamIndexUpper, Finset.sum_const, Finset.card_univ, Fintype.card_coe,
      seamWeightOrbit_card_eq_meshKeyWeight mem, nsmul_eq_mul, seamWeightedPerimeter]
  rw [Finset.sum_congr rfl (fun e _ => subtotal e), Finset.sum_const, Finset.card_univ,
    card_macroEdgeIndex, nsmul_eq_mul]
  norm_num

theorem sum_perimeterIndexUpper (q : ℕ) :
    (∑ a : PerimeterIndex q, perimeterIndexUpper a) = 2 * weightedArcUpperTotal q := by
  simp only [perimeterIndexUpper, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
    sum_faceIndexUpper, sum_seamIndexUpper, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  unfold weightedArcUpperTotal
  ring

end Unfoldings.FewestNets.Icosahedron
