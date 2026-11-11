module

public import Unfoldings.Geometry.HeightGraphSplice
public import Unfoldings.Geometry.MonotoneStrip
public import Unfoldings.Geometry.ChainLinear

/-! Represent an entire genuine coordinate-monotone polygonal chain by a height graph. -/

@[expose] public section

noncomputable section

namespace Unfoldings.PolygonalChain

variable {n : ℕ} (P : PolygonalChain ℂ n)

theorem height_vertices_mono
    (directions : ∀ i, 0 ≤ (P.edge i).re ∧ 0 ≤ (P.edge i).im) :
    Monotone (fun j => (P.vertex j).re + (P.vertex j).im) := by
  apply Fin.monotone_iff_le_succ.mpr
  intro i
  have real : 0 ≤ (P.vertex i.succ).re - (P.vertex i.castSucc).re := (directions i).1
  have imaginary : 0 ≤ (P.vertex i.succ).im - (P.vertex i.castSucc).im := (directions i).2
  linarith

/-- Preserve every whole original segment, including its endpoints. The graph extends beyond
the finite chain; no geometry beyond its represented segments is asserted. -/
theorem exists_heightGraph
    (directions : ∀ i, 0 ≤ (P.edge i).re ∧ 0 ≤ (P.edge i).im)
    (genuine : ∀ i, 0 < (P.edge i).re + (P.edge i).im) :
    ∃ G : MonotoneHeightGraph,
      (∀ j, G.coordinate ((P.vertex j).re + (P.vertex j).im) = (P.vertex j).re) ∧
      ∀ i (t : unitInterval),
        G.coordinate ((P.point i t).re + (P.point i t).im) = (P.point i t).re := by
  induction n with
  | zero =>
    refine ⟨MonotoneHeightGraph.constant (P.vertex 0).re, ?_, ?_⟩
    · intro j
      have same : j = 0 := Fin.eq_zero j
      subst j
      rfl
    · intro i
      exact Fin.elim0 i
  | succ n ih =>
    let Q : PolygonalChain ℂ n := ⟨fun j => P.vertex j.castSucc⟩
    have qdirections : ∀ i, 0 ≤ (Q.edge i).re ∧ 0 ≤ (Q.edge i).im :=
      fun i => directions i.castSucc
    have qgenuine : ∀ i, 0 < (Q.edge i).re + (Q.edge i).im :=
      fun i => genuine i.castSucc
    obtain ⟨G, vertices, points⟩ := ih Q qdirections qgenuine
    let a := Q.vertex (Fin.last n)
    let b := P.vertex (Fin.last (n + 1))
    have last_real : 0 ≤ b.re - a.re := (directions (Fin.last n)).1
    have last_imaginary : 0 ≤ b.im - a.im := (directions (Fin.last n)).2
    have last_genuine : 0 < (b.re - a.re) + (b.im - a.im) := genuine (Fin.last n)
    have ascending : 0 < b.re + b.im - (a.re + a.im) := by linarith
    let H := MonotoneHeightGraph.through a b (sub_nonneg.mp last_real)
      (sub_nonneg.mp last_imaginary) ascending
    have first_point := MonotoneHeightGraph.through_lineMap a b (sub_nonneg.mp last_real)
      (sub_nonneg.mp last_imaginary) ascending 0
    have last_point := MonotoneHeightGraph.through_lineMap a b (sub_nonneg.mp last_real)
      (sub_nonneg.mp last_imaginary) ascending 1
    simp only [AffineMap.lineMap_apply_zero] at first_point
    simp only [AffineMap.lineMap_apply_one] at last_point
    have first_coordinate : H.coordinate (a.re + a.im) = a.re :=
      congrArg Complex.re first_point
    have last_coordinate : H.coordinate (b.re + b.im) = b.re :=
      congrArg Complex.re last_point
    have joined : G.coordinate (a.re + a.im) = H.coordinate (a.re + a.im) :=
      (vertices (Fin.last n)).trans first_coordinate.symm
    have qmonotone := Q.height_vertices_mono qdirections
    let height : ℂ →ₗ[ℝ] ℝ := Complex.reCLM.toLinearMap + Complex.imCLM.toLinearMap
    refine ⟨G.splice H (a.re + a.im) joined, ?_, ?_⟩
    · intro j
      refine Fin.lastCases ?_ (fun k => ?_) j
      · rw [G.splice_coordinate_right H _ joined (by linarith)]
        exact last_coordinate
      · change (G.splice H (a.re + a.im) joined).coordinate
          ((Q.vertex k).re + (Q.vertex k).im) = (Q.vertex k).re
        rw [G.splice_coordinate_left H _ joined (qmonotone (Fin.le_last k))]
        exact vertices k
    · intro i t
      refine Fin.lastCases ?_ (fun k => ?_) i
      · have lower : a.re + a.im ≤ (P.point (Fin.last n) t).re +
            (P.point (Fin.last n) t).im := by
          have formula := P.linear_point height (Fin.last n) t
          change height a ≤ height (P.point (Fin.last n) t)
          change height (P.point (Fin.last n) t) =
            (1 - (t : ℝ)) * height a + (t : ℝ) * height b at formula
          have ordered : height a ≤ height b := by change a.re + a.im ≤ b.re + b.im; linarith
          nlinarith [t.property.1]
        rw [G.splice_coordinate_right H _ joined lower]
        exact congrArg Complex.re (MonotoneHeightGraph.through_lineMap a b
          (sub_nonneg.mp last_real) (sub_nonneg.mp last_imaginary) ascending t)
      · change (G.splice H (a.re + a.im) joined).coordinate
          ((Q.point k t).re + (Q.point k t).im) = (Q.point k t).re
        have upper : (Q.point k t).re + (Q.point k t).im ≤ a.re + a.im := by
          change height (Q.point k t) ≤ height a
          rw [Q.linear_point height k t]
          have first : height (Q.vertex k.castSucc) ≤ height a := qmonotone (Fin.le_last _)
          have last : height (Q.vertex k.succ) ≤ height a := qmonotone (Fin.le_last _)
          nlinarith [t.property.1, t.property.2]
        rw [G.splice_coordinate_left H _ joined upper]
        exact points k t

end Unfoldings.PolygonalChain
