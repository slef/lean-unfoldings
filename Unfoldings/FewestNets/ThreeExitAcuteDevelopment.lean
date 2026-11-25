module

public import Unfoldings.FewestNets.ThreeExitRoots
public import Unfoldings.Geometry.AcuteHeadingControls
public import Unfoldings.Roof.AcuteBankSubhistories

/-! Physical development estimates for every bank following the actual three-exit cuts. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof.ThreeExitComponentRouting

open FewestNets Real

universe u v w z

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexRoof C} {slopes : Set Plane} {seed : Face}
  {B : PolygonSideDirections (Fin 3) slopes}
  {compact : IsCompact slopes} {nonempty : slopes.Nonempty} {H : ThreeExitStemWindows}
  (R : K.ThreeExitComponentRouting seed B compact nonempty H)

local notation "U" => K.selectionComponent slopes seed
local notation "V" => {v : C.Vertex Set.univ // K.projectedVertex v ∈ K.restrictedCarrier U}
local notation "G" => SlopeEnvelope.recenter
  (K.componentClippedExtension
    (Set.nonempty_of_mem (K.seed_mem_selectionComponent slopes seed)) compact nonempty) B.reference
local notation "Root" => {r // r ∈ R.stems.choice.parents.roots}

set_option maxHeartbeats 700000 in
/-- All intervals of an actual bank following the oriented cuts have the
acute-cone intrinsic length and radial bounds. -/
theorem sharp_threeExit_bank_subhistories (level : ℝ)
    (higher : ∀ v : V, (G).height (K.projectedVertex v.val) < level)
    {Fine : Type w} [Fintype Fine] {D : TriangleComplex.{w, z} Fine} (Q : ConvexRoof D)
    {retain : Set D.Seam} {n : ℕ} (bank : (D.boundarySystem retain).Chain n)
    (cut : ∀ i, ¬ D.IsBoundaryEdge Set.univ (D.germEdge (bank.point i).val))
    (aligned : ∀ i : Fin (n + 1), let P := Q.folding.projectedBoundaryChain bank
      Nonempty ((R.truncatedEmbedding level higher).OrientedSubsegment
        (P.vertex i.castSucc) (P.vertex i.succ)))
    {width gamma phi : ℝ} (acute : width < π / 2) (gamma_pos : 0 < gamma)
    (γ_margin : gamma ≤ cos width)
    (span : ∀ r : Root,
      let exit := ((R.rootHeadingChart r) (R.rootExitDirection r)).arg
      let lo := R.rootWindowStart r
      max (lo + H.width) exit - min lo exit ≤ width)
    (tilt_pos : 0 < phi) (small_phi : phi < π / 2) (height_bound : (3 : ℝ) / 4 ≤ cos phi)
    (tilt : Q.TiltBound phi) (small : acuteConeDevelopmentError phi (√2) < gamma) :
    let error := acuteConeDevelopmentError phi (√2)
    let D' := (cos phi)⁻¹ * √2 / (1 - error)
    let d := (gamma - error) / (1 + error)
    let P := D.boundaryChainRoll bank
    (∀ (first length : ℕ) (fits : first + length ≤ n + 1),
      let interval := P.interval first length fits
      interval.projectedLength ≤ D' * ‖interval.vertex (Fin.last length) - interval.vertex 0‖) ∧
    ∀ (j : Fin (n + 2)) (i : Fin (n + 1)), j.val ≤ i.val →
      d * (‖P.vertex i.castSucc - P.vertex j‖ * ‖P.edge i‖) ≤
        inner ℝ (P.vertex i.castSucc - P.vertex j) (P.edge i) := by
  let P := Q.folding.projectedBoundaryChain bank
  obtain ⟨r, headings⟩ :=
    R.exists_root_window_for_fine_history level higher (Nat.succ_pos n) P aligned
  let frame := R.rootHeadingChart r
  let direction := frame (R.rootExitDirection r)
  let point := R.rootWindowStart r
  let lo := min point direction.arg
  let hi := max (point + H.width) direction.arg
  let S := P.inComplexFrame frame
  have width_bound : hi - lo ≤ width := span r
  have acute_span := width_bound.trans_lt acute
  have genuine (i) : P.edge i ≠ 0 := Q.projectedBoundaryChain_edge_ne_zero bank i
  have in_interval (i : Fin (n + 1)) : (frame (P.edge i)).arg ∈ Set.Icc lo hi := by
    rcases headings i with stem | exit
    · exact ⟨(min_le_left _ _).trans stem.1, stem.2.trans (le_max_left _ _)⟩
    · rw [exit]
      exact ⟨min_le_right _ _, le_max_right _ _⟩
  have progress (i) := headingControls_pos frame (genuine i) acute_span (in_interval i)
  obtain ⟨axis, unit, _, direction_bound⟩ :=
    exists_threeExit_history_axis S.edge direction
      (fun same => R.rootExitDirection_ne_zero r (frame.map_eq_zero_iff.mp same))
      width_bound (fun i _ => by simpa only [S, P.inComplexFrame_edge] using headings i)
  have width_nonneg : 0 ≤ width := by
    have ordered : lo ≤ hi := (min_le_right _ _).trans (le_max_right _ _)
    linarith only [ordered, width_bound]
  apply Q.sharp_acute_physical_bank_subhistories tilt_pos small_phi height_bound tilt gamma_pos
    (γ_margin.trans (cos_le_one _)) (sqrt_nonneg _) bank cut
    (headingControl frame ((lo + hi) / 2 + π / 4))
    (headingControl frame ((lo + hi) / 2 - π / 4))
    (headingControls_bijective frame _) ⟨fun i => (progress i).1, fun i => (progress i).2⟩ _ _ small
  · dsimp only
    intro j i before
    have radial := (R.fine_history_bounds level higher (Nat.succ_pos n) P aligned
      acute.le span j i before).2
    exact (mul_le_mul_of_nonneg_right γ_margin
      (mul_nonneg (norm_nonneg _) (norm_nonneg _))).trans radial
  · dsimp only
    intro first length fits
    have radius : width / 2 ≤ π / 4 := by linarith only [acute]
    have comparison := (S.interval first length fits).cone_length_bound_sqrt_two unit
      (by positivity : 0 ≤ width / 2) radius
      (fun i => direction_bound ⟨first + i.val, by omega⟩)
    simpa only [S, PolygonalChain.inComplexFrame_interval_projectedLength,
      PolygonalChain.interval_last, PolygonalChain.interval_start,
      PolygonalChain.inComplexFrame_norm_sub] using comparison

end Unfoldings.ConvexRoof.ThreeExitComponentRouting
