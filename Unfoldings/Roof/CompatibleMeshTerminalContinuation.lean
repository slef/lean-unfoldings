module

public import Unfoldings.Roof.CompatibleMeshTerminalRoot
public import Unfoldings.Roof.CompatibleTerminalHistory
public import Unfoldings.Roof.CompatibleSubhistoryMargins

/-! Continue actual original fine histories arbitrarily far along their derived terminal rays. -/

@[expose] public section

noncomputable section

open scoped NNReal ENNReal

namespace Unfoldings.ConvexRoof

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexRoof C)
  {slopes : Set Plane} (compact : IsCompact slopes) (nonempty : slopes.Nonempty)
  {boundary : (frontier slopes).Nonempty} {a β : ℝ}
  (R : K.CompatiblePotentialRouting {f | K.normalSlope f ∈ slopes}
    (K.clippedExtension slopes compact nonempty) boundary a β)
  (no_boundary : ∀ f, K.normalSlope f ∉ frontier slopes)
  (level : ℝ)
  (higher : ∀ v, (K.clippedExtension slopes compact nonempty).height (K.projectedVertex v) < level)
  (M : (K.clippedExtension slopes compact nonempty).FiniteSlopeModel)
  (positive : 0 < a) (inner_disk : Metric.ball (0 : Plane) a ⊆ slopes)
  (beta : 0 ≤ β) (acute : β < Real.pi / 2)

local notation "T" => K.compatibleCutMesh compact nonempty R no_boundary level higher M
  positive inner_disk
local notation "conforming" => K.compatibleCutMesh_conforming compact nonempty R no_boundary
  level higher M positive inner_disk
local notation "inside" => K.compatible_section_interior compact nonempty R level higher M
local notation "Q" => SpatialEnvelope.Triangulation.roof
  (SpatialEnvelope.ConstrainedTriangulation.toTriangulation T) conforming inside
local notation "Fcut" => K.compatibleMeshForest compact nonempty R no_boundary level higher
  M positive inner_disk beta acute

local instance compatibleContinuedHistoryIndexFintype : Fintype (T).Index :=
  @Fintype.ofFinite _ (T).finite

local notation "RootAt[" s "," h "]" =>
  K.compatibleMeshTerminalRoot compact nonempty R no_boundary level higher M
    positive inner_disk beta acute s h
local notation "HistoryAt[" s "," n "]" =>
  K.compatibleMeshHistory compact nonempty R no_boundary level higher M
    positive inner_disk beta acute s n

/-- Append an arbitrary terminal duration to the actual fine history. The named original
ray and exact join point are constructed from that history, rather than supplied. -/
def compatibleMeshContinuedHistory (start : (T).pairedComplex.Vertex Set.univ)
    (n : ℕ) (positive_length : 0 < n) (length : (Fcut).parents.distanceToRoot start = n)
    (time : ℝ) : PolygonalChain Plane (n + 1) :=
  (HistoryAt[start,n]).snoc
    (R.exterior.ray (R.terminalIndex RootAt[start,by omega])
      (R.terminalTime level RootAt[start,by omega] + time))

local notation "ContinuedAt[" s "," n "," h "," hn "," t "]" =>
  K.compatibleMeshContinuedHistory compact nonempty R no_boundary level higher M
    positive inner_disk beta acute s n h hn t

/-- The original fresh source remains the exact first vertex after continuation. -/
theorem compatibleMeshContinuedHistory_vertex_zero
    (start : (T).pairedComplex.Vertex Set.univ) (n : ℕ) (positive_length : 0 < n)
    (length : (Fcut).parents.distanceToRoot start = n) (time : ℝ) :
    (ContinuedAt[start,n,positive_length,length,time]).vertex 0 = (Q).projectedVertex start := by
  change ((HistoryAt[start,n]).snoc _).vertex (0 : Fin (n + 1)).castSucc = _
  rw [PolygonalChain.snoc_vertex_castSucc]
  rfl

/-- The new endpoint retains its exact original unbounded ray coordinate. -/
theorem compatibleMeshContinuedHistory_vertex_last
    (start : (T).pairedComplex.Vertex Set.univ) (n : ℕ) (positive_length : 0 < n)
    (length : (Fcut).parents.distanceToRoot start = n) (time : ℝ) :
    (ContinuedAt[start,n,positive_length,length,time]).vertex (Fin.last (n + 1)) =
      R.exterior.ray (R.terminalIndex RootAt[start,by omega])
        (R.terminalTime level RootAt[start,by omega] + time) :=
  PolygonalChain.snoc_vertex_last _ _

/-- Every appended finite tail still follows the original compatible routing. -/
theorem compatibleMeshContinuedHistory_follows
    (start : (T).pairedComplex.Vertex Set.univ) (n : ℕ) (positive_length : 0 < n)
    (length : (Fcut).parents.distanceToRoot start = n) {time : ℝ} (forward : 0 ≤ time) :
    R.Follows ContinuedAt[start,n,positive_length,length,time] := by
  apply R.follows_snoc_terminal (HistoryAt[start,n])
    (K.compatibleMeshHistory_follows compact nonempty R no_boundary level higher M positive
      inner_disk beta acute start n length.ge) RootAt[start,by omega]
    (R.terminalTime_pos level higher _).le (by linarith)
  exact K.compatibleMeshHistory_last_terminalPoint compact nonempty R no_boundary level higher M
    positive inner_disk beta acute start n positive_length length

/-- The same common-potential length bound controls arbitrarily long actual terminal tails. -/
theorem compatibleMeshContinuedHistory_length_bound
    (start : (T).pairedComplex.Vertex Set.univ) (n : ℕ) (positive_length : 0 < n)
    (length : (Fcut).parents.distanceToRoot start = n) {time : ℝ} (forward : 0 ≤ time)
    {b : ℝ} (upper : ∀ p ∈ slopes, ‖p‖ ≤ b) :
    (ContinuedAt[start,n,positive_length,length,time]).projectedLength ≤
      (b / (a * Real.cos β)) *
        ‖(ContinuedAt[start,n,positive_length,length,time]).vertex (Fin.last (n + 1)) -
          (Q).projectedVertex start‖ := by
  have bound := R.follows_length_bound positive beta acute inner_disk upper
    ContinuedAt[start,n,positive_length,length,time]
    (K.compatibleMeshContinuedHistory_follows compact nonempty R no_boundary level higher M positive
      inner_disk beta acute start n positive_length length forward)
  rwa [K.compatibleMeshContinuedHistory_vertex_zero] at bound

variable {b : ℝ} (bpos : 0 < b) (ratio : a ≤ b) (upper : ∀ p ∈ slopes, ‖p‖ ≤ b)
  (small : 2 * annularHistoryAngle (a / b) β < Real.pi / 2)

include bpos ratio upper small

/-- All original fine banks and the appended tail keep the same positive source margin. -/
theorem compatibleMeshContinuedHistory_source_margin
    (start : (T).pairedComplex.Vertex Set.univ) (n : ℕ) (positive_length : 0 < n)
    (length : (Fcut).parents.distanceToRoot start = n) {time : ℝ} (forward : 0 ≤ time)
    (i : Fin (n + 1)) :
    Real.cos (2 * annularHistoryAngle (a / b) β) *
      (‖(ContinuedAt[start,n,positive_length,length,time]).vertex i.castSucc -
          (Q).projectedVertex start‖ *
        ‖(ContinuedAt[start,n,positive_length,length,time]).edge i‖) ≤
      inner ℝ ((ContinuedAt[start,n,positive_length,length,time]).vertex i.castSucc -
        (Q).projectedVertex start) ((ContinuedAt[start,n,positive_length,length,time]).edge i) := by
  have margin := R.follows_subhistory_radial_margin
    ContinuedAt[start,n,positive_length,length,time]
    (K.compatibleMeshContinuedHistory_follows compact nonempty R no_boundary level higher M positive
      inner_disk beta acute start n positive_length length forward)
    positive beta acute bpos ratio inner_disk upper small 0 i (Nat.zero_le _)
  rwa [K.compatibleMeshContinuedHistory_vertex_zero] at margin

/-- Whole-point radial order from every earlier point persists to every finite terminal time. -/
theorem compatibleMeshContinuedHistory_globallyRadiallyMonotone
    (start : (T).pairedComplex.Vertex Set.univ) (n : ℕ) (positive_length : 0 < n)
    (length : (Fcut).parents.distanceToRoot start = n) {time : ℝ} (forward : 0 ≤ time) :
    (ContinuedAt[start,n,positive_length,length,time]).GloballyRadiallyMonotone :=
  R.follows_globallyRadiallyMonotone ContinuedAt[start,n,positive_length,length,time]
    (K.compatibleMeshContinuedHistory_follows compact nonempty R no_boundary level higher M positive
      inner_disk beta acute start n positive_length length forward)
    positive beta acute bpos ratio inner_disk upper small

end Unfoldings.ConvexRoof
