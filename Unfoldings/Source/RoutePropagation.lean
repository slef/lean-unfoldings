module

public import Unfoldings.Source.FiberWordMotion
public import Unfoldings.Source.FaceRouteMotion
public import Unfoldings.Combinatorics.FiniteReach

/-!
# Bounded propagation of actual source motions along retained face routes

An actual face piece preserves its motion. A junction changes the motion by
one of finitely many constructed bounded seam words. Induction through the
whole route, including its initial and final face-copy choices, bounds the
actual endpoint motion by the route length plus one finite-choice steps.
-/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialFolding.ConvexBoundary

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {F : SpatialFolding C} (P : F.ConvexBoundary)

theorem sourceMotion_reachable_along_faceRoute :
    letI := P.metricSpace
    ∀ {source : C.Realization Set.univ} (R : SourceFrame source)
      {start finish : C.Realization Set.univ} (p : Path start finish) (route : C.FaceRoute p),
      (∀ t, p t ∉ sourceCutLocus source) →
      ∀ a : C.PointFiber Set.univ start, ∀ b : C.PointFiber Set.univ finish,
        ∀ start_off : start ∉ sourceCutLocus source, ∀ finish_off : finish ∉ sourceCutLocus source,
          P.sourceFiberMotion R finish finish_off b ∈
            finiteReach (C.boundedWordPlacement (N := Fintype.card Face))
              (P.sourceFiberMotion R start start_off a) (route.steps + 1) := by
  let := P.metricSpace
  intro source R start finish p route outside a b start_off finish_off
  let step := C.boundedWordPlacement (N := Fintype.card Face)
  let initial := P.sourceFiberMotion R start start_off a
  have positive_steps : 0 < route.steps := by
    by_contra wrong
    have zero : route.steps = 0 := Nat.eq_zero_of_not_pos wrong
    have last_zero : Fin.last route.steps = 0 := Fin.ext zero
    have ends := route.finish
    rw [last_zero, route.start] at ends
    exact zero_ne_one ends
  have entry_off (i : Fin route.steps) :
      C.faceMap Set.univ (route.face i) (route.entry i) ∉ sourceCutLocus source := by
    rw [route.entry_image]
    exact outside _
  have exit_off (i : Fin route.steps) :
      C.faceMap Set.univ (route.face i) (route.exit i) ∉ sourceCutLocus source := by
    rw [route.exit_image]
    exact outside _
  let entry_motion (i : Fin route.steps) :=
    P.sourceTaggedMotion R ⟨route.face i, route.entry i⟩ (entry_off i)
  let exit_motion (i : Fin route.steps) :=
    P.sourceTaggedMotion R ⟨route.face i, route.exit i⟩ (exit_off i)
  have same_piece (i : Fin route.steps) : entry_motion i = exit_motion i :=
    P.sourceFaceRoute_piece_motion R route outside i (entry_off i) (exit_off i)
  let first : Fin route.steps := ⟨0, positive_steps⟩
  have first_image : C.faceMap Set.univ (route.face first) (route.entry first) = start := by
    rw [route.entry_image]
    change p (route.time 0) = start
    rw [route.start, Path.source]
  let first_copy : C.PointFiber Set.univ start :=
    ⟨⟨route.face first, route.entry first⟩, first_image⟩
  have first_step := P.sourceFiberMotion_mem_candidates R start start_off a first_copy
  change entry_motion first ∈ Set.range (step initial) at first_step
  obtain ⟨first_word, first_word_eq⟩ := first_step
  have first_member := finiteReach_step step initial
    (initial_mem_finiteReach step initial 0) first_word
  rw [first_word_eq] at first_member
  have reached : ∀ (k : ℕ) (hk : k < route.steps),
      exit_motion ⟨k, hk⟩ ∈ finiteReach step initial (k + 1) := by
    intro k
    induction k with
    | zero =>
      intro hk
      rw [← same_piece ⟨0, hk⟩]
      exact first_member
    | succ k ih =>
      intro hk
      let i : Fin route.steps := ⟨k, Nat.lt_of_succ_lt hk⟩
      let j : Fin route.steps := ⟨k + 1, hk⟩
      have previous := ih i.isLt
      have crossing := P.sourceFiberMotion_mem_candidates R (p (route.time i.succ))
        (outside _) (route.junctionLeft i) (route.junctionRight i j rfl)
      change entry_motion j ∈ Set.range (step (exit_motion i)) at crossing
      obtain ⟨word, word_eq⟩ := crossing
      have next := finiteReach_step step initial previous word
      rw [word_eq] at next
      rw [← same_piece j]
      exact next
  let last : Fin route.steps := ⟨route.steps - 1, by omega⟩
  have last_time : last.succ = Fin.last route.steps := Fin.ext (by dsimp [last]; omega)
  have last_image : C.faceMap Set.univ (route.face last) (route.exit last) = finish := by
    rw [route.exit_image, last_time, route.finish, Path.target]
  let last_copy : C.PointFiber Set.univ finish := ⟨⟨route.face last, route.exit last⟩, last_image⟩
  have last_member := reached last.val last.isLt
  have last_budget : last.val + 1 = route.steps := by dsimp [last]; omega
  rw [last_budget] at last_member
  have last_step := P.sourceFiberMotion_mem_candidates R finish finish_off last_copy b
  change P.sourceFiberMotion R finish finish_off b ∈
    Set.range (step (exit_motion last)) at last_step
  obtain ⟨word, word_eq⟩ := last_step
  have result := finiteReach_step step initial last_member word
  rw [word_eq] at result
  exact result

end Unfoldings.SpatialFolding.ConvexBoundary
