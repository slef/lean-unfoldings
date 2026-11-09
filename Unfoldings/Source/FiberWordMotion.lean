module

public import Unfoldings.Source.TaggedMotion

/-!
# Bounded actual seam words propagate the source motions of all point copies

Every seam step uses the proved actual outward transition. Finite word
composition therefore identifies the endpoint motion, not just one matching
point. This includes chains through flat subdivision vertices.
-/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialFolding.ConvexBoundary

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {F : SpatialFolding C} (P : F.ConvexBoundary)

def sourceFiberMotion :
    letI := P.metricSpace
    {source : C.Realization Set.univ} → (R : SourceFrame source) →
      (x : C.Realization Set.univ) → (outside : x ∉ sourceCutLocus source) →
        C.PointFiber Set.univ x → (Plane ≃ᵃⁱ[ℝ] Plane) := by
  let := P.metricSpace
  intro source R x outside a
  exact P.sourceTaggedMotion R a.val (a.property.symm ▸ outside)

theorem sourceFiberMotion_word :
    letI := P.metricSpace
    ∀ {source : C.Realization Set.univ} (R : SourceFrame source)
      (x : C.Realization Set.univ) (outside : x ∉ sourceCutLocus source)
      {a b : C.PointFiber Set.univ x} (W : C.PointSeamRoute Set.univ x a b),
      P.sourceFiberMotion R x outside b = C.wordPlacement
        (List.ofFn (fun i => (W.seam i, W.side i))) (P.sourceFiberMotion R x outside a) := by
  let := P.metricSpace
  intro source R x outside a b W
  let motion (i : Fin (W.steps + 1)) := P.sourceFiberMotion R x outside (W.copy i)
  have joined (i : Fin W.steps) : motion i.succ =
      (C.seamTransition (W.seam i) (W.side i)).trans (motion i.castSucc) := by
    obtain ⟨q, first, last⟩ := W.crossing i
    have outside_first : MetricGluing.point C.Cell (C.glue Set.univ)
        (C.edgePoint (C.seamSide (W.seam i) (W.side i)) q) ∉ sourceCutLocus source := by
      rw [← first, (W.copy i.castSucc).property]
      exact outside
    have outside_last : MetricGluing.point C.Cell (C.glue Set.univ)
        (C.edgePoint (C.seamSide (W.seam i) (!(W.side i)))
          (C.across (W.seam i) (W.side i) q)) ∉ sourceCutLocus source := by
      rw [← last, (W.copy i.succ).property]
      exact outside
    have actual := P.sourceTaggedMotion_seam R (W.seam i) (W.side i) q outside_first outside_last
    have first_motion := P.sourceTaggedMotion_congr R first
      ((W.copy i.castSucc).property.symm ▸ outside) outside_first
    have last_motion := P.sourceTaggedMotion_congr R last
      ((W.copy i.succ).property.symm ▸ outside) outside_last
    change P.sourceTaggedMotion R (W.copy i.succ).val _ =
      (C.seamTransition (W.seam i) (W.side i)).trans
        (P.sourceTaggedMotion R (W.copy i.castSucc).val _)
    rw [first_motion, last_motion]
    exact actual
  have result := C.wordPlacement_on_motions (fun i => (W.seam i, W.side i)) motion joined
  change P.sourceFiberMotion R x outside (W.copy (Fin.last W.steps)) =
    C.wordPlacement (List.ofFn (fun i => (W.seam i, W.side i)))
      (P.sourceFiberMotion R x outside (W.copy 0)) at result
  rw [W.start, W.finish] at result
  exact result

theorem sourceFiberMotion_mem_candidates :
    letI := P.metricSpace
    ∀ {source : C.Realization Set.univ} (R : SourceFrame source)
      (x : C.Realization Set.univ) (outside : x ∉ sourceCutLocus source)
      (a b : C.PointFiber Set.univ x),
      P.sourceFiberMotion R x outside b ∈ Set.range
        (C.boundedWordPlacement (N := Fintype.card Face) (P.sourceFiberMotion R x outside a)) := by
  let := P.metricSpace
  intro source R x outside a b
  obtain ⟨W, short⟩ := F.exists_short_pointSeamRoute Set.univ x a b
  exact ⟨W.code C short, (P.sourceFiberMotion_word R x outside W).symm⟩

end Unfoldings.SpatialFolding.ConvexBoundary
